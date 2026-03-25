import json
import os
import platform
import signal
import subprocess
import tempfile
import threading
import time
import psutil
import resource
import hashlib
from typing import Optional, Dict, Tuple
from pathlib import Path

from loguru import logger

from lean_verifier.utils import get_error_msg
from lean_verifier.config import settings
from lean_verifier.exceptions import (
    FunctionTimedOut,
    LeanCrashError,
    LeanEOFError,
    LeanBrokenPipeError,
)

# Constants
PROCESS_RESTART_DELAY = 0.5  # seconds to wait after killing process before restart
SIGTERM_WAIT_TIME = 0.3      # seconds to wait for SIGTERM before SIGKILL
MEMORY_WARNING_THRESHOLD = 0.95  # warn when memory usage exceeds 80% of limit


# Get absolute path of project root directory
def get_project_root():
    """Get absolute path of project root directory"""
    current_file = Path(__file__)
    project_root = current_file.parent.parent
    return project_root

project_root = get_project_root()
path_to_repl = str(project_root / "repl/.lake/build/bin/repl")
path_to_mathlib = str(project_root / "mathlib4")
path_to_tacs = str(project_root / "lean-tacs")


class LeanREPL:
    """
    Enhanced LeanREPL with environment caching support.
    
    Key features:
    - Separate header (imports) from body (proofs)
    - Cache loaded environments by header hash
    - Reuse environments across multiple verifications
    """
    
    def __init__(self, enable_cache: bool = True, max_cached_envs: int = 5, max_env_reuse_count: int = 100):
        """
        Args:
            enable_cache: Whether to enable environment caching
            max_cached_envs: Maximum number of cached environments (memory limit)
            max_env_reuse_count: Maximum reuse count per environment (prevents memory leaks)
        """
        self.enable_cache = enable_cache
        self.max_cached_envs = max_cached_envs
        self.max_env_reuse_count = max_env_reuse_count
        
        # Cache: header_hash -> (env_id, header_code)
        self.env_cache: Dict[str, Tuple[int, str]] = {}
        self.env_use_counts: Dict[str, int] = {}
        
        # Start the REPL process
        self.error_file = tempfile.TemporaryFile("w+")
        self.start_process()
        
        self.header = None
        self.run_command_total = 0
        
        # Stats
        self.cache_hits = 0
        self.cache_misses = 0
        self.cache_refreshes = 0  # Count environments refreshed due to reuse limit

    def _split_code(self, code: str) -> Tuple[str, str, str]:
        """
        Split code into header (imports/opens) and body.
        
        Returns:
            (header_hash, header_code, body_code)
        """
        lines = code.strip().split('\n')
        header_lines = []
        body_start = 0
        
        for i, line in enumerate(lines):
            stripped = line.strip()
            # Identify import/open statements
            if stripped.startswith('import ') or stripped.startswith('open '):
                header_lines.append(line)
            elif stripped and not stripped.startswith('--'):
                # First non-empty, non-comment, non-import line
                body_start = i
                break
        
        header_code = '\n'.join(header_lines)
        body_code = '\n'.join(lines[body_start:])
        
        # Generate hash for header
        header_hash = hashlib.md5(header_code.encode()).hexdigest() if header_code else "empty"
        
        return header_hash, header_code, body_code

    def _get_or_create_env(self, header_hash: str, header_code: str, timeout: int = 60, max_retries: int = 2) -> Optional[int]:
        """
        Get cached environment ID or create new one, with retry for system errors.
        
        Args:
            header_hash: Hash of the header code
            header_code: Header code to create environment from
            timeout: Timeout for create_env
            max_retries: Maximum number of retries for system errors
            
        Returns:
            env_id if successful, None if no header or creation failed
        """
        if not header_code.strip():
            # No header, no environment needed
            return None
        
        # Check cache
        if header_hash in self.env_cache:
            # Check process health before reusing cached environment
            health = self._get_process_health()
            should_reset, health_reason = self._check_memory_health(health)
            
            # Check if environment has been reused too many times
            reuse_exceeded = self.env_use_counts[header_hash] >= self.max_env_reuse_count
            
            if should_reset or reuse_exceeded:
                # Force refresh: remove from cache and recreate
                old_env_id, _ = self.env_cache.pop(header_hash)
                del self.env_use_counts[header_hash]
                self.cache_refreshes += 1
                
                if should_reset:
                    logger.info(
                        f"🔄 Cache REFRESH for header {header_hash[:8]} "
                        f"(env_id={old_env_id}, health check failed: {health_reason})"
                    )
                    # Reset process due to health issue
                    self._reset_process()
                else:
                    logger.info(
                        f"🔄 Cache REFRESH for header {header_hash[:8]} "
                        f"(env_id={old_env_id} exceeded {self.max_env_reuse_count} reuses)"
                    )
                # Fall through to create new environment
            else:
                # Reuse cached environment
                env_id, _ = self.env_cache[header_hash]
                self.env_use_counts[header_hash] += 1
                self.cache_hits += 1
                logger.debug(
                    f"🎯 Cache HIT for header {header_hash[:8]} "
                    f"(env_id={env_id}, uses={self.env_use_counts[header_hash]}/{self.max_env_reuse_count})"
                )
                # Log normal health status (DEBUG level)
                self._log_process_health(health, "Cache reuse: ")
                return env_id
        
        # Cache miss - create new environment with retry
        self.cache_misses += 1
        logger.info(f"❔ Cache MISS for header {header_hash[:8]}, creating new env...")
        
        # Evict oldest env if cache is full (LRU-like)
        if len(self.env_cache) >= self.max_cached_envs:
            # Find least used environment
            oldest_hash = min(self.env_use_counts.items(), key=lambda x: x[1])[0]
            old_env_id, _ = self.env_cache.pop(oldest_hash)
            del self.env_use_counts[oldest_hash]
            logger.info(f"🗑️  Evicted env {old_env_id} (header {oldest_hash[:8]})")
        
        # Create new environment with retry for system errors
        last_error = None
        for attempt in range(max_retries + 1):
            try:
                response = self.create_env(header_code, timeout=timeout)
                error_msg = get_error_msg(response)
                
                if error_msg:
                    # System error or code error
                    last_error = error_msg
                    logger.warning(f"⚠️  Attempt {attempt + 1}/{max_retries + 1} failed to create env: {error_msg}")
                    
                    # If it's a system error (contains keywords), retry
                    is_system_error = any(keyword in error_msg.lower() for keyword in [
                        'unknown environment', 'initialization failed', 'process', 'timeout'
                    ])
                    
                    if is_system_error and attempt < max_retries:
                        logger.info(f"🔄 Retrying env creation (attempt {attempt + 2}/{max_retries + 1})...")
                        time.sleep(0.5)  # Brief pause before retry
                        continue
                    else:
                        # Code error or max retries reached
                        logger.error(f"❌ Failed to create env for header {header_hash[:8]}: {error_msg}")
                        return None
                
                # Success - extract env_id
                env_id = response.get('env', 0)
                
                # Cache the environment
                self.env_cache[header_hash] = (env_id, header_code)
                self.env_use_counts[header_hash] = 1
                logger.info(f"✅ Created and cached env_id={env_id} for header {header_hash[:8]}")
                
                return env_id
                
            except FunctionTimedOut:
                # Timeout - retry if not max attempts
                logger.warning(f"⏱️  Attempt {attempt + 1}/{max_retries + 1} timed out creating env")
                if attempt < max_retries:
                    logger.info(f"🔄 Retrying after timeout (attempt {attempt + 2}/{max_retries + 1})...")
                    continue
                else:
                    logger.error(f"❌ Failed to create env after {max_retries + 1} timeout attempts")
                    raise
                    
            except Exception as e:
                # Other exceptions: log and return None
                logger.error(f"❌ Exception creating env: {e}")
                return None
        
        # If we get here, all retries failed
        logger.error(f"❌ Failed to create env for header {header_hash[:8]} after {max_retries + 1} attempts")
        return None

    def one_pass_verify(self, code: str, timeout: int, infotree_type=None, max_retries: int = 2):
        """
        Verify code with header/body splitting and environment caching.
        
        Strategy:
        1. Cache the header (imports) environment once (with retry for system errors)
        2. Each verification creates a NEW temporary child environment from the cached base
        3. Use gc=True to automatically clean up temporary environments
        4. NO retry for verify phase - only retry at create_env phase
        
        This prevents 'already declared' errors by ensuring each verification
        gets a fresh child environment, not a reused one.
        """
        if not self.enable_cache:
            # Disabled: verify entire code at once (no caching, no retry)
            return self._verify_full_code(code, timeout, infotree_type, max_retries=0)
        
        # Split code into header and body
        header_hash, header_code, body_code = self._split_code(code)
        
        logger.debug(f"📝 Code split - Header: {len(header_code)} chars, Body: {len(body_code)} chars")
        
        # Get or create cached environment for header (with retry built-in)
        base_env_id = self._get_or_create_env(header_hash, header_code, timeout=timeout, max_retries=max_retries)
        
        # Verify body using the cached base environment (NO retry)
        start_time = time.time()
        
        if base_env_id is not None:
            # Extend from cached base environment with gc=True
            # This creates a NEW child environment each time
            response = self._verify_with_env(base_env_id, body_code, timeout, infotree_type)
        else:
            # No header or create_env failed: verify full code as fallback
            logger.info("⚠️  No cached env available, using full code verification")
            response = self._verify_full_code(code, timeout, infotree_type, max_retries=0)
        
        elapsed = time.time() - start_time
        logger.debug(f"✅ Verification completed in {elapsed:.2f}s")
        return response

    def _verify_full_code(self, code: str, timeout: int, infotree_type=None, max_retries: int = 2):
        """Original one-pass verification without caching."""
        if infotree_type is None:
            command = {"cmd": code, "gc": True}
        else:
            command = {"cmd": code, "infotree": infotree_type, "gc": True}
        
        last_exception = None
        for attempt in range(max_retries + 1):
            try:
                start_time = time.time()
                logger.info(f"🚀 Full code verification attempt {attempt + 1}/{max_retries + 1}")
                response = self._send_command_with_timeout(command, timeout)
                elapsed = time.time() - start_time
                logger.info(f"✅ Verification completed in {elapsed:.2f}s")
                return response
                
            except FunctionTimedOut:
                # Timeout: retry after restarting
                logger.warning(f"⏱️  Timeout after {timeout}s - attempt {attempt + 1}")
                last_exception = FunctionTimedOut()
                
                if attempt < max_retries:
                    logger.info(f"🔄 Restarting for retry {attempt + 2}/{max_retries + 1}")
                    try:
                        self.close()
                        time.sleep(PROCESS_RESTART_DELAY)
                        self.start_process()
                    except Exception as e:
                        logger.error(f"❌ Failed to restart: {e}")
                        break
            
            except Exception as e:
                # Non-timeout errors: don't retry, fail immediately
                logger.error(f"❌ Error in attempt {attempt + 1} ({type(e).__name__}): {e}")
                last_exception = e
                break  # Don't retry for non-timeout errors
        
        raise LeanCrashError(f"Failed after {max_retries + 1} attempts: {str(last_exception)}")

    def _verify_with_env(self, env_id: int, body_code: str, timeout: int, infotree_type=None):
        """Verify body code using a pre-loaded environment."""
        return self.extend_env(env_id, body_code, timeout=timeout, infotree_type=infotree_type)

    def _get_process_health(self) -> Dict:
        """Get process health status and resource usage."""
        try:
            if self.process is None:
                return {"status": "not_started", "pid": None}
            
            returncode = self.process.poll()
            if returncode is not None:
                return {"status": "dead", "pid": self.process.pid, "exit_code": returncode}
            
            # Get resource usage
            try:
                proc = psutil.Process(self.process.pid)
                memory_info = proc.memory_info()
                memory_mb = memory_info.rss / (1024 * 1024)
                cpu_percent = proc.cpu_percent(interval=0.1)
                
                # Include child process memory
                children = proc.children(recursive=True)
                total_memory_mb = memory_mb + sum(
                    child.memory_info().rss / (1024 * 1024)
                    for child in children
                    if not self._is_process_gone(child)
                )
                
                return {
                    "status": "alive",
                    "pid": self.process.pid,
                    "memory_mb": round(memory_mb, 2),
                    "total_memory_mb": round(total_memory_mb, 2),
                    "cpu_percent": round(cpu_percent, 2),
                    "num_children": len(children),
                }
            except (psutil.NoSuchProcess, psutil.AccessDenied) as e:
                return {"status": "inaccessible", "pid": self.process.pid, "error": str(e)}
        except Exception as e:
            return {"status": "error", "error": str(e)}
    
    @staticmethod
    def _is_process_gone(proc) -> bool:
        """Check whether the process has exited."""
        try:
            proc.memory_info()
            return False
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            return True
    
    def _check_memory_health(self, health: Dict) -> Tuple[bool, str]:
        """
        Check whether memory usage is healthy.

        Returns:
            (should_reset, reason)
        """
        if health["status"] != "alive":
            return True, f"Process not alive: {health}"
        
        memory_mb = health.get("total_memory_mb", 0)
        memory_limit_mb = settings.REPL_MEMORY_LIMIT_GB * 1024
        memory_ratio = memory_mb / memory_limit_mb if memory_limit_mb > 0 else 0
        
        if memory_ratio > MEMORY_WARNING_THRESHOLD:
            return True, f"High memory: {memory_mb:.1f}MB/{memory_limit_mb:.0f}MB ({memory_ratio*100:.1f}%)"
        
        return False, ""
    
    def _log_process_health(self, health: Dict, context: str = ""):
        """Log process health status."""
        if health["status"] == "alive":
            memory_mb = health.get("total_memory_mb", 0)
            memory_limit_mb = settings.REPL_MEMORY_LIMIT_GB * 1024
            memory_ratio = memory_mb / memory_limit_mb if memory_limit_mb > 0 else 0
            
            log_msg = (
                f"📊 {context}Process health: Memory {memory_mb:.1f}MB ({memory_ratio*100:.1f}%), "
                f"CPU {health.get('cpu_percent', 0):.1f}%, PID {health.get('pid')}"
            )
            
            if memory_ratio > MEMORY_WARNING_THRESHOLD:
                logger.warning(f"⚠️  {log_msg}, Children: {health.get('num_children', 0)}")
            else:
                logger.debug(log_msg)
        else:
            logger.error(f"❌ {context}Process health: {health}")

    def _send_command(self, command):
        """
        Send a JSON command to the REPL and return the JSON response.

        Single responsibility: I/O only; no health checks here.
        Process failures surface as BrokenPipeError/IOError for callers to handle.
        """
        self.run_command_total += 1
        json_command = json.dumps(command, ensure_ascii=False) + "\n\n"
        
        time_elapsed = time.time()
        self.process.stdin.write(json_command)
        self.process.stdin.flush()

        logger.debug(f"📥 Reading response from REPL...")
        response_lines = []
        
        try:
            # Phase 1: Skip any garbage/residual output until we find JSON start
            json_started = False
            skipped_lines_count = 0
            while not json_started:
                line = self.process.stdout.readline()
                
                if not line:  # EOF
                    # Read stderr for crash details
                    stderr_content = self.get_error_content()
                    exit_code = self.process.poll()
                    
                    error_details = []
                    error_details.append(f"exit_code={exit_code}")
                    if stderr_content.strip():
                        error_details.append(f"stderr={stderr_content[:500]}")
                    
                    error_info = ", ".join(error_details)
                    logger.error(f"❌ EOF before finding JSON start ({error_info})")
                    raise LeanEOFError(f"EOF before finding JSON response ({error_info})")
                
                stripped = line.strip()
                if not stripped:  # Empty line, keep looking
                    continue
                
                # Check if this line starts with '{'
                if stripped.startswith('{'):
                    json_started = True
                    response_lines.append(line)
                    if skipped_lines_count > 0:
                        logger.debug(f"📄 Found JSON start, skipped {skipped_lines_count} non-JSON lines")
                else:
                    # Non-JSON line (residual output), skip it
                    skipped_lines_count += 1
                    logger.debug(f"⏭️  Skipping non-JSON line: {line[:100]}")
            
            # Phase 2: Read the rest of the JSON until blank line or EOF
            while True:
                line = self.process.stdout.readline()
                
                # Stop on EOF or blank line
                if not line or not line.strip():
                    logger.debug(f"📄 Empty line or EOF detected, stopping read")
                    break
                
                response_lines.append(line)
        except BrokenPipeError as e:
            logger.error(f"❌ Broken pipe error: {e}")
            raise LeanBrokenPipeError("Lean process broken pipe error")

        response_str = "".join(response_lines).strip()
        time_elapsed = time.time() - time_elapsed
        
        # Parse JSON response
        try:
            response_json = json.loads(response_str)
        except json.JSONDecodeError as e:
            logger.error(f"❌ JSON decode error: {e}")
            logger.error(f"📊 Response length: {len(response_str)} chars")
            logger.error(f"📄 Response (first 1000 chars): {response_str[:1000]}")
            # Phase 1 already ensured we start with '{', so this is a malformed JSON
            raise LeanCrashError(f"Malformed JSON response: {str(e)}")

        # Read and clear stderr (always clear to prevent accumulation)
        error_content = self.get_error_content()
        self.error_file.seek(0)
        self.error_file.truncate(0)
        
        if len(error_content.strip()) > 0:
            logger.error(f"❌ Error from stderr: {error_content}")
            raise LeanCrashError(f"Lean process error: {error_content}")
        
        response_json["time"] = time_elapsed
        return response_json
    
    def _send_command_with_timeout(self, command, timeout: int):
        """Send command with real timeout by killing process if it exceeds time limit.
        
        This uses threading.Timer to force-kill the Lean process if it doesn't respond
        within the timeout period. This is more reliable than func_timeout which cannot
        interrupt blocking I/O operations like readline().
        """
        result = {"response": None, "timed_out": False, "error": None}
        
        def kill_on_timeout():
            """Timer callback to forcefully kill the Lean process"""
            if self.process and self.process.poll() is None:
                logger.warning(f"⏱️  Timeout {timeout}s exceeded, killing Lean process PID={self.process.pid}")
                self._log_process_health(self._get_process_health(), "at timeout: ")
                # Set flag first to avoid races (EOF may fire right after SIGTERM)
                result["timed_out"] = True
                try:
                    # Kill the entire process group
                    os.killpg(os.getpgid(self.process.pid), signal.SIGTERM)
                    time.sleep(SIGTERM_WAIT_TIME)
                    # If still alive, use SIGKILL
                    if self.process.poll() is None:
                        os.killpg(os.getpgid(self.process.pid), signal.SIGKILL)
                except Exception as e:
                    logger.error(f"Failed to kill process: {e}")
                    result["error"] = f"Failed to kill process: {e}"
        
        # Start the timer
        timer = threading.Timer(timeout, kill_on_timeout)
        timer.start()
        
        try:
            # Try to send command normally
            response = self._send_command(command)
            timer.cancel()  # Success - cancel the timer
            return response
        
        except (IOError, ValueError) as e:
            timer.cancel()
            # Python native I/O errors (not converted to Lean exceptions)
            if result["timed_out"]:
                logger.error(f"⏱️  Process killed due to timeout ({timeout}s)")
                self._reset_process()
                raise FunctionTimedOut(timeout)
            else:
                logger.warning(f"⚠️  I/O error detected: {e}, resetting process")
                self._log_process_health(self._get_process_health(), "at I/O error: ")
                self._reset_process()
                raise LeanCrashError(f"I/O error: {e}")
        
        except LeanCrashError as e:
            timer.cancel()
            # Check if timeout-related
            if result["timed_out"]:
                self._reset_process()
                raise FunctionTimedOut(timeout)
            
            # Log health for EOF/BrokenPipe errors
            if isinstance(e, (LeanEOFError, LeanBrokenPipeError)):
                error_type = "EOF" if isinstance(e, LeanEOFError) else "BrokenPipe"
                logger.warning(f"⚠️  {error_type} error detected, resetting process")
                self._log_process_health(self._get_process_health(), f"at {error_type}: ")
            else:
                logger.warning(f"⚠️  LeanCrashError detected, resetting process")
            
            self._reset_process()
            raise
        
        except Exception as e:
            timer.cancel()
            if result["timed_out"]:
                self._reset_process()
                raise FunctionTimedOut(timeout)
            raise
        
        finally:
            # Ensure timer is cancelled
            if timer.is_alive():
                timer.cancel()

    def create_env(self, code: str, timeout: int = 60):
        """Create a new environment (for caching headers)."""
        command = {"cmd": code}
        # Use threading-based timeout that can actually kill the process
        response = self._send_command_with_timeout(command, timeout)
        
        if get_error_msg(response) is None:
            self.header = code
        
        return response

    def extend_env(self, context_id: int, code: str, timeout: int = 60, infotree_type=None):
        """Extend an existing environment with new code."""
        if infotree_type is None:
            command = {"cmd": code, "env": context_id, "gc": True}
        else:
            command = {"cmd": code, "env": context_id, "infotree": infotree_type, "gc": True}
        
        # Use threading-based timeout that can actually kill the process
        response = self._send_command_with_timeout(command, timeout)
        
        return response

    def get_cache_stats(self) -> Dict:
        """Get caching statistics."""
        total_requests = self.cache_hits + self.cache_misses
        hit_rate = (self.cache_hits / total_requests * 100) if total_requests > 0 else 0
        
        return {
            "enabled": self.enable_cache,
            "cache_hits": self.cache_hits,
            "cache_misses": self.cache_misses,
            "cache_refreshes": self.cache_refreshes,
            "hit_rate": f"{hit_rate:.1f}%",
            "cached_envs": len(self.env_cache),
            "max_cached_envs": self.max_cached_envs,
            "max_env_reuse_count": self.max_env_reuse_count,
            "env_use_counts": dict(self.env_use_counts),
            "total_commands": self.run_command_total,
        }

    def clear_cache(self):
        """Clear the environment cache."""
        cleared = len(self.env_cache)
        self.env_cache.clear()
        self.env_use_counts.clear()
        logger.info(f"🗑️  Cleared {cleared} cached environments")

    def start_process(self):
        """Start the Lean REPL process."""
        def preexec_fn():
            # Memory limit (aligned with kimina-lean-server: only on Linux)
            if settings.HARD_ENFORCE_MEMORY_LIMIT and platform.system() != "Darwin":
                soft_limit = settings.REPL_MEMORY_LIMIT_GB * 1024 * 1024 * 1024
                hard_limit = soft_limit
                resource.setrlimit(resource.RLIMIT_AS, (soft_limit, hard_limit))
            
            # No CPU limit on REPL (aligned with kimina-lean-server)
            # Most Lean proofs take up to one core
            # Adjustment via max REPLs and timeout
            os.setsid()

        start_time = time.time()
        logger.info(f"🚀 Starting Lean process...")
        logger.info(f"📁 REPL path: {path_to_repl}")
        logger.info(f"📁 Mathlib path: {path_to_mathlib}")
        logger.info(f"📁 Tacs path: {path_to_tacs}")
        
        if not os.path.exists(path_to_repl):
            raise LeanCrashError(f"REPL not found at: {path_to_repl}")
        if not os.path.exists(path_to_mathlib):
            raise LeanCrashError(f"Mathlib not found at: {path_to_mathlib}")
        if not os.path.exists(path_to_tacs):
            raise LeanCrashError(f"Tacs not found at: {path_to_tacs}")
        
        # Use standard subprocess.Popen
        # Use lean-tacs as working directory since it depends on both mathlib and tacs
        self.process = subprocess.Popen(
            ["lake", "env", path_to_repl],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=self.error_file,
            text=True,
            bufsize=1,
            cwd=path_to_tacs,
            env=os.environ,
            preexec_fn=preexec_fn,
        )
        
        startup_time = time.time() - start_time
        logger.info(f"✅ Lean process started in {startup_time:.2f}s, PID: {self.process.pid}")

    def get_error_content(self):
        """Read error content from stderr."""
        if self.error_file is None:
            return ""
        self.error_file.seek(0)
        return self.error_file.read()

    def close(self):
        """Terminate the REPL process and all child processes."""
        try:
            self.process.stdin.close()
            os.killpg(os.getpgid(self.process.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        finally:
            self.process.wait()
    
    def _reset_process(self):
        """Reset the Lean process after a timeout or crash.
        
        This method:
        1. Kills the old process
        2. Clears the environment cache (old env_ids are invalid)
        3. Starts a new process
        4. Resets psutil tracking
        """
        logger.warning("🔄 Resetting Lean process after error...")
        
        # Kill old process if still alive
        try:
            if self.process and self.process.poll() is None:
                os.killpg(os.getpgid(self.process.pid), signal.SIGKILL)
                self.process.wait(timeout=2)
        except Exception as e:
            logger.error(f"Error killing old process: {e}")
        
        # Clear environment cache (env_ids are no longer valid)
        old_cache_size = len(self.env_cache)
        self.env_cache.clear()
        self.env_use_counts.clear()
        if old_cache_size > 0:
            logger.info(f"🗑️  Cleared {old_cache_size} cached environments")
        
        # Start new process
        try:
            self.start_process()
            logger.info("✅ Lean process reset successfully")
        except Exception as e:
            logger.error(f"❌ Failed to reset process: {e}")
            raise LeanCrashError(f"Failed to reset Lean process: {e}")

    def __del__(self):
        if hasattr(self, 'process'):
            self.close()
    
    
if __name__ == "__main__":
    # Create REPL with caching enabled
    repl = LeanREPL(enable_cache=True, max_cached_envs=10)

    codes = [
        "import Mathlib\ntheorem t1 : 1+1=2 := rfl",
        "import Mathlib\ntheorem t2 : 2+2=4 := rfl",  # Reuses environment
        "import Mathlib\ntheorem t3 : 3+3=6 := rfl",  # Reuses environment
    ]

    for code in codes:
        response = repl.one_pass_verify(code, timeout=60)
        print(response)

    # Inspect cache performance
    print(repl.get_cache_stats())
    # {'cache_hits': 2, 'cache_misses': 1, 'hit_rate': '66.7%', ...}

    repl.close()