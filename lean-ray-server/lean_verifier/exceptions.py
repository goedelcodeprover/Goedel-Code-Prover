"""
Lean Verifier Exception Classes

All custom exceptions for the Lean verification system.
"""


class FunctionTimedOut(Exception):
    """Timeout exception raised when Lean process exceeds time limit"""
    def __init__(self, timeout_seconds=None):
        self.timeout_seconds = timeout_seconds
        if timeout_seconds:
            super().__init__(f"Lean process timed out after {timeout_seconds} seconds")
        else:
            super().__init__("Lean process timed out")


class LeanCrashError(Exception):
    """Base class for Lean process errors"""
    pass


class LeanEOFError(LeanCrashError):
    """
    EOF error - Lean process closed output stream
    
    This typically indicates:
    - Lean process crashed due to invalid code
    - Out of memory (OOM killer terminated the process)
    - Internal Lean compiler bug
    - Process was forcefully killed
    """
    pass


class LeanBrokenPipeError(LeanCrashError):
    """
    Broken pipe error - Lean process communication failed
    
    This typically indicates:
    - Lean process crashed while we were writing to stdin
    - Timing issue: process died between write and read
    - Usually follows an EOF error in rapid succession
    """
    pass

