"""
┌─────────────────────────────────────────────────────────────┐
│  _verify_full_code (outermost, with retry loop)              │
│  for attempt in range(max_retries + 1):                      │
│      try:                                                     │
│          response = _send_command_with_timeout(...)  ────┐   │
│          return response  # success                          │   │
│      except FunctionTimedOut:  # timeouts only             │   │
│          → retry                                           │   │
│      except Exception:  # other errors                     │   │
│          → stop retrying, fail                             │   │
└───────────────────────────────────────────────────────────┼───┘
                                                            │
                        ┌───────────────────────────────────┘
                        ↓
┌─────────────────────────────────────────────────────────────┐
│  _send_command_with_timeout (middle: timeout + I/O)        │
│                                                              │
│  1. Start timer (separate thread)                            │
│     timer = Timer(timeout, kill_on_timeout)                 │
│                                                              │
│  2. try:                                                     │
│        response = _send_command(command)  ──────────┐       │
│        timer.cancel()  # success, cancel timer      │       │
│        return response                              │       │
│                                                      │       │
│     except (IOError, ValueError, BrokenPipeError):  │       │
│        timer.cancel()                               │       │
│        if result["timed_out"]:  # timer fired       │       │
│            _reset_process()                         │       │
│            raise FunctionTimedOut ←─────────────────┼───┐   │
│        else:  # real I/O error                      │   │   │
│            _reset_process()                         │   │   │
│            raise LeanCrashError ←───────────────────┼─┐ │   │
│                                                      │ │ │   │
│     except LeanCrashError:  # from _send_command    │ │ │   │
│        timer.cancel()                               │ │ │   │
│        if result["timed_out"]:                      │ │ │   │
│            raise FunctionTimedOut ←─────────────────┼─┼─┘   │
│        _reset_process()                             │ │     │
│        raise  # re-raise LeanCrashError ←───────────┼─┘     │
└─────────────────────────────────────────────────────┼───────┘
                                                      │
                        ┌─────────────────────────────┘
                        ↓
┌─────────────────────────────────────────────────────────────┐
│  _send_command (lowest: actual I/O)                          │
│                                                              │
│  Possible failures:                                          │
│                                                              │
│  1. Write (lines ~319–320):                                  │
│     self.process.stdin.write(json_command)                  │
│     self.process.stdin.flush()                              │
│     ↓                                                        │
│     BrokenPipeError if Lean died and the pipe broke         │
│     ↓                                                        │
│     Caught ~361:                                             │
│     except BrokenPipeError:                                 │
│         raise LeanCrashError("broken pipe") ────────┐       │
│                                                      │       │
│  2. Read (~330):                                     │       │
│     line = self.process.stdout.readline()           │       │
│     ↓                                                │       │
│     if not line:  # EOF                             │       │
│         raise LeanCrashError("EOF") ────────────────┤       │
│                                                      │       │
│  3. JSON (~369):                                     │       │
│     response_json = json.loads(response_str)        │       │
│     ↓                                                │       │
│     except json.JSONDecodeError:                    │       │
│         raise LeanCrashError("Malformed JSON") ─────┤       │
│                                                      │       │
│  4. stderr (~382):                                   │       │
│     if error_content:                               │       │
│         raise LeanCrashError("Lean error") ─────────┤       │
│                                                      │       │
│  All LeanCrashError propagate up to                   │       │
│  _send_command_with_timeout                              │
└─────────────────────────────────────────────────────────────┘
"""
