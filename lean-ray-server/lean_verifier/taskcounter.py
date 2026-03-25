"""
Task counter — thread-safe task state tracking.

Tracks total task count.
Can be shared globally as a Ray actor.
"""

import threading
from typing import Dict

import ray


class TaskCounter:
    """Thread-safe task counter (plain class)."""
    
    def __init__(self):
        """Initialize the task counter."""
        self._lock = threading.Lock()
        self._total_tasks = 0
    
    def add_tasks(self, count: int = 1):
        """Increment the task count."""
        with self._lock:
            self._total_tasks += count
    
    def remove_tasks(self, count: int = 1):
        """Decrement the task count."""
        with self._lock:
            self._total_tasks = max(0, self._total_tasks - count)
    
    def get_status(self) -> Dict[str, int]:
        """Return the current task status."""
        with self._lock:
            return {
                "total_tasks": self._total_tasks
            }
    
    def reset(self):
        """Reset the counter."""
        with self._lock:
            self._total_tasks = 0


# Ray actor variant of TaskCounter (global shared)
@ray.remote
class GlobalTaskCounter:
    """Globally shared task counter (Ray actor)."""
    
    def __init__(self):
        """Initialize the task counter."""
        self._lock = threading.Lock()
        self._total_tasks = 0
    
    def add_tasks(self, count: int = 1):
        """Increment the task count."""
        with self._lock:
            self._total_tasks += count
    
    def remove_tasks(self, count: int = 1):
        """Decrement the task count."""
        with self._lock:
            self._total_tasks = max(0, self._total_tasks - count)
    
    def get_status(self) -> Dict[str, int]:
        """Return the current task status."""
        with self._lock:
            return {
                "total_tasks": self._total_tasks
            }
    
    def reset(self):
        """Reset the counter."""
        with self._lock:
            self._total_tasks = 0


def get_or_create_global_task_counter():
    """Get or create the globally shared task counter."""
    counter_name = "global_task_counter"
    try:
        # Try to get an existing counter
        counter = ray.get_actor(counter_name)
        return counter
    except ValueError:
        # Does not exist; try to create a new one
        try:
            counter = GlobalTaskCounter.options(
                name=counter_name,
                lifetime="detached"
            ).remote()
            return counter
        except ValueError:
            # Creation may fail if another process/replica just created it; fetch again
            # This can happen under concurrent initialization (race)
            counter = ray.get_actor(counter_name)
            return counter

