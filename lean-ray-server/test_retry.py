#!/usr/bin/env python3
"""
Test retry mechanism.
"""
import requests
import time
import json

def test_retry_mechanism():
    """Test retry mechanism."""
    base_url = "http://localhost:8000"
    
    print("🚀 Testing retry mechanism")
    
    # Test single verification (with retries)
    print("\n📋 Testing single verification with retries...")
    payload = {
        "code": "def add (a b : Nat) : Nat := a + b",
        "timeout": 60,
        "max_retries": 3
    }
    
    try:
        start_time = time.time()
        response = requests.post(f"{base_url}/verify", json=payload, timeout=60)
        response.raise_for_status()
        
        data = response.json()
        elapsed = time.time() - start_time
        print(f"✅ Single verification succeeded: {elapsed:.2f}s")
        print(f"📊 Result: {data}")
        
    except Exception as e:
        print(f"❌ Single verification failed: {e}")
    
    # Test batch verification (with retries)
    print("\n📋 Testing batch verification with retries...")
    test_codes = [
        "def add (a b : Nat) : Nat := a + b",
        "def mul (a b : Nat) : Nat := a * b",
        "def sub (a b : Nat) : Nat := if a >= b then a - b else 0",
        "def div (a b : Nat) : Nat := if b > 0 then a / b else 0",
        "def mod (a b : Nat) : Nat := if b > 0 then a % b else a"
    ] * 400  # 2000 test cases
    
    payload = {
        "codes": test_codes,
        "timeout": 60,
        "max_retries": 3
    }
    
    try:
        start_time = time.time()
        response = requests.post(f"{base_url}/verify/batch", json=payload, timeout=300)
        response.raise_for_status()
        
        data = response.json()
        elapsed = time.time() - start_time
        
        # Aggregate results
        total_tasks = len(test_codes)
        success_count = sum(1 for result in data.get("results", []) if result.get("is_valid_no_sorry", False))
        timeout_count = sum(1 for result in data.get("results", []) if "timeout" in str(result.get("error", "")))
        retry_count = sum(1 for result in data.get("results", []) if "attempt" in str(result.get("error", "")))
        
        print(f"✅ Batch verification finished: {elapsed:.2f}s")
        print(f"📊 Total tasks: {total_tasks}")
        print(f"📊 Succeeded: {success_count}")
        print(f"📊 Timeouts: {timeout_count}")
        print(f"📊 Retries: {retry_count}")
        print(f"📊 Success rate: {success_count/total_tasks*100:.1f}%")
        
        if timeout_count > 0:
            print(f"⚠️ Still {timeout_count} timeout(s)")
        else:
            print("🎉 No timeouts — retry mechanism is working!")
        
    except Exception as e:
        print(f"❌ Batch verification failed: {e}")

if __name__ == "__main__":
    test_retry_mechanism()
