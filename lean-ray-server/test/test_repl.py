from lean_verifier.leanrepl import LeanREPL
from lean_verifier.utils import parse_client_response

    
def test_repl1():
    code = """import Mathlib\n\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\ntheorem test : 1 = 1 := by simp\n  
    """
    repl = LeanREPL()
    response = {}
    try:
      response["response"] = repl.one_pass_verify(code, 30)
    except Exception as e:
      response["error"] = str(e)
      pass
    messages = parse_client_response(response)
    assert messages["has_error"] == False
    assert messages["is_valid_no_sorry"] == True
    assert messages["is_valid_with_sorry"] == True
    
def test_repl2():
    code = """import Mathlib\n\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\ntheorem test : 1 = 1 := by\n  sorry
    """
    repl = LeanREPL()
    response = {}
    try:
      response["response"] = repl.one_pass_verify(code, 30)
    except Exception as e:
      response["error"] = str(e)
      pass
    messages = parse_client_response(response)
    assert messages["has_error"] == False
    assert messages["is_valid_no_sorry"] == False
    assert messages["is_valid_with_sorry"] == True
    
def test_repl3():
    code = """import Mathlib\n\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\ntheorem test : 1 = 1 := by\n  test
    """
    repl = LeanREPL()
    response = {}
    try:
      response["response"] = repl.one_pass_verify(code, 30)
    except Exception as e:
      response["error"] = str(e)
      pass
    messages = parse_client_response(response)
    assert messages["has_error"] == True
    assert messages["is_valid_no_sorry"] == False
    assert messages["is_valid_with_sorry"] == False

if __name__ == "__main__":
  test_repl1()
  # test_repl2()
  # test_repl3()
