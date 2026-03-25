"""
Decomposition configuration module
"""
import os
from dataclasses import dataclass
from pathlib import Path

from common.constants import QUICKCHECK_TACTIC  # noqa: F401 — re-export for back-compat

PROJECT_ROOT = Path(__file__).parent.parent

@dataclass(frozen=True)
class DecomposeConfig:
    """Decomposition configuration class"""
    
    # LLM API configuration (field names consistent with prover Config)
    api_base: str = "http://localhost:8901/v1"
    model: str = ""
    api_key: str = "dummy"
    
    # Azure OpenAI configuration (auto-enabled when api_base contains .azure.com)
    azure_api_version: str = os.getenv("AZURE_API_VERSION", "2025-03-01-preview")
    azure_managed_identity_client_id: str = os.getenv("AZURE_MANAGED_IDENTITY_CLIENT_ID", "")
    
    input_token_price: float = 0.05
    output_token_price: float = 3.00
    budget_limit: float = 100.00

    temperature: float = 0.9  # LLM generation temperature, controls output randomness (0-1)
    max_tokens: int = 16000  # Maximum tokens for LLM generation
    reasoning_effort: str = "medium"  # Reasoning model thinking intensity: "low", "medium", "high"
    
    # Gemini API key (set environment variable when using Gemini)
    GEMINI_API_KEY: str = os.getenv("GEMINI_API_KEY", "")
    
    # Lean verification server configuration
    lean_server_url: str = "http://localhost:8900"  # Lean verification server address
    timeout: int = 300  # Timeout for a single verification request (seconds)
    
    # Data and output configuration
    benchmark_file: str = "benchmark/verina_bench.json"  # Benchmark problem file path
    output_dir: str = "results"  # Output results directory
    
    # Decomposition and verification configuration
    quickcheck_tactic: str = QUICKCHECK_TACTIC  # QuickCheck verification tactic
    pass_k: int = 1  # pass@k: run k times per problem, select the result with the lowest score
    score_tolerance: float = 0.05  # Score tolerance for pass@k selection (0.05=5%): scores within this range in the same tier are treated as equivalent, preferring fewer lines
    max_lemmas: int = 0  # Filter solutions where lemma+theorem count exceeds this value during pass@k selection, 0 means no limit
    num_iterations: int = 128  # Maximum recursive decomposition iterations per problem
    target_selection_temperature: float = 0.9  # Softmax temperature for target selection, higher = more uniform, lower = biased toward high-scoring targets
    
    # Concurrency configuration
    max_workers: int = 512  # Maximum concurrent LLM requests
    lean_max_concurrent: int = 96  # Lean Server maximum concurrency (rate limiting)
    max_concurrent_tasks: int = 512  # Maximum concurrent tasks (controls thread count and FD count)
    
    # Prompt template
    prompt_template: str = """
You are an expert in Lean 4 theorem proving. Your task is to decompose a theorem into smaller, provable lemmas.

**Think step by step.** Before writing code, first analyze the theorem structure and explain your decomposition strategy in a `<reasoning>` block.

## Task
Decompose the theorem `{theorem_name}` into helper lemmas, then prove the original theorem by combining them.

## Decomposition Strategies

**1. Structural Decomposition** — Match goal structure
- `P ∧ Q` → Split into `lemma_P` and `lemma_Q`, combine with `And.intro` or `⟨_, _⟩`
- `P ∨ Q` → Prove one side, use `Or.inl` or `Or.inr`
- `∃ x, P x` → First find witness, then prove `P witness`
- `∀ x, P x` → Use `intro x`, prove for arbitrary `x`

**2. Induction Decomposition** — For recursive structures
- `List α` → Base case `[]` + inductive step `x :: xs`
- `Nat` → Base case `0` + inductive step `n + 1`
- Extract each case as a separate lemma with explicit induction hypothesis

**3. Rewrite Chain** — For equational goals `A = D`
- Break into: `A = B`, `B = C`, `C = D`
- Combine with `Trans.trans` or `calc`

**4. Case Analysis** — When proof differs by condition
- Split by `Decidable`, `match`, or `if-then-else`
- Each branch becomes a separate lemma

## Output Requirements

1. **Reasoning first**: Wrap your analysis in `<reasoning>...</reasoning>` tags before any code
2. **Helper lemmas**: Use `lemma` keyword, body is `sorry`
3. **Main theorem**: Use `theorem` keyword, prove it using the lemmas (NO `sorry`)
6. **Format**: Wrap ALL code in a single ```lean block

## Example

<reasoning>
The goal is to prove `sum xs = foldr (· + ·) 0 xs` for any list `xs`.
This is an equality over a recursive structure (List), so I'll use **Induction Decomposition**:
- Base case: `sum [] = foldr (· + ·) 0 []` → both simplify to 0
- Inductive step: assuming `sum xs = foldr ...`, prove for `x :: xs`
I'll create two lemmas: `sum_zero` for base case, `sum_cons` for inductive step.
</reasoning>

```lean
-- Helper lemmas (with sorry)
lemma sum_zero : sum [] = 0 := by sorry

lemma sum_cons (x : Nat) (xs : List Nat) (ih : sum xs = foldr (· + ·) 0 xs) :
    sum (x :: xs) = foldr (· + ·) 0 (x :: xs) := by sorry

-- Main theorem (NO sorry - uses the lemmas)
theorem sum_eq_foldr (xs : List Nat) : sum xs = foldr (· + ·) 0 xs := by
  induction xs with
  | nil => exact sum_zero
  | cons x xs ih => exact sum_cons x xs ih
```

## Problem to Decompose

{formal_problem}
""".strip()
