# Goedel-Code-Prover

[[Paper]](https://arxiv.org/abs/2603.19329) [[Website]](https://goedelcodeprover.github.io/) [[Model]](https://huggingface.co/Goedel-LM/Goedel-Code-Prover-8B)

A two-stage automated Lean 4 theorem proving system: **Decompose** (theorem decomposition) + **Prove** (proof completion).

Given a Lean 4 theorem with a `sorry` placeholder, Goedel-Code-Prover uses LLMs to first break it into smaller lemmas, then fill in every `sorry` with a machine-checked proof.

## How It Works

```
Input (theorem + sorry)
        |
        v
  +-------------+
  |  Decompose  |  LLM splits complex theorems into smaller helper lemmas
  |             |  Iteratively refined via QuickCheck + complexity scoring
  +------+------+
         |  formal_solution (helper lemmas with sorry)
         v
  +-------------+
  |  Transform  |  Adds EVOLVE-BLOCK markers automatically
  |             |  Protects imports and theorem signatures from modification
  +------+------+
         |
         v
  +-------------+
  |    Prove    |  LLM fills each sorry via SEARCH/REPLACE diffs
  |             |  Multi-epoch strategy: prove -> fix -> eliminate
  +------+------+
         |
         v
Output (complete proof, no sorry)
```

## Prerequisites

- **Python** >= 3.10
- **Lean verification server** -- an HTTP server that compiles and checks Lean 4 code (see `lean-ray-server/` included in this repo)
- **LLM service** -- any OpenAI-compatible API (local vLLM, Azure OpenAI, Gemini, etc.)

## Quick Start

### 1. Install Python dependencies

```bash
pip install -r requirements.txt
```

### 2. Set up the Lean verification server

The Lean verification server is bundled at `lean-ray-server/`. Follow its own README to install Lean/Mathlib dependencies and start the server:

```bash
cd lean-ray-server
bash setup.sh          # Downloads repl, mathlib4, quickcheck, lean-tacs
bash start_server.sh   # Starts the Ray-based verification server
```

### 3. Start an LLM server

Any OpenAI-compatible API works. For example, with vLLM:

```bash
vllm serve your-model-name --port 8901
```

### 4. Configure

```bash
cp config.example.yaml config.yaml
# Edit config.yaml: set LLM and Lean server URLs, model name, concurrency, etc.
```

### 5. Run

```bash
# Full pipeline (decompose -> prove)
python main.py benchmark/verina_bench.json

# Decompose only
python main.py benchmark/verina_bench.json --stages decompose

# Prove only (from previously decomposed JSON)
python main.py results/decomposed_formal_solutions_*.json --stages prove

# Custom config and output path
python main.py benchmark/verina_bench.json -c config.yaml -o results/final.json

# Verbose logging
python main.py benchmark/verina_bench.json -v
```

### CLI Arguments

| Argument | Description |
|----------|-------------|
| `input_file` | Input JSON file (benchmark or pre-decomposed JSON) |
| `-c, --config` | Config file path (default: `config.yaml`) |
| `-o, --output` | Final output file path (default: auto-generated) |
| `--stages` | Stages to run: `decompose`, `prove`, or both |
| `-v, --verbose` | Enable verbose logging |

## Project Structure

```
Goedel-Code-Prover/
|-- main.py                    # Unified pipeline entry point
|-- config.example.yaml        # Configuration template (copy to config.yaml)
|-- transform.py               # EVOLVE-BLOCK marker transformation
|-- requirements.txt           # Python dependencies
|
|-- common/                    # Shared utilities
|   |-- budget.py              # Token usage tracking and budget management
|   |-- constants.py           # Shared constants (QUICKCHECK_TACTIC, etc.)
|   |-- io_utils.py            # JSON I/O and safe filename helpers
|   |-- lean_client.py         # Unified Lean verification client (sync + async)
|   +-- logger.py              # Logging setup and noisy-logger suppression
|
|-- decomposer/                # Stage 1: Theorem decomposition
|   |-- config.py              # DecomposeConfig dataclass
|   |-- run.py                 # Batch problem processing orchestrator
|   |-- verify_single.py       # Single-problem iterative decomposition logic
|   |-- verifier.py            # Lean verification with semaphore throttling
|   |-- scorer.py              # Complexity scoring and target selection
|   +-- utils.py               # LLM client setup, prompt building, budget
|
|-- prover/                    # Stage 2: Proof completion
|   |-- config.py              # Config dataclass (nested YAML structure)
|   |-- run.py                 # Async proof engine (pass@k, multi-epoch)
|   |-- lean_client.py         # Config-aware Lean client + cheating detection
|   |-- llm_client.py          # LLM API (OpenAI / Azure / Gemini)
|   |-- diff_utils.py          # SEARCH/REPLACE diff parsing and application
|   |-- sorry_revise.py        # sorry hard-replacement fallback
|   +-- eval.py                # pass@k evaluation and reporting
|
|-- LeanCodeParser/            # Lean code parser
|   |-- tree.py                # LeanCodeTree: structural representation
|   +-- utils.py               # Code block extraction and manipulation
|
|-- lean-ray-server/           # Bundled Lean verification server (Ray-based)
|   |-- lean_verifier/         # Server core (REPL management, HTTP API)
|   |-- quickcheck/            # QuickCheck Lean library (counterexample testing)
|   |-- test/                  # Server test suite
|   +-- setup.sh               # One-command server setup
|
|-- scripts/                   # Utility scripts
|   |-- eval_decomposed_json.py       # Evaluate decomposition results
|   |-- reselect_from_logs.py         # Re-select best from iteration logs
|   |-- test_llm_api.py               # Test LLM API connectivity
|   |-- benchmark_llm_throughput.py   # Measure LLM throughput
|   |-- check_llm_metrics.py          # Query vLLM server metrics
|   +-- profile_analysis.py           # Prove stage performance profiling
|
|-- benchmark/                 # Input benchmark data
|-- results/                   # Output results (git-ignored)
+-- logs/                      # Runtime logs (git-ignored)
```

## Configuration

All settings live in a single `config.yaml` (see `config.example.yaml` for the full template). The file has three sections:

### Pipeline

```yaml
pipeline:
  benchmark_file: "benchmark/verina_bench.json"
  output_dir: "results"
  stages: ["decompose", "prove"]    # Run one or both stages
```

### Decompose Stage

```yaml
decompose:
  llm:
    api_base: "http://localhost:8901/v1"
    model: "decompose-model"
    temperature: 0.9
    max_tokens: 16000
  lean_server_url: "http://localhost:8900"
  num_iterations: 128        # Max iterations per problem
  pass_k: 10                 # Run k times, pick best decomposition
  max_workers: 512           # Max concurrent LLM requests
  lean_max_concurrent: 96    # Max concurrent Lean verifications
  budget_limit: 100.00       # USD budget cap
```

### Prove Stage

```yaml
prove:
  llm:
    api_base: "http://localhost:8901/v1"
    model: "prove-model"
    temperature: 0.7
    max_tokens: 8192
  lean_server:
    url: "http://localhost:8900"
    timeout: 300
  prover:
    pass_k: 10                # Independent runs per problem
    num_epochs: 20            # Epochs per run
    fix_attempts_per_epoch: 5 # Fix attempts per epoch
    max_workers: 512          # Max concurrent LLM requests
```

The two stages can use different LLM models while sharing the same Lean verification server.

## Input / Output Format

### Input

A JSON array of problems, each with a `problem_id` and `formal_problem` (Lean 4 code containing `sorry`):

```json
[
  {
    "problem_id": "verina/verina_basic_1.lean",
    "formal_problem": "import Mathlib\n...\ntheorem example := by sorry"
  }
]
```

### Decompose Output (intermediate)

Adds a `formal_solution` field with decomposed lemmas (some still contain `sorry`):

```json
[
  {
    "problem_id": "verina/verina_basic_1.lean",
    "formal_problem": "...",
    "formal_solution": "... (helper lemmas with sorry) ..."
  }
]
```

### Final Output

Adds `proved_solution` (sorry-free code) and `proof_result` metadata:

```json
[
  {
    "problem_id": "verina/verina_basic_1.lean",
    "formal_problem": "...",
    "formal_solution": "...",
    "proved_solution": "... (complete proof, no sorry) ...",
    "proof_result": { "success": true, "attempts": 15 }
  }
]
```

## Core Mechanisms

### Theorem Decomposition (Stage 1)

1. Parse the theorem into a `LeanCodeTree` (structural representation)
2. Select the highest-complexity target using softmax-weighted probability
3. LLM generates helper lemmas + main theorem proof
4. Lean server verifies compilation; QuickCheck detects counterexamples
5. Iterate until fully proved or max iterations reached

### Proof Completion (Stage 2)

Each epoch consists of three phases:

1. **Prove / Fix** -- LLM generates SEARCH/REPLACE diffs to fill `sorry` or fix compilation errors
2. **Eliminate** -- Replace broken proof bodies with `sorry` to restore compilability (fallback)
3. **Sorry Replace** -- Hard-replace entire proof body with `sorry` (last-resort fallback)

Supports **pass@k**: each problem runs k independent times; any single success counts, with early stopping when a proof is found.

### Cheating Detection

The prover includes anti-cheating checks to ensure proof integrity:

- Extracts the original theorem signature and verifies the modified code still proves the original specification
- Detects non-standard axioms (e.g., `sorryAx`, custom axioms)
- EVOLVE-BLOCK markers restrict LLM modifications to proof bodies only, preventing signature changes

## License

MIT
