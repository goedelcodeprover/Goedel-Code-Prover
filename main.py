#!/usr/bin/env python3
"""
Lean4-CodeVerifier Unified Pipeline

Two-stage automated proof system:
  Stage 1 - Decompose: Break theorems into smaller auxiliary lemmas (LLM + Lean verification)
  Stage 2 - Prove:     Complete proofs for lemmas still containing sorry (LLM + diff + Lean verification)

Usage:
  # Full pipeline (decompose + prove)
  python main.py --input_file benchmark/verina_bench.json

  # Run decompose only
  python main.py --input_file benchmark/verina_bench.json --stages decompose

  # Run prove only (input is already decomposed JSON)
  python main.py --input_file results/decomposed.json --stages prove

  # Specify config file
  python main.py --input_file benchmark/verina_bench.json -c config.yaml
"""

import argparse
import asyncio
import concurrent.futures
import json
import logging
import sys
from datetime import datetime
from pathlib import Path
from dataclasses import replace
from typing import List, Dict, Optional

import yaml

from common.logger import suppress_noisy_loggers, LOG_FORMAT

logging.basicConfig(
    level=logging.INFO,
    format=LOG_FORMAT,
    handlers=[logging.StreamHandler(sys.stdout)]
)
logger = logging.getLogger(__name__)
suppress_noisy_loggers()


def load_config(config_path: str) -> dict:
    """Load the unified configuration file."""
    with open(config_path, 'r', encoding='utf-8') as f:
        return yaml.safe_load(f)


def _extract_keys(source: dict, keys: list, target: dict):
    """Extract existing keys from source and write them into target."""
    for key in keys:
        if key in source:
            target[key] = source[key]


def build_decompose_config(unified_cfg: dict):
    """Build DecomposeConfig from unified configuration."""
    from decomposer.config import DecomposeConfig

    decompose_section = unified_cfg.get("decompose", {})
    llm_section = decompose_section.get("llm", {})

    # Build kwargs dict with only the fields present in the config
    kwargs = {}

    _extract_keys(llm_section, [
        "api_base", "model", "api_key", "temperature", "max_tokens", "reasoning_effort",
    ], kwargs)

    _extract_keys(decompose_section, [
        "input_token_price", "output_token_price", "budget_limit",
        "lean_server_url", "timeout",
        "pass_k", "max_lemmas", "num_iterations", "target_selection_temperature",
        "score_tolerance",
        "max_workers", "lean_max_concurrent", "max_concurrent_tasks",
    ], kwargs)

    # Data and output config - retrieved from the pipeline section
    _extract_keys(unified_cfg.get("pipeline", {}), [
        "benchmark_file", "output_dir",
    ], kwargs)

    return DecomposeConfig(**kwargs)


def build_prover_config(unified_cfg: dict, config_path: str):
    """Build prover Config from unified configuration."""
    from prover.config import Config

    prove_section = unified_cfg.get("prove", {})
    return Config.from_dict(prove_section, debug=unified_cfg.get("debug", False))


# ==================== Stage 2: Prove ====================

async def run_prove_stage(
    data: List[Dict],
    config,
    output_dir: str,
    timestamp: str,
    output_path: Optional[str] = None,
) -> None:
    """
    Run the proof completion stage.

    Args:
        data: Input data (formal_solution with EVOLVE-BLOCK markers)
        config: prover Config
        output_dir: Output directory
        timestamp: Timestamp string
        output_path: Final result output path
    """
    from prover.run import prove_all

    # Create main log file for per-problem summary results (not detailed proof process).
    # Clean up any leftover FileHandlers to avoid handler accumulation and FD leaks.
    for h in logger.handlers[:]:
        if isinstance(h, logging.FileHandler):
            h.close()
            logger.removeHandler(h)
    log_dir = Path(f"logs/prove_{timestamp}")
    log_dir.mkdir(parents=True, exist_ok=True)
    main_log_file = log_dir / f"main_prove_{timestamp}.log"
    main_fh = logging.FileHandler(main_log_file, encoding='utf-8')
    main_fh.setFormatter(logging.Formatter(LOG_FORMAT))
    logger.addHandler(main_fh)

    try:
        # Enlarge default thread pool to avoid run_in_executor queuing bottleneck
        loop = asyncio.get_running_loop()
        pool_size = config.prover.max_workers + config.prover.lean_max_concurrent
        loop.set_default_executor(concurrent.futures.ThreadPoolExecutor(max_workers=pool_size))
        logger.info(f"[Prove] Default thread pool set to {pool_size} threads")

        logger.info("=" * 80)
        logger.info(f"[Prove] Starting proof completion, timestamp: {timestamp}")
        logger.info("=" * 80)

        # Write temporary input file for prove_all
        temp_input = Path(output_dir) / f"prove_input_{timestamp}.json"
        temp_input.parent.mkdir(parents=True, exist_ok=True)
        with open(temp_input, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

        results_dir = Path(output_dir) / f"prove_results_{timestamp}"
        final_output = output_path or str(Path(output_dir) / f"proved_solutions_{timestamp}.json")

        from prover.config import set_config as set_prover_config
        set_prover_config(config)

        logger.info(f"[Prove] Input: {len(data)} problems, pass@{config.prover.pass_k}, "
                     f"epochs={config.prover.num_epochs}, LLM_concurrency={config.prover.max_workers}, Lean_concurrency={config.prover.lean_max_concurrent}")

        results = await prove_all(
            data_path=str(temp_input),
            config=config,
            output_path=final_output,
            results_dir=str(results_dir),
            log_dir=str(log_dir),
            summary_logger=logger,
        )

        # Read output file and summarize final results per problem
        with open(final_output, 'r', encoding='utf-8') as f:
            output_data = json.load(f)

        success_count = 0
        fail_count = 0
        skip_count = 0
        disproved_count = 0
        for item in output_data:
            pid = item.get("problem_id", "unknown")
            pass_k = config.prover.pass_k

            if item.get("disproved"):
                disproved_count += 1
                logger.info(f"  [Prove] {pid}: disproved (skipped)")
                continue
            if pass_k > 1 and "proof_runs" in item:
                # pass@k mode
                any_success = item.get("pass_k_success", False)
                runs = item.get("proof_runs", [])
                run_results = []
                for run in runs:
                    status = "success" if run.get("success") else "failed"
                    attempts = run.get("attempts", 0)
                    run_results.append(f"run{run.get('run_idx', '?')}:{status}({attempts} attempts)")
                summary = ", ".join(run_results)

                if any_success:
                    success_count += 1
                    logger.info(f"  [Prove] {pid}: success [{summary}]")
                else:
                    fail_count += 1
                    logger.warning(f"  [Prove] {pid}: failed [{summary}]")

            elif "proof_result" in item:
                # pass@1 mode
                pr = item["proof_result"]
                attempts = pr.get("attempts", 0)
                if pr.get("success"):
                    success_count += 1
                    logger.info(f"  [Prove] {pid}: success ({attempts} attempts)")
                else:
                    fail_count += 1
                    sorries = pr.get("remaining_sorries", "?")
                    err = pr.get("error_message", "")
                    err_str = f", error={err[:200]}" if err else ""
                    logger.warning(f"  [Prove] {pid}: failed ({attempts} attempts, {sorries} sorry remaining{err_str})")
            else:
                skip_count += 1
                logger.warning(f"  [Prove] {pid}: skipped (no formal_solution)")

        # Summary statistics
        total = success_count + fail_count + skip_count + disproved_count
        logger.info(f"[Prove] Summary: {total} problems, success={success_count}, failed={fail_count}, disproved={disproved_count}, skipped={skip_count}")
        if success_count + fail_count > 0:
            rate = 100 * success_count / (success_count + fail_count)
            logger.info(f"[Prove] Success rate: {rate:.1f}% ({success_count}/{success_count + fail_count})")

        # Print token usage statistics
        from prover.llm_client import print_usage_stats, get_usage_stats
        print_usage_stats(config)
        stats = get_usage_stats(config)
        logger.info(f"[Prove] Total cost: ${stats['estimated_cost_usd']:.4f} / ${stats['budget_limit']:.2f}")

        logger.info(f"[Prove] Proof results saved to: {final_output}")

    finally:
        # Ensure the main log file handler is always cleaned up
        main_fh.close()
        logger.removeHandler(main_fh)


# ==================== Main ====================

def main():
    parser = argparse.ArgumentParser(
        description="Lean4-CodeVerifier: Theorem decomposition + proof completion two-stage pipeline",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python main.py --input_file benchmark/verina_bench.json                          # Full pipeline
  python main.py --input_file benchmark/verina_bench.json --stages decompose       # Decompose only
  python main.py --input_file results/decomposed.json --stages prove               # Prove only
  python main.py --input_file benchmark/verina_bench.json -c config.yaml -o out.json
        """,
    )
    parser.add_argument(
        "--input_file",
        help="Input JSON file path (benchmark or already-decomposed JSON)",
        required=True,
    )
    parser.add_argument(
        "-c", "--config",
        default="config.yaml",
        help="Config file path (default: config.yaml)",
    )
    parser.add_argument(
        "-o", "--output",
        help="Final output file path (auto-generated by default)",
    )
    parser.add_argument(
        "--stages",
        nargs="+",
        choices=["decompose", "prove"],
        help="Which stages to run (default: read from config, usually decompose prove)",
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Show verbose logs",
    )

    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    # Load unified configuration
    unified_cfg = load_config(args.config)
    pipeline_cfg = unified_cfg.get("pipeline", {})

    # Determine which stages to run
    stages = args.stages or pipeline_cfg.get("stages", ["decompose", "prove"])
    output_dir = pipeline_cfg.get("output_dir", "results")
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')

    logger.info(f"Stages to run: {stages}")
    logger.info(f"Input file: {args.input_file}")
    logger.info(f"Output directory: {output_dir}")

    data = None

    # ===== Stage 1: Decompose =====
    if "decompose" in stages:
        from decomposer.run import run_decompose_stage

        decompose_cfg = build_decompose_config(unified_cfg)
        decompose_cfg = replace(decompose_cfg, benchmark_file=args.input_file)
        data = run_decompose_stage(
            benchmark_file=args.input_file,
            cfg=decompose_cfg,
            output_dir=output_dir,
            timestamp=timestamp,
        )

    # ===== Stage 1.5: Transform =====
    if "prove" in stages:
        from common.transform import transform_for_prover

        if data is None:
            # Prove-only mode, load from file
            logger.info(f"[Transform] Loading from file: {args.input_file}")
            with open(args.input_file, 'r', encoding='utf-8') as f:
                data = json.load(f)

        logger.info(f"[Transform] Adding EVOLVE-BLOCK markers for {len(data)} problems...")
        transformed_data = transform_for_prover(data)

        # Save the transformed intermediate file
        transformed_file = Path(output_dir) / f"transformed_{timestamp}.json"
        transformed_file.parent.mkdir(parents=True, exist_ok=True)
        with open(transformed_file, 'w', encoding='utf-8') as f:
            json.dump(transformed_data, f, ensure_ascii=False, indent=2)
        logger.info(f"[Transform] Saved to: {transformed_file}")

        # ===== Stage 2: Prove =====
        prover_cfg = build_prover_config(unified_cfg, args.config)
        asyncio.run(run_prove_stage(
            data=transformed_data,
            config=prover_cfg,
            output_dir=output_dir,
            timestamp=timestamp,
            output_path=args.output,
        ))

    logger.info("=" * 80)
    logger.info("Pipeline complete!")
    logger.info("=" * 80)


if __name__ == "__main__":
    main()
