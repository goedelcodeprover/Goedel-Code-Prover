"""
Configuration module
"""

import os
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

import yaml


@dataclass
class LeanServerConfig:
    """Lean verification server configuration"""
    url: str = "http://localhost:8000"
    timeout: int = 60
    timeout_buffer: int = 60


@dataclass
class LLMConfig:
    """LLM configuration"""
    api_base: str = ""
    api_key: Optional[str] = None
    api_version: Optional[str] = None
    use_v1_api: bool = False  # Use next-gen v1 API
    use_azure_ad: bool = False
    managed_identity_client_id: Optional[str] = None
    model: str = "gpt-4o"
    temperature: float = 0.2
    max_tokens: int = 8192
    timeout: int = 300
    # Billing configuration (price unit: USD per million tokens)
    input_token_price: float = 0.10      # Input token price
    output_token_price: float = 0.40     # Output token price
    budget_limit: float = 100.00         # Budget limit (USD)


@dataclass
class ProverConfig:
    """Proof strategy configuration (three-stage epoch mode)"""
    pass_k: int = 1                   # Run pass_k times per problem; success on any run counts as pass
    # Three stages per epoch: fix(i times) -> eliminate(1 time) -> sorry hard-replace(1 time)
    num_epochs: int = 10              # k = total number of epochs
    fix_attempts_per_epoch: int = 5   # i = fix attempts per epoch
    max_total_attempts: int = 20      # Total attempt limit (reserved)
    max_workers: int = 8              # LLM max concurrency
    lean_max_concurrent: int = 8       # Lean Server max concurrency
    max_concurrent_tasks: int = 512    # Max concurrent tasks (controls open log files to avoid FD exhaustion)
    enable_per_run_log: bool = True   # Whether to write a separate log file per run; disabling greatly reduces FD count, avoiding Too many open files


@dataclass
class Config:
    """Main configuration"""
    lean_server: LeanServerConfig = field(default_factory=LeanServerConfig)
    llm: LLMConfig = field(default_factory=LLMConfig)
    prover: ProverConfig = field(default_factory=ProverConfig)
    debug: bool = False
    
    @classmethod
    def from_dict(cls, data: dict, debug: bool = False) -> "Config":
        """Build Config from a dictionary

        Args:
            data: Dictionary containing lean_server / llm / prover sub-keys
            debug: Debug flag
        """
        lean_data = data.get("lean_server", {})
        lean_config = LeanServerConfig(
            url=lean_data.get("url", "http://localhost:8000"),
            timeout=lean_data.get("timeout", 60),
            timeout_buffer=lean_data.get("timeout_buffer", 60),
        )

        llm_data = data.get("llm", {})
        api_key = llm_data.get("api_key")
        if api_key and isinstance(api_key, str) and api_key.startswith("${") and api_key.endswith("}"):
            env_var = api_key[2:-1]
            api_key = os.environ.get(env_var)

        llm_config = LLMConfig(
            api_base=llm_data.get("api_base", ""),
            api_key=api_key,
            api_version=llm_data.get("api_version"),
            use_v1_api=llm_data.get("use_v1_api", False),
            use_azure_ad=llm_data.get("use_azure_ad", False),
            managed_identity_client_id=llm_data.get("managed_identity_client_id"),
            model=llm_data.get("model", "gpt-4o"),
            temperature=llm_data.get("temperature", 0.2),
            max_tokens=llm_data.get("max_tokens", 8192),
            timeout=llm_data.get("timeout", 300),
            input_token_price=llm_data.get("input_token_price", 0.10),
            output_token_price=llm_data.get("output_token_price", 0.40),
            budget_limit=llm_data.get("budget_limit", 100.00),
        )

        prover_data = data.get("prover", {})
        prover_config = ProverConfig(
            pass_k=prover_data.get("pass_k", 1),
            num_epochs=prover_data.get("num_epochs", 10),
            fix_attempts_per_epoch=prover_data.get("fix_attempts_per_epoch", 5),
            max_total_attempts=prover_data.get("max_total_attempts", 20),
            max_workers=prover_data.get("max_workers", 8),
            lean_max_concurrent=prover_data.get("lean_max_concurrent", 8),
            max_concurrent_tasks=prover_data.get("max_concurrent_tasks", 512),
            enable_per_run_log=prover_data.get("enable_per_run_log", True),
        )

        return cls(
            lean_server=lean_config,
            llm=llm_config,
            prover=prover_config,
            debug=debug,
        )

    @classmethod
    def from_yaml(cls, yaml_path: str) -> "Config":
        """Load configuration from a YAML file (compatible with standalone prove config and unified config)"""
        with open(yaml_path, "r") as f:
            data = yaml.safe_load(f)

        if "prove" in data:
            return cls.from_dict(data["prove"], debug=data.get("debug", False))
        return cls.from_dict(data, debug=data.get("debug", False))


# Default config path
_DEFAULT_CONFIG_PATH = Path(__file__).parent.parent / "config.yaml"

# Global config instance
_config: Optional[Config] = None


def set_config(config: Config) -> None:
    """Set the global config instance"""
    global _config
    _config = config


def get_config(config_path: str = None) -> Config:
    """Get the config instance"""
    global _config
    if _config is None:
        path = config_path or str(_DEFAULT_CONFIG_PATH)
        if Path(path).exists():
            _config = Config.from_yaml(path)
        else:
            _config = Config()
    return _config


def reload_config(config_path: str = None) -> Config:
    """Reload configuration"""
    global _config
    _config = None
    return get_config(config_path)
