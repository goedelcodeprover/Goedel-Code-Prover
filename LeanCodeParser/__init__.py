"""LeanCodeParser package exports."""

from .tree import LeanCodeTree, TreeNode
from .utils import (
    CodeBlock,
    CodeBlockList,
    extract_lean4_code,
    parse_code_blocks,
    remove_comments,
    remove_proof,
    replace_sorry_by_tactic,
    rephrase_header,
    sanity_check,
    deduplicate_code_blocks,
    parse_lemma_name,
    fine_closed_theorem,
)

__all__ = [
    "LeanCodeTree",
    "TreeNode",
    "CodeBlock",
    "CodeBlockList",
    "extract_lean4_code",
    "parse_code_blocks",
    "remove_comments",
    "remove_proof",
    "replace_sorry_by_tactic",
    "rephrase_header",
    "sanity_check",
    "deduplicate_code_blocks",
    "parse_lemma_name",
    "fine_closed_theorem",
]

