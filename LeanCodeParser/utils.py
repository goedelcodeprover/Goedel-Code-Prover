"""
Utility functions for parsing and manipulating Lean 4 code.

This module provides functionality to:
- Extract and parse Lean code blocks from text
- Remove comments from Lean code
- Parse code into structured CodeBlock objects
- Manipulate proofs and replace 'sorry' placeholders
- Perform sanity checks on code transformations
"""

from __future__ import annotations

import logging
import re
import warnings
from dataclasses import dataclass, field
from typing import Any, Mapping
from warnings import warn
from difflib import SequenceMatcher

from common.constants import LEAN_REPL_LINE_OFFSET

logger = logging.getLogger(__name__)

# Regular expressions for matching proof patterns and 'sorry' placeholders
PROOF_INTRO_PATTERN = re.compile(r"(:=\s*(?:by\s+)?)", re.MULTILINE)
SORRY_WORD_PATTERN = re.compile(r"\bsorry\b")
SORRY_BY_PATTERN = re.compile(r"\bby\s+sorry\b")
SORRY_DEF_PATTERN = re.compile(r":=\s+sorry\b")

@dataclass
class CodeBlock:
    """Typed representation of a Lean code block.
    
    A CodeBlock represents a single declaration or code unit in Lean 4,
    such as a theorem, lemma, definition, namespace, etc.
    
    Attributes:
        name: The name of the code block (e.g., function name, theorem name)
        type: The type of declaration (e.g., "theorem", "lemma", "def", "namespace")
        content: The full content of the code block as a string
        start_line: Optional starting line number (1-indexed)
        end_line: Optional ending line number
        has_sorry: Whether the code block contains a 'sorry' placeholder
        is_proved: Whether the code block is fully proved (no sorry)
        metadata: Additional metadata dictionary for storing extra information
    """

    name: str
    type: str
    content: str
    start_line: int | None = None
    end_line: int | None = None
    has_sorry: bool = False
    is_proved: bool = False
    metadata: dict[str, Any] = field(default_factory=dict)

    @classmethod
    def from_mapping(cls, data: Mapping[str, Any]) -> "CodeBlock":
        """Create a CodeBlock from a dictionary/mapping.
        
        Unknown keys in the mapping are stored in the metadata field.
        
        Args:
            data: A dictionary containing CodeBlock fields
            
        Returns:
            A new CodeBlock instance
        """
        known_keys = {"name", "type", "content", "start_line", "end_line", "has_sorry", "metadata"}
        metadata = dict(data.get("metadata", {}))
        # Store any unknown keys in metadata
        for key, value in data.items():
            if key in known_keys:
                continue
            metadata[key] = value
        return cls(
            name=str(data.get("name", "")),
            type=str(data.get("type", "")),
            content=str(data.get("content", "")),
            start_line=data.get("start_line"),
            end_line=data.get("end_line"),
            has_sorry=bool(data.get("has_sorry", False)),
            is_proved=bool(data.get("is_proved", False)),
            metadata=metadata,
        )

    def to_mapping(self) -> dict[str, Any]:
        """Convert the CodeBlock to a dictionary representation.
        
        Only includes optional fields (start_line, end_line) if they are not None.
        Merges metadata fields into the top-level dictionary.
        
        Returns:
            A dictionary representation of the CodeBlock
        """
        result: dict[str, Any] = {
            "name": self.name,
            "type": self.type,
            "content": self.content,
            "has_sorry": self.has_sorry,
            "is_proved": self.is_proved,
        }
        if self.start_line is not None:
            result["start_line"] = self.start_line
        if self.end_line is not None:
            result["end_line"] = self.end_line
        if self.metadata:
            result.update(self.metadata)
        return result

CodeBlockList = list[CodeBlock]

# ------------------------------------------------------------------
# Text and code handling
# ------------------------------------------------------------------
def extract_lean4_code(text: str, *, warn_on_empty: bool = True) -> str:
    """Extract Lean 4 code blocks from markdown-formatted text.
    
    Looks for code blocks marked with ```lean4 or ```lean and extracts
    their content. If no code blocks are found, returns the original text.
    
    Args:
        text: Input text that may contain markdown code blocks
        warn_on_empty: If True, issue a warning when no code blocks are found
        
    Returns:
        Extracted code content, or original text if no blocks found
    """
    pattern = r"```(?:lean4|lean)?\n(.*?)```"
    matches = re.findall(pattern, text, re.DOTALL)
    if not matches or not matches[0].strip():
        if warn_on_empty:
            warn("No Lean code blocks found in the text; returning the original text.")
        return text
    return "\n\n".join(matches)

def remove_comments(code: str) -> str:
    """Remove all comments from Lean code.
    
    Removes both single-line comments (starting with --) and multi-line
    comments (enclosed in /- ... -/). Also removes inline comments (-- ...).
    
    Args:
        code: Lean code string that may contain comments
        
    Returns:
        Code with all comments removed
    """
    source = code

    result: list[str] = []
    in_multiline_comment = False

    for line in source.split("\n"):
        if in_multiline_comment:
            # We're inside a multiline comment, look for the end
            if "-/" in line:
                # Find where the comment ends
                end_idx = line.find("-/")
                # Keep everything after -/
                remaining = line[end_idx + 2:]
                # Process the remaining part for inline comments
                inline_comment_idx = remaining.find("--")
                if inline_comment_idx != -1:
                    remaining = remaining[:inline_comment_idx].rstrip()
                if remaining.strip():  # If there's code after the comment
                    result.append(remaining)
                in_multiline_comment = False
            # Otherwise, skip the entire line (it's inside a comment)
            continue

        # Skip lines that are only single-line comments (starting with --)
        stripped = line.strip()
        if stripped.startswith("--"):
            # Check if it's a doc comment /-- which should be preserved differently
            # But for now, we'll remove all -- comments
            continue

        # Process the line to remove inline comments and multiline comments
        processed_line = ""
        i = 0
        
        while i < len(line):
            # Check for start of multiline comment
            if i < len(line) - 1 and line[i:i+2] == "/-":
                # Check if comment ends on the same line
                end_idx = line.find("-/", i + 2)
                if end_idx != -1:
                    # Comment ends on same line, skip it and continue
                    i = end_idx + 2
                    continue
                else:
                    # Comment continues to next line
                    in_multiline_comment = True
                    break
            
            # Check for single-line comment (--)
            if i < len(line) - 1 and line[i:i+2] == "--":
                # Found inline comment, stop processing this line
                break
            
            processed_line += line[i]
            i += 1
        
        # Add the processed line (remove trailing whitespace)
        result.append(processed_line.rstrip())

    cleaned = "\n".join(result)
    return cleaned

# ------------------------------------------------------------------
# Structured parsing
# ------------------------------------------------------------------

def parse_lemma_name(line: str) -> str | None:
    """Parse a lemma/theorem declaration line to get the name."""
    match = re.match(r"lemma\s+([^\s:()\[\]{}]+)", line)
    if match:
        return match.group(1)
    match = re.match(r"theorem\s+([^\s:()\[\]{}]+)", line)
    if match:
        return match.group(1)
    return None

def fine_closed_theorem(code: str, line_index: int, repl_line_offset: int = LEAN_REPL_LINE_OFFSET) -> str | None:
    """Find the closed theorem in the code."""
    code_lines = code.split("\n")
    name = None
    ## there exists offset due to repl
    # c.f. https://github.com/leanprover-community/repl
    actual_line_index = line_index + repl_line_offset  
    for line in code_lines[actual_line_index:0:-1]:
        if line.strip().startswith(("theorem", "lemma")):
            name = parse_lemma_name(line)
            break
    if name is None:
        context = "\n".join(code_lines[max(0, line_index - 5):line_index + 5])
        logger.warning(f"Failed to find enclosing theorem at line {line_index}:\n{context}")
    return name

def parse_code_blocks(code: str) -> CodeBlockList:
    """Parse Lean code into a list of structured CodeBlock objects.
    
    Identifies declarations (theorems, lemmas, definitions, namespaces, etc.)
    and groups them into CodeBlock objects. Also extracts header content
    (imports and options) as a separate block.
    
    Args:
        code: Raw Lean code string (may contain markdown code blocks)
        
    Returns:
        List of CodeBlock objects representing the parsed code structure
    """
    # Extract code from markdown if needed
    code = extract_lean4_code(code) if "```" in code else code
    cleaned = remove_comments(code)
    code_lines = cleaned.split("\n")

    # Patterns for matching different types of Lean declarations
    patterns = [
        (r"namespace\s+([^\s]+)", "env"),
        (r"end\s+([^\s]+)", "env"),
        (
            r"(partial\s+)?(def|theorem|lemma|axiom|instance|class|structure|inductive)\s+([^\s:()\[\]{}]+)",
            None,
        ),
        (r"variable\s+([\[\(\{])([^\]\)\}]+)", "variable"),
    ]

    declarations: list[dict[str, Any]] = []

    # First pass: identify all declarations
    for idx, line in enumerate(code_lines):
        stripped = line.strip()
        actual_start = idx

        # Handle attributes (e.g., @[...]) that appear before declarations
        if idx > 0 and code_lines[idx - 1].strip().startswith("@["):
            actual_start = idx - 1

        # Try to match each pattern
        for pattern, decl_type in patterns:
            match = re.match(pattern, stripped)
            if not match:
                continue

            # Extract name and type based on pattern
            if decl_type == "env":
                name = match.group(1)
                type_name = "namespace" if "namespace" in pattern else "end"
            elif decl_type == "variable":
                content = match.group(2).strip()
                name_match = re.match(r"(\w+)", content)
                name = name_match.group(1) if name_match else f"variable_{idx}"
                type_name = "variable"
            else:
                # Handle declarations like def, theorem, lemma, etc.
                is_partial = match.group(1) is not None
                decl_type_str = match.group(2)
                name = match.group(3)
                type_name = f"partial {decl_type_str}" if is_partial else decl_type_str

            declarations.append(
                {
                    "line_num": idx,
                    "actual_start": actual_start,
                    "type": type_name,
                    "name": name,
                    "full_line": stripped,
                }
            )
            break

    # Extract header (imports and options before first declaration)
    header: CodeBlock | None = None
    if declarations and declarations[0]["actual_start"] > 0:
        header_lines = code_lines[: declarations[0]["actual_start"]]
        header_content = "\n".join(header_lines).strip()
        if header_content:
            header = CodeBlock(
                name="Header (imports)",
                type="header",
                start_line=1,
                end_line=declarations[0]["actual_start"],
                has_sorry=False,
                content=header_content,
            )

    # Second pass: create CodeBlock objects for each declaration
    blocks: CodeBlockList = []
    if header:
        blocks.append(header)

    for idx, decl in enumerate(declarations):
        start_line = decl["actual_start"]
        # End line is the start of the next declaration, or end of file
        end_line = (
            declarations[idx + 1]["actual_start"]
            if idx + 1 < len(declarations)
            else len(code_lines)
        )

        block_content = "\n".join(code_lines[start_line:end_line])
        contains_sorry = "sorry" in block_content or "admit" in block_content

        blocks.append(
            CodeBlock(
                name=decl["name"],
                type=decl["type"],
                start_line=start_line + 1,  # Convert to 1-indexed
                end_line=end_line,
                has_sorry=contains_sorry,
                content=block_content.strip(),
            )
        )

    return blocks

def deduplicate_code_blocks(blocks: CodeBlockList) -> CodeBlockList:
    """Deduplicate code blocks based on their name.
    
    For blocks with the same name:
    - If some blocks don't contain 'sorry', keep the last one without 'sorry'
    - If all blocks contain 'sorry', keep the last one
    
    Args:
        blocks: List of CodeBlock objects to deduplicate
        
    Returns:
        Deduplicated list of CodeBlock objects, preserving order of first occurrence
    """
    # Group blocks by name
    blocks_by_name: dict[str, list[CodeBlock]] = {}
    for block in blocks:
        if block.name not in blocks_by_name:
            blocks_by_name[block.name] = []
        blocks_by_name[block.name].append(block)
    
    # For each name, select the best block
    result: CodeBlockList = []
    seen_names: set[str] = set()
    
    # Process blocks in original order
    for block in blocks:
        if block.name in seen_names:
            continue
        
        seen_names.add(block.name)
        same_name_blocks = blocks_by_name[block.name]
        
        # Find blocks without 'sorry'
        blocks_without_sorry = [b for b in same_name_blocks if not b.has_sorry]
        
        if blocks_without_sorry:
            # Keep the last block without 'sorry'
            selected_block = blocks_without_sorry[-1]
        else:
            # All blocks have 'sorry', keep the last one
            selected_block = same_name_blocks[-1]
        
        result.append(selected_block)
    
    return result

def rephrase_header(header: CodeBlock) -> CodeBlock:
    """Normalize and standardize the header block (imports and options).
    
    Ensures that required imports ("import Mathlib" and "import Tacs") and
    the maxHeartbeats option are present. Removes duplicates and organizes
    imports and options in a consistent order.
    
    Args:
        header: CodeBlock representing the header section
        
    Returns:
        Modified header CodeBlock with normalized imports and options
    """
    import_pattern = re.compile(r"^\s*import\s+\S+")
    option_pattern = re.compile(r"^\s*set_option\s+")  # Match all set_option
    open_pattern = re.compile(r"^\s*open\s+")  # Match open statements

    def _add_unique(target: list[str], value: str) -> None:
        """Add value to list only if it's not already present."""
        if value not in target:
            target.append(value)

    raw_header_lines = header.content.split("\n") if header.content else []
    imports: list[str] = []
    options: list[str] = []
    opens: list[str] = []
    other_header_lines: list[str] = []

    # Categorize header lines
    for line in raw_header_lines:
        stripped = line.strip()
        if not stripped:
            continue
        if import_pattern.match(stripped):
            _add_unique(imports, stripped)
        elif option_pattern.match(stripped):
            _add_unique(options, stripped)  # Keep original set_option
        elif open_pattern.match(stripped):
            _add_unique(opens, stripped)
        else:
            _add_unique(other_header_lines, stripped)
            
    # Ensure required imports are present
    if "import Mathlib" not in imports:
        imports.insert(0, "import Mathlib")
    if "import Tacs" not in imports:
        imports.append("import Tacs")
    # Ensure maxHeartbeats 0 is present
    has_max_heartbeats = any("maxHeartbeats" in opt for opt in options)
    if not has_max_heartbeats:
        options.append("set_option maxHeartbeats 0")

    # Order: import → set_option → open → other
    header.content = "\n".join(imports + options + opens + other_header_lines).strip()

    return header

def remove_proof(content: str) -> str:
    """Remove the proof body and replace it with 'sorry'.
    
    Removes everything after the proof introduction (':=' or ':= by' or '=>' or '=> by') 
    and replaces it with ' := by sorry'.
    Handles both single-line and multi-line patterns (e.g., pattern matching with '| _ => by').
    Preserves newlines in the declaration signature.
    
    Args:
        content: Code content that may contain a proof
        
    Returns:
        Code with proof replaced by ' := by sorry'
        
    Raises:
        ValueError: If no proof pattern is found in the content
    """
    content = content.strip()
    
    # Pattern 1: ":= by" (most common case for theorems/lemmas)
    # Match := followed by whitespace (including newlines) and 'by'
    # \s+ already matches newlines, no need to normalize
    match = re.search(r':=\s+by\b', content)
    if match:
        prefix = content[:match.start()].rstrip()
        return prefix + " := by sorry"
    
    # Pattern 2: "=> by" (alternative format, including pattern matching like "| _ => by")
    match = re.search(r'=>\s+by\b', content)
    if match:
        prefix = content[:match.start()].rstrip()
        # For pattern matching syntax, keep the pattern structure
        if '|' in prefix:
            return prefix + " => by sorry"
        else:
            return prefix + " := by sorry"
    
    # Pattern 3: ":=" (definitions or other declarations)
    # Find all := occurrences and use the last one
    matches = list(re.finditer(r':=', content))
    if matches:
        last_match = matches[-1]
        prefix = content[:last_match.start()].rstrip()
        return prefix + " := by sorry"
    
    # Pattern 4: "=>" (alternative format, including pattern matching)
    # Find all => occurrences and use the last one
    matches = list(re.finditer(r'=>', content))
    if matches:
        last_match = matches[-1]
        prefix = content[:last_match.start()].rstrip()
        if '|' in prefix:
            return prefix + " => by sorry"
        else:
            return prefix + " := by sorry"
    
    # No proof pattern found
    raise ValueError(
        f"Unexpected proof format in remove_proof: no ':=' or '=>' found in content. "
        f"Content preview: {content[:200]}..."
    )

def replace_sorry_by_tactic(content: str, tactic: str) -> str:
    """Replace 'sorry' placeholders with a specific tactic.
    
    Handles different forms of 'sorry':
    - "by sorry" -> "by {tactic}"
    - ":= sorry" -> ":= by {tactic}"
    - "sorry" -> "{tactic}"
    
    Args:
        content: Code content containing 'sorry' placeholders
        tactic: The tactic string to replace 'sorry' with
        
    Returns:
        Code with 'sorry' replaced by the given tactic
    """
    updated = SORRY_BY_PATTERN.sub(f"by {tactic}", content)
    updated = SORRY_DEF_PATTERN.sub(f":= by {tactic}", updated)
    updated = SORRY_WORD_PATTERN.sub(tactic, updated)
    return updated
            
def _similar_enough(a: str, b: str, *, threshold: float = 0.9) -> bool:
    """Check if two strings are similar enough based on sequence matching.
    
    Uses difflib.SequenceMatcher to compute similarity ratio.
    
    Args:
        a: First string to compare
        b: Second string to compare
        threshold: Minimum similarity ratio (0.0 to 1.0) to consider similar
        
    Returns:
        True if strings are identical or similarity ratio >= threshold
    """
    if a == b:
        return True
    if not a or not b:
        return False
    ratio = SequenceMatcher(None, a, b).ratio()
    return ratio >= threshold

#  compare type, treat lemma and theorem as equivalent
def _type_equivalent(t1: str, t2: str) -> bool:
    equiv_types = {"lemma", "theorem"}
    if t1 in equiv_types and t2 in equiv_types:
        return True
    return t1 == t2

def sanity_check(nodes: CodeBlockList, node: CodeBlock) -> bool:
    """Check if a node's signature matches any node in the list.
    
    Compares the declaration signature (everything before ':=') of the
    given node with nodes in the list that have the same name and type.
    Used to verify that code transformations preserve the original structure.
    
    If a matching name and type is found but signatures don't match,
    the function will automatically merge the old signature with the new proof
    (correcting the node in-place).
    
    Args:
        nodes: List of CodeBlock objects to search (may be modified in-place)
        node: CodeBlock to check against the list
        
    Returns:
        True if a matching node with same name and type is found (signature
        may be corrected), False otherwise
    """
    for node_ in nodes:
        if node.name == node_.name and _type_equivalent(node.type, node_.type):
            # Compare only the signature (before ':='), not the proof body
            old_content = node.content.split(":=", 1)[0].strip()
            new_content = node_.content.split(":=", 1)[0].strip()
            # Normalize whitespace: replace all whitespace with single spaces
            old_normalized = re.sub(r'\s+', ' ', old_content)
            new_normalized = re.sub(r'\s+', ' ', new_content)
            if _similar_enough(old_normalized, new_normalized):
                return True
            else:
                # If signatures don't match, merge old signature with new proof
                warnings.warn(f"Sanity check failed but merged old signature with new proof for {node_.name}")
                if ":=" in node_.content:
                    new_proof = node_.content.split(":=", 1)[1].strip()
                    # Use old signature + new proof
                    node_.content = f"{old_content} := {new_proof}"
                return True  # Return True since we found a match and corrected it
    return False