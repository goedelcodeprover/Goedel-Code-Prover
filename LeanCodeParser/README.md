# LeanCodeParser

LeanCodeParser focuses on processing Lean source produced by large language models. It provides tools to extract code blocks from raw text, parse declaration structure, build a code tree, and normalize import headers.

## Feature overview
- Extract Lean snippets from Markdown or plain text, stripping line and block comments
- Parse declarations into structured code blocks with metadata: name, location, whether they contain `sorry`, content, etc.
- Build a tree representing hierarchical relationships between code blocks
- Normalize import headers by adding necessary import statements
- Support expanding and validating code blocks for consistent structure

## Installation

```bash
pip install -e /path/to/LeanCodeParser
```

Or install from source:

```bash
cd /path/to/LeanCodeParser
pip install .
```

## Quick start

### Basic usage: extract and parse code blocks

```python
from LeanCodeParser import LeanCodeTree, extract_code_blocks, parse_code_blocks, CodeBlock

# Extract Lean code from Markdown
raw_text = """
# Example
```lean
import Mathlib.Data.List.Basic

def test_def (x : Nat) : Nat := x + 1
lemma test_lemma : true := by simp
```
"""

lean_code = extract_code_blocks(raw_text)
blocks = parse_code_blocks(lean_code)

for block in blocks:
    print(f"{block.type}: {block.name}")
    print(f"  Has sorry: {block.has_sorry}")
    print(f"  Lines: {block.start_line}-{block.end_line}")
```

### Build a code tree with LeanCodeTree

```python
from LeanCodeParser import LeanCodeTree

code = """
import Mathlib.Data.List.Basic
set_option maxHeartbeats 1000000

def test_def (x : Nat) : Nat := x + 1
lemma test_lemma : true := by simp
theorem test_theorem : true := by sorry
"""

# Create a tree; theorem or lemma is picked as the root automatically
tree = LeanCodeTree(code)

# Normalize environment (imports, sorry, etc.)
tree.normalize_env()

# Find a specific node
theorem_node = tree.find_node("test_theorem")

# Expand a node (add children)
if theorem_node:
    new_code = """
    lemma helper_lemma : true := by simp
    theorem test_theorem : true := by simp
    """
    tree.expand(theorem_node, new_code, sanity_check=True)

# Emit final code
final_code = tree.to_code(target_key="test_theorem")
print(final_code)
```

### Utility functions

```python
from LeanCodeParser import (
    extract_code_blocks,
    parse_code_blocks,
    remove_comments,
    rephrase_header,
    sanity_check,
    CodeBlock,
)

# Extract code blocks
lean_code = extract_code_blocks(markdown_text)

# Remove comments
clean_code = remove_comments(lean_code)

# Parse into structured blocks
blocks = parse_code_blocks(clean_code)

# Normalize import header
if blocks and blocks[0].type == "header":
    normalized_header = rephrase_header(blocks[0])

# Check similarity between blocks
is_similar = sanity_check(existing_blocks, new_block)
```

## API reference

### LeanCodeTree

Main code-tree class for managing and manipulating Lean code as a tree.

- `__init__(data: str, target_key: str | None = None)` — build a tree from a code string
- `normalize_env()` — normalize environment (imports, sorry, etc.)
- `find_node(key: str)` — find a node by key
- `expand(node: TreeNode, data: str, do_sanity_check: bool = True)` — expand a node
- `to_code(target_key: str | None = None)` — produce a code string
- `walk_level()` — walk nodes by level
- `walk_leaves()` — walk leaf nodes

### CodeBlock

Dataclass for a code block with fields:
- `name: str` — block name
- `type: str` — block type (e.g. `"theorem"`, `"lemma"`, `"def"`, `"header"`, …)
- `content: str` — source content
- `start_line: Optional[int]` — start line
- `end_line: Optional[int]` — end line
- `has_sorry: bool` — whether the block contains `sorry`
- `metadata: dict[str, Any]` — extra metadata

### Utility functions

- `extract_code_blocks(text: str, *, warn_on_empty: bool = True) -> str` — extract Lean from text
- `remove_comments(code: str) -> str` — strip comments
- `parse_code_blocks(code: str) -> CodeBlockList` — parse into a list of blocks
- `rephrase_header(header: CodeBlock) -> CodeBlock` — normalize import header
- `sanity_check(nodes: CodeBlockList, node: CodeBlock) -> bool` — check block similarity

## Tips

- `LeanCodeTree` automatically picks `theorem` or `lemma` as the root when present
- `normalize_env()` adds imports such as `import Mathlib` and `import Tacs` when needed
- `expand()` supports a sanity check so new code matches the original structure
- Type hints are supported across the API for better IDE completion

## License

This project is intended for internal research experiments and does not currently ship a public license.
