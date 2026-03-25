"""
Simple tree structures used for representing Lean code blocks.

This module is deliberately lightweight so it can be reused by different
components in the experiments without pulling additional dependencies.
"""

from __future__ import annotations

import logging
from collections import deque
from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass, field
from typing import Any, Mapping
import re

logger = logging.getLogger(__name__)
from .utils import CodeBlock
from .utils import sanity_check, rephrase_header, parse_code_blocks, deduplicate_code_blocks, fine_closed_theorem, \
                    remove_proof, replace_sorry_by_tactic

def _derive_key(data: CodeBlock) -> str | None:
    """Extract a key from a CodeBlock for use as a node identifier.
    
    Args:
        data: CodeBlock to extract key from
        
    Returns:
        The name of the code block, or None if empty
    """
    key = data.name
    return key or None

def _normalize_payload(data: CodeBlock | Mapping[str, Any]) -> CodeBlock:
    """Convert various payload types to a CodeBlock.
    
    Args:
        data: Either a CodeBlock instance or a dictionary/mapping
        
    Returns:
        A CodeBlock instance
        
    Raises:
        TypeError: If data is neither a CodeBlock nor a Mapping
    """
    if isinstance(data, CodeBlock):
        return data
    if isinstance(data, Mapping):
        return CodeBlock.from_mapping(data)
    raise TypeError(f"Unsupported code block payload: {type(data)!r}")


@dataclass
class TreeNode:
    """Basic tree node containing a normalized `CodeBlock` payload.
    
    A TreeNode represents a node in a tree structure where each node
    contains a CodeBlock. The tree structure allows hierarchical organization
    of Lean code blocks, useful for representing proof dependencies and
    code structure.
    
    Attributes:
        payload: The CodeBlock data stored in this node
        key: Optional key identifier (typically the code block name)
        parent: Reference to the parent node (None for root)
        children: List of child nodes
    """

    payload: CodeBlock
    key: str | None = None
    parent: TreeNode | None = field(default=None, repr=False)
    children: list["TreeNode"] = field(default_factory=list, repr=False)

    def __post_init__(self) -> None:
        """Initialize the key from the payload name if not set."""
        self.key = self.payload.name
        
    def is_equal(self, other: TreeNode) -> bool:
        """Check if this node is equal to another node.
        
        Two nodes are considered equal if they have the same key
        
        Args:
            other: TreeNode to compare with
            
        Returns:
            True if nodes are equal, False otherwise
        """
        return self.key == other.key

    # ------------------------------------------------------------------
    # Mutators
    # ------------------------------------------------------------------
    def merge(self, other: TreeNode) -> None:
        """Merge another node into this node.
        
        Only merges if the current node has 'sorry' or is not proved.
        If the node is already proved without 'sorry', it remains unchanged.
        
        Args:
            other: TreeNode to merge into this node
        """
        if self.payload.has_sorry or not self.payload.is_proved:
            self.payload.content = other.payload.content
            self.payload.has_sorry = other.payload.has_sorry
            self.payload.is_proved = other.payload.is_proved            
    
    def add_child(
        self,
        data: TreeNode,
    ) -> None:
        """Add a single child node to this node.
        
        Sets the parent reference of the child node to this node.
        
        Args:
            data: TreeNode to add as a child
        """
        data.parent = self
        self.children.append(data)

    def extend_children(
        self,
        items: Iterable[TreeNode],
    ) -> None:
        """Add multiple child nodes to this node.
        
        Sets the parent reference of each child node to this node.
        
        Args:
            items: Iterable of TreeNode objects to add as children
        """
        for item in items:
            item.parent = self
            self.children.append(item)

    def find(self, predicate: Callable[[TreeNode], bool]) -> TreeNode | None:
        """Find the first node in the subtree that matches the predicate.
        
        Searches using level-order traversal (breadth-first).
        
        Args:
            predicate: Function that takes a TreeNode and returns True if it matches
            
        Returns:
            First matching TreeNode, or None if not found
        """
        for node in self.walk_level():
            if predicate(node):
                return node
        return None

    def find_by_key(self, key: str) -> TreeNode | None:
        """Find a node by its key in the subtree.
        
        Args:
            key: The key to search for
            
        Returns:
            TreeNode with matching key, or None if not found
        """
        return self.find(lambda node: node.key == key)

    def path_to_root(self) -> list[TreeNode]:
        """Get the path from this node to the root.
        
        Returns:
            List of TreeNode objects from root to this node (inclusive)
        """
        node: TreeNode | None = self
        path: list[TreeNode] = []
        while node is not None:
            path.append(node)
            node = node.parent
        return list(reversed(path))

    # ------------------------------------------------------------------
    # Traversal helpers
    # ------------------------------------------------------------------
    def walk_level(self) -> Iterator[TreeNode]:
        """Traverse the subtree in level-order (breadth-first).
        
        Yields:
            TreeNode objects in level-order traversal
        """
        queue: deque[TreeNode] = deque([self])
        while queue:
            node = queue.popleft()
            yield node
            queue.extend(node.children)
    def to_dict(self, *, children_key: str = "children") -> dict[str, Any]:
        """Convert the subtree to a nested dictionary representation.
        
        Args:
            children_key: Key name to use for children in the dictionary
            
        Returns:
            Dictionary representation of the subtree
        """
        node_repr: dict[str, Any] = {
            "key": self.key,
            "payload": self.payload.to_mapping(),
            children_key: [child.to_dict(children_key=children_key) for child in self.children],
        }
        return node_repr


class LeanCodeTree:
    """Utility wrapper around :class:`TreeNode` for managing Lean code structures.
    
    This class provides a high-level interface for working with Lean code as a tree.
    It handles parsing Lean code strings, organizing code blocks into a tree structure,
    and managing the environment (imports, definitions) and proof targets.
    
    The tree separates the code into:
    - Environment nodes: imports, definitions, and other supporting code
    - Root node: The main theorem or lemma being proved
    - Child nodes: Sub-theorems or lemmas used in the proof
    """
    
    # Class constants for node names
    PLACEHOLDER_NAME = "placeholder"
    HEADER_NAME = "Header (imports)"
    
    def _get_target_key(self) -> str | None:
        """Get the target key safely.
        
        Returns:
            The target key if target is set, None otherwise
        """
        if hasattr(self, 'target') and self.target is not None:
            return self.target.key
        return None

    def __init__(
        self,
        data: str,
        target_key: str | None = None,
    ) -> None:
        """Initialize a LeanCodeTree from Lean code.
        
        Parses the code and identifies the target theorem/lemma. If target_key
        is provided, uses that specific declaration; otherwise, finds the first
        theorem or lemma.
        
        Args:
            data: Raw Lean code string to parse
            target_key: Optional name of the target theorem/lemma to prove
            
        Raises:
            ValueError: If no theorem or lemma is found
        """
        # Parse code into CodeBlock objects and create TreeNode instances
        code_nodes = [TreeNode(_normalize_payload(code_block), key=code_block.name) for code_block in parse_code_blocks(data)]
        placeholder = TreeNode(CodeBlock(name=self.PLACEHOLDER_NAME, type=self.PLACEHOLDER_NAME, content=self.PLACEHOLDER_NAME))
        placeholder_idx = -1
        env: list[TreeNode] = []
        root: TreeNode | None = None
        
        # Find the target node (theorem or lemma to prove)
        if target_key is not None:
            # Search backwards for the specified target
            for code_node in code_nodes[::-1]:
                if code_node.key == target_key:
                    placeholder_idx = code_nodes.index(code_node)
                    # Insert placeholder at target position for environment separation
                    env = code_nodes[:placeholder_idx] + [placeholder] + code_nodes[placeholder_idx + 1:]
                    root = code_node
                    break
        else:
            # Find first theorem or lemma
            for code_node in code_nodes[::-1]:
                if code_node.payload.type == "theorem" or code_node.payload.type == "lemma":
                    placeholder_idx = code_nodes.index(code_node)
                    env = code_nodes[:placeholder_idx] + [placeholder] + code_nodes[placeholder_idx + 1:]
                    root = code_node
                    break
        if env == [] or root is None:
            if target_key is not None:
                raise ValueError(f"No theorem or lemma found with key '{target_key}'")
            else:
                raise ValueError("No theorem or lemma found in the code. "
                               "Please ensure the code contains at least one theorem or lemma.")
        self.placeholder_idx = placeholder_idx
        self.set_env(env)
        self.root = root
        self._total_nodes = code_nodes
        self._saved_tree = {}
        
    def set_env(self, env: list[TreeNode]) -> None:
        """Set up and normalize the environment nodes.
        
        Processes the environment nodes (imports, definitions, etc.) by:
        1. Ensuring a header node exists and normalizing imports
        2. Collecting definition names
        3. Handling definitions with 'sorry' by converting to partial defs
        4. Marking all environment nodes as proved
        
        Args:
            env: List of TreeNode objects representing the environment
        """
        # Ensure header node exists and normalize it
        header_node: TreeNode | None = None 
        for node in env:
            if node.key == self.HEADER_NAME:
                header_node = node
                break
        if header_node is None:
            header_node = TreeNode(CodeBlock(name=self.HEADER_NAME, type="header", content="", has_sorry=False))
            env.insert(0, header_node)
            self.placeholder_idx += 1
        header_node.payload = rephrase_header(header_node.payload)
                
        # Process definitions: collect names and handle 'sorry' placeholders
        defs = []
        for node in env:
            code_block = node.payload
            if code_block.type == "def":
                defs.append(code_block.name)
                if code_block.has_sorry:
                    # Convert to partial def if not recursive, otherwise use PASS_PROOF
                    if "let rec" not in code_block.content:
                        code_block.type = "partial def"
                        code_block.content = code_block.content.replace("def", "partial def", 1)
                        code_block.has_sorry = False
                    else:
                        code_block.content = code_block.content.replace("sorry", "apply PASS_PROOF")
                        code_block.has_sorry = False
        
        # Mark all environment nodes as proved (they're assumed to be correct)
        self.env = env
        self.defs = defs
        
    def set_target(self, target_key: str | None = None) -> str:
        """Set the target node (theorem/lemma to prove).
        
        If target_key is provided, finds that specific node. Otherwise,
        finds the first node with a 'sorry' placeholder.
        
        Args:
            target_key: Optional name of the target node
            
        Returns:
            The key of the target node
            
        Raises:
            ValueError: If no suitable target node is found
        """
        target_node: TreeNode | None = None
        for node in self.walk_leaves():
            if target_key is not None:
                # If a specific key is provided, only match that key
                if node.key == target_key:
                    target_node = node
                    break
            else:
                # Find first node with 'sorry' if no specific key provided
                if node.payload.has_sorry:
                    target_node = node
                    break
        if target_node is None:
            if target_key is not None:
                raise ValueError(f"No target node found with key '{target_key}' that has 'sorry'")
            else:
                raise ValueError("No target node with 'sorry' found in the tree. "
                               "Please ensure there is at least one theorem or lemma with 'sorry'.")
        self.target = target_node
        return self.target.key
    
    def get_target(self) -> str:
        """Get the target node (theorem/lemma to prove).
        
        Returns:
            The target node
        """
        return self.target.payload.content

    def add_child(
        self,
        parent: TreeNode,
        data: str,
    ) -> TreeNode:
        """Add child nodes to a parent node from Lean code.
        
        Parses the provided code string and adds the resulting code blocks
        as children of the parent node.
        
        Args:
            parent: TreeNode to add children to
            data: Lean code string to parse and add as children
            
        Returns:
            The parent node (for method chaining)
        """
        code_blocks = parse_code_blocks(data)
        nodes = [TreeNode(_normalize_payload(code_block), key=code_block.name) for code_block in code_blocks]
        parent.extend_children(nodes)
        return parent

    def find_node(self, key: str) -> TreeNode | None:
        """Find a node by its key in the leaves of the tree.
        
        Args:
            key: The key to search for
            
        Returns:
            TreeNode with matching key, or None if not found
        """
        for node in self.walk_leaves():
            if node.key == key:
                return node
        return None
    
    def walk_level(self) -> Iterator[TreeNode]:
        """Traverse the tree in level-order starting from root.
        
        Yields:
            TreeNode objects in level-order traversal
        """
        queue: deque[TreeNode] = deque([self.root])
        while queue:
            node = queue.popleft()
            yield node
            queue.extend(node.children)
            
    def walk_leaves(self) -> Iterator[TreeNode]:
        r"""Traverse only the leaf nodes using depth-first search (DFS).
        
        Uses pre-order depth-first traversal: visits nodes from left to right,
        going deep before going wide. Leaf nodes are yielded as they are encountered.
        
        Example tree structure:
            A
           / \
          B   C
         / \   \
        D   E   F
        
        Traversal order: D, E, B, F, C, A
        Leaf nodes output: D, E, F (in depth-first, left-to-right order)
        
        Note: If leaf nodes are at different depths, they are visited in
        depth-first order (deeper nodes before shallower nodes at the same
        horizontal level).
        
        Yields:
            Leaf TreeNode objects in depth-first, left-to-right order
        """
        def _dfs(node: TreeNode) -> Iterator[TreeNode]:
            if not node.children:
                yield node
            else:
                for child in node.children:
                    yield from _dfs(child)
        
        yield from _dfs(self.root)
                
    # ------------------------------------------------------------------
    # Save and restore the tree
    # ------------------------------------------------------------------
    def to_dict(self, *, children_key: str = "children") -> dict[str, Any]:
        """Convert the tree to a dictionary representation.
        
        Args:
            children_key: Key name to use for children in the dictionary
            
        Returns:
            Dictionary representation of the tree including root and env
        """
        result = {
            "root": self.root.to_dict(children_key=children_key),
            "env": [node.to_dict(children_key=children_key) for node in self.env],
            "placeholder_idx": self.placeholder_idx,
        }
        # Save target_key if target is set, so it can be restored later
        target_key = self._get_target_key()
        if target_key is not None:
            result["target_key"] = target_key
        return result
    
    def from_dict(self, data: dict[str, Any], *, children_key: str = "children") -> None:
        """Restore the tree from a dictionary representation.
        
        Args:
            data: Dictionary representation of the tree
            children_key: Key name used for children in the dictionary
            
        Raises:
            KeyError: If required keys are missing from the dictionary
            ValueError: If the dictionary structure is invalid
        """
        # Validate required keys
        required_keys = ["root", "env", "placeholder_idx"]
        missing_keys = [key for key in required_keys if key not in data]
        if missing_keys:
            raise KeyError(f"Missing required keys in dictionary: {missing_keys}")
        
        def _node_from_dict(node_dict: dict[str, Any]) -> TreeNode:
            """Recursively reconstruct a TreeNode from dictionary."""
            if "payload" not in node_dict:
                raise KeyError("Missing 'payload' key in node dictionary")
            payload = CodeBlock.from_mapping(node_dict["payload"])
            node = TreeNode(payload, key=node_dict.get("key"))
            children = node_dict.get(children_key, [])
            for child_dict in children:
                child_node = _node_from_dict(child_dict)
                node.add_child(child_node)
            return node
        
        self.root = _node_from_dict(data["root"])
        self.env = [_node_from_dict(node_dict) for node_dict in data["env"]]
        self.placeholder_idx = data["placeholder_idx"]
        # Rebuild _total_nodes by collecting all nodes from env and root subtree
        self._total_nodes = []
        for env_node in self.env:
            self._total_nodes.extend(env_node.walk_level())
        self._total_nodes.extend(self.root.walk_level())
        # Restore target if it was saved
        if "target_key" in data:
            target_key = data["target_key"]
            target_node = self.find_node(target_key)
            if target_node is not None:
                self.target = target_node
            # If target node not found, target will remain unset (which is acceptable)
        else:
            # Clear target since the old node objects are no longer valid
            if hasattr(self, 'target'):
                delattr(self, 'target')
    
    def clone(self, id: str) -> None:
        """Save a snapshot of the whole tree.
        
        Stores the current tree for later restoration. This is useful
        for preserving the state of proofs before modifications.
        """
        self._saved_tree[id] = self.to_dict()
    
    def restore(self, id: str) -> None:
        """Restore the tree to its previously saved state.
        
        Restores the entire tree structure from the saved snapshot
        created by clone().
        
        Raises:
            ValueError: If no tree has been cloned previously
        """
        if id not in self._saved_tree:
            raise ValueError(f"No tree has been saved for id: {id}")
        self.from_dict(self._saved_tree[id])
            
    def remove(self, id: str) -> None:
        """Remove a saved tree snapshot.
        
        Removes the saved tree snapshot with the given id.
        
        Raises:
            KeyError: If the id does not exist
        """
        if id not in self._saved_tree:
            raise KeyError(f"No saved tree found for id: {id}")
        del self._saved_tree[id]
            
    # ------------------------------------------------------------------
    # Manipulate the tree leaves
    # ------------------------------------------------------------------
    def truncate_leaves(self, tactic: str | None = None) -> None:
        """Remove proofs from leaf nodes, optionally replacing with a tactic.
        
        This method performs two operations in sequence:
        1. Removes proof body from leaf nodes (except target node and nodes that
           are already proved), replacing them with 'sorry'.
        2. If tactic is provided, replaces 'sorry' placeholders with the given
           tactic in ALL leaf nodes (including target and proved nodes).
        
        Args:
            tactic: Optional tactic string to replace 'sorry' with. If None,
                   only step 1 is performed (proofs are removed but not replaced).
            
        Raises:
            ValueError: If target is not set
        """
        target_key = self._get_target_key()
        if target_key is None:
            raise ValueError("Target is not set. Call set_target() first.")
        # Collect all leaf nodes first to avoid iterating twice
        leaf_nodes = list(self.walk_leaves())
        
        # Remove proofs from leaf nodes (except target or node that is already proved)
        for node in leaf_nodes:
            if node.key == target_key or node.payload.is_proved:
                continue
            node.payload.content = remove_proof(node.payload.content)

        # Replace 'sorry' with tactic if provided
        if tactic is not None:
            for node in leaf_nodes:
                node.payload.content = replace_sorry_by_tactic(node.payload.content, tactic)
            

    # ------------------------------------------------------------------
    # Expand the tree
    # ------------------------------------------------------------------
    def expand(self, node: TreeNode, data: str, do_sanity_check: bool = True) -> TreeNode:
        """Expand a node by adding child nodes from parsed code.
        
        Parses the provided code and adds new theorem/lemma nodes as children
        of the given node. If sanity check fails (target theorem not found by name),
        uses the proof from the last theorem in generated code combined with the
        original theorem signature.
        
        Args:
            node: TreeNode to expand
            data: Lean code string containing new theorems/lemmas
            do_sanity_check: If True, attempt sanity check and auto-recover if failed
            
        Returns:
            The expanded node (for method chaining)
        """
        code_blocks = deduplicate_code_blocks(parse_code_blocks(data))
        
        # Check if sanity check passes
        sanity_passed = sanity_check(code_blocks, node.payload) if do_sanity_check else True
        
        # Collect theorem/lemma code blocks
        theorem_lemma_blocks = [cb for cb in code_blocks if cb.type in ("theorem", "lemma")]
        
        new_nodes = []
        target_key = self._get_target_key()
        target_node = None
        
        for code_block in theorem_lemma_blocks:
            new_node = TreeNode(_normalize_payload(code_block), key=code_block.name)
            if new_node.key == target_key:
                target_node = new_node
            elif all(not new_node.is_equal(saved_node) for saved_node in self._total_nodes):
                new_nodes.append(new_node)

        # If sanity check failed: use last code block's proof with original signature
        if not sanity_passed and target_node is None:
            # Find the last code block with same type as original (theorem or lemma)
            # If no same-type block found, fall back to last theorem/lemma
            original_type = node.payload.type
            same_type_blocks = [cb for cb in theorem_lemma_blocks if cb.type == original_type]
            last_block = same_type_blocks[-1] if same_type_blocks else (theorem_lemma_blocks[-1] if theorem_lemma_blocks else None)
            
            if last_block and ":=" in last_block.content:
                last_proof = last_block.content.split(":=", 1)[1].strip()
                # Get original signature
                original_content = node.payload.content
                original_sig = original_content.split(":=", 1)[0].strip() if ":=" in original_content else original_content.strip()
                
                # Combine: original signature + last block's proof
                combined_content = f"{original_sig} := {last_proof}"
                recovered_block = CodeBlock(
                    name=node.payload.name,
                    type=node.payload.type,
                    content=combined_content,
                    is_proved=False
                )
                target_node = TreeNode(_normalize_payload(recovered_block), key=node.payload.name)
                
                # Remove the last block from new_nodes if it was added
                new_nodes = [n for n in new_nodes if n.key != last_block.name]

        # Move target_key node to the end if it exists
        if target_node is not None:
            new_nodes.append(target_node)
        node.extend_children(new_nodes)
        self._total_nodes.extend(new_nodes)
        return node
    
    def revise(self, data: list[str]) -> list[TreeNode]:
        """Revise the tree with new feedback.
        
        Parses error messages to find the corresponding lemma/theorem that contains
        the error. Returns all matching nodes found.
        
        Args:
            data: List of error message strings from Lean verification
            
        Returns:
            List of TreeNode objects to revise
        """
        code = self.to_code()
        error_lemmas = set()
        # Parse error messages and find corresponding lemmas/theorems
        for error_msg in data:
            if not error_msg:
                continue
            
            # Extract line number from error message
            # Format: "{'line': 45, 'column': 40}: unsolved goals\n..."
            line_match = re.search(r"\{'line':\s*(\d+)", error_msg)
            if not line_match:
                continue
            error_line = int(line_match.group(1))
            lemma_name = fine_closed_theorem(code, error_line)
            if lemma_name is None:
                # Skip this error message if we can't find the corresponding lemma/theorem
                logger.warning(f"Could not find lemma/theorem for error at line {error_line}: {error_msg[:100]}")
                continue
            error_lemmas.add(lemma_name)
            
        nodes_to_revise = []
        for node in self.walk_leaves():
            if node.key in error_lemmas \
                    or "sorry" in node.payload.content or "admit" in node.payload.content:
                node.payload.content = remove_proof(node.payload.content)
                node.payload.has_sorry, node.payload.is_proved = True, False
                nodes_to_revise.append(node.key)
            else:
                node.payload.has_sorry, node.payload.is_proved = False, True
        
        if len(nodes_to_revise) < len(error_lemmas):
            logger.warning(
                f"nodes_to_revise ({len(nodes_to_revise)}) may not cover all error_lemmas ({len(error_lemmas)}): "
                f"nodes={nodes_to_revise}, errors={error_lemmas}"
            )
        
        return nodes_to_revise
    
    def check_target(self) -> bool:
        """Check if the target has 'sorry'.
        
        Returns:
            True if the target does not have 'sorry', False otherwise
            
        Raises:
            ValueError: If target is not set or target node is not found
        """
        target_key = self._get_target_key()
        if target_key is None:
            raise ValueError("Target is not set. Call set_target() first.")
        node = self.find_node(target_key)
        if node is None:
            raise ValueError(f"The target node '{target_key}' is not found in the tree")
        return node.payload.is_proved
    
    # ------------------------------------------------------------------
    # Convert the tree to code
    # ------------------------------------------------------------------
    def to_code(self, target_key: str | None = None) -> str:
        """Convert the tree structure back to a Lean code string.
        
        Reconstructs the code by combining environment nodes with proof nodes
        (leaf nodes). The proof nodes are inserted at the placeholder position
        in the environment.
        
        Args:
            target_key: Optional key to stop at when collecting proof nodes
            
        Returns:
            Complete Lean code string combining environment and proofs
        """
        code_nodes = self.env
        proof_nodes = []
        # Collect proof nodes (leaves) up to target if specified
        for proof_node in self.walk_leaves():
            proof_nodes.append(proof_node)
            if target_key is not None and proof_node.key == target_key:
                break
        # Create a set of proof node keys for quick lookup
        proof_node_keys = {node.key for node in proof_nodes}
        # Insert proof nodes at placeholder position
        code_nodes = code_nodes[:self.placeholder_idx] + proof_nodes + code_nodes[self.placeholder_idx + 1:]
        
        def _get_content(code_node: TreeNode) -> str:
            """Get content with @[reducible, simp] prefix for local def blocks."""
            content = code_node.payload.content
            # Add @[reducible, simp] attribute for local def blocks (proof nodes with type 'def')
            if code_node.key in proof_node_keys and code_node.payload.type == "def":
                # Check if it already has the attribute
                if not content.strip().startswith("@["):
                    content = "@[reducible, simp]\n" + content
            return content
        
        contents = [_get_content(code_node) for code_node in code_nodes]
        return "\n\n".join(contents)