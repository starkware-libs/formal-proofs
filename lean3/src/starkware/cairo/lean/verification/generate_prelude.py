from typing import List, Tuple

# Comment inserted at the end of the prelude to indicate the end of the prelude.
prelude_end_comment = "-- End of automatically generated prelude."


def skip_initial_comment(lines: List[str]) -> int:
    """
    Skips to the first line following the initial Lean comment (between /- -/).
    The index of the first line following the comment is returned.
    """
    for start, line in enumerate(lines):
        if line.lstrip().startswith("/-"):
            break
        elif line != "" and not line.isspace():
            # Nothing except white space allowed before initial comment.
            return 0

    if start == len(lines):
        return 0

    for end in range(start + 1, len(lines)):
        if lines[end].rstrip().endswith("-/"):
            return end + 1

    return 0


def skip_imports(lines: List[str], pos: int) -> int:
    """
    Skip all 'import' lines at the beginning of the file.
    Returns the position after the last import.
    """
    for n in range(pos, len(lines)):
        if lines[n] != "" and not lines[n].isspace() and not lines[n].lstrip().startswith("import"):
            return n

    return len(lines)


def find_prelude_end(lines: List[str]) -> int:
    """
    Returns the number of the first line after the prelude (this may be beyond
    the end of the list). The end of the prelude is identified by a special comment
    block. If this cannot be found, the function returns the position beyond the initial
    comment and all imports.
    """
    for line_num, line in enumerate(lines):
        if line.strip() == prelude_end_comment.strip():
            return line_num + 1
    # end of prelude comment not found, skip initial comment and imports
    return skip_imports(lines, skip_initial_comment(lines))


def stripped_block(block: List[str]) -> List[str]:
    """
    Remove empty lines from the block
    """
    return list(filter(lambda x: x != "" and not x.isspace(), block))


def line_block_at(block: List[str], lines: List[str], pos: int) -> bool:
    # Compare without (trailing) empty lines.
    block = stripped_block(block)

    if len(lines) - pos < len(block):
        return False
    for i, b_line in enumerate(block):
        if b_line.strip() != lines[pos + i].strip():
            return False
    return True


def insert_prelude_blocks_at(
    prelude: List[List[str]], lines: List[str], from_block: int, to_block: int, insert_pos: int
) -> Tuple[List[str], int]:
    """
    Inserts prelude blocks from from_block to to_block (not including) into
    the list of lines at position insert_pos. Returns the new list and the number of
    lines added.
    """
    if from_block >= to_block:
        return (lines, 0)

    insert = [line for block in prelude[from_block:to_block] for line in block]
    return (lines[:insert_pos] + insert + lines[insert_pos:], len(insert))


def insert_prelude_blocks(prelude: List[List[str]], lines: List[str]) -> List[str]:
    """
    Inserts the prelude into a list of lines (of a Lean file). Each block (list of line)
    in the prelude is added to the file's list of lines if it does not already appear
    in the list. The block is added as close to the beginning of the list as possible,
    but not before the position of the previous prelude block.
    Returns the new list of lines.
    """
    search_pos = 0
    insert_pos = search_pos
    block_to_insert = 0

    while search_pos < len(lines) and block_to_insert < len(prelude):
        for block in range(block_to_insert, len(prelude)):
            if line_block_at(prelude[block], lines, search_pos):
                lines, added = insert_prelude_blocks_at(
                    prelude, lines, block_to_insert, block, insert_pos
                )
                search_pos += added + len(stripped_block(prelude[block]))
                insert_pos = search_pos
                block_to_insert = block + 1
                break
        else:
            search_pos += 1

    lines, _ = insert_prelude_blocks_at(prelude, lines, block_to_insert, len(prelude), insert_pos)
    return lines


def insert_lean_prelude(prelude: List[List[str]], lines: List[str]) -> List[str]:
    """
    Inserts the prelude into a list of lines (of a file). The Lean import blocks
    (which are assumed to be the first blocks) are added in the existing import
    section (all lines following the initial comment which are a Lean import or empty).
    The remaining prelude blocks are added after the import section. It is therefore
    important not to mix import and other code in the same prelude block.
    """
    after_comment = skip_initial_comment(lines)
    after_imports = skip_imports(lines, after_comment)

    # The import section consists of an initial comment and all imports.
    import_blocks = list(filter(lambda x: x and x[0].lstrip().startswith("import"), prelude))
    import_lines = insert_prelude_blocks(import_blocks, lines[after_comment:after_imports])
    non_import_blocks = list(
        filter(lambda x: x and not x[0].lstrip().startswith("import"), prelude)
    )
    # Add the closing comment.
    non_import_blocks.append(["", prelude_end_comment, ""])
    non_import_lines = insert_prelude_blocks(non_import_blocks, lines[after_imports:])

    return lines[:after_comment] + import_lines + non_import_lines


def insert_additional_imports(imports: List[str], lines: List[str]) -> List[str]:
    """
    Inserts additional imports to the list of lines of the spec file. The imports are
    added directly after the existing imports (if any) and after the initial comment
    if there are no imports.
    """
    after_comment = skip_initial_comment(lines)
    after_imports = skip_imports(lines, after_comment)

    for import_line in imports:
        if import_line in lines[after_comment:after_imports]:
            continue
        lines = lines[:after_imports] + [import_line] + lines[after_imports:]
        after_imports += 1

    return lines


def insert_open_import_namespaces(import_files: List[str], lines: List[str]) -> List[str]:
    """
    Inserts open <namespace> lines to the list of lines of the spec file. This is
    for the namespaces of the given import files. The open <namespace> lines are
    added directly after the imports. Existing 'open' lines are not added.
    """
    after_imports = skip_imports(lines, skip_initial_comment(lines))

    # Add an extra empty line between the imports and the 'open <namespace> lines.
    if after_imports == 0 or (
        len(lines[after_imports - 1]) > 0 and not lines[after_imports - 1].isspace()
    ):
        lines = lines[:after_imports] + [""] + lines[after_imports:]
        after_imports += 1

    for import_file in import_files:
        open_line = "open " + import_file
        if open_line in lines[after_imports:]:
            continue
        lines = lines[:after_imports] + [open_line] + lines[after_imports:]
        after_imports += 1

    return lines
