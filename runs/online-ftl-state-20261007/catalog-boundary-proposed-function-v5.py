def compact_statement_equations(lines: list[str], start: int) -> str:
    parts: list[str] = []
    delimiter_depth = 0
    block_comment_depth = 0
    in_string = False
    initial_match = DECL_RE.match(lines[start])
    is_definition = bool(initial_match and initial_match.group("kind") == "def")
    equation_style = False
    for raw in lines[start : min(len(lines), start + 90)]:
        stripped = raw.strip()
        if not stripped:
            continue
        if equation_style and delimiter_depth == 0 and not block_comment_depth and not in_string:
            if DECL_RE.match(raw) or END_RE.match(raw) or NAMESPACE_RE.match(raw) or SECTION_RE.match(raw) or stripped.startswith("/--"):
                break
        if is_definition and delimiter_depth == 0 and not block_comment_depth and not in_string and stripped.startswith("| "):
            equation_style = True
        compact = re.sub(r"\s+", " ", stripped)
        is_result_let = stripped.startswith("let ")
        assignment_index: int | None = None
        index = 0
        while index < len(raw):
            if block_comment_depth:
                if raw.startswith("/-", index):
                    block_comment_depth += 1
                    index += 2
                    continue
                if raw.startswith("-/", index):
                    block_comment_depth -= 1
                    index += 2
                    continue
                index += 1
                continue
            if in_string:
                if raw[index] == '"' and (index == 0 or raw[index - 1] != "\\"):
                    in_string = False
                index += 1
                continue
            if raw.startswith("--", index):
                break
            if raw.startswith("/-", index):
                block_comment_depth += 1
                index += 2
                continue
            char = raw[index]
            if char == '"':
                in_string = True
            elif char in "([{":
                delimiter_depth += 1
            elif char in ")]}":
                delimiter_depth = max(0, delimiter_depth - 1)
            elif raw.startswith(":=", index) and delimiter_depth == 0 and not is_result_let and not equation_style:
                assignment_index = index
                break
            index += 1
        if assignment_index is not None:
            before = re.sub(r"\s+", " ", raw[:assignment_index].strip()).rstrip()
            if before:
                parts.append(before)
            break
        parts.append(compact)
        if stripped == "where" or stripped.endswith(" where"):
            break
        if sum(len(part) for part in parts) > 8000:
            break
    return " ".join(parts)[:8000]
