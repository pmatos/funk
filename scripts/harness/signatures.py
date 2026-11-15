"""The signatures of the functions of a canonical module, read from its text
line by line: the parameter and result types of each function of its own
table, by its symbol as text writes it (#13)."""


def result_types(text: str) -> dict[str, list[str]]:
    """The result types of each function of a canonical module, by its
    symbol as text writes it. A canonical module writes each function's
    signature on one line: `func SYMBOL(PARAMS) -> TYPES {`."""
    found = {}
    for line in text.split("\n"):
        if not line.startswith("func @") or not line.endswith(" {"):
            continue
        rest = line[len("func ") : -len(" {")]
        end = symbol_end(rest)
        close = closing_paren(rest, end)
        if close is None:
            continue
        tail = rest[close + 1 :]
        found[rest[:end]] = split_types(tail[4:]) if tail.startswith(" -> ") else []
    return found


def param_types(text: str) -> dict[str, list[str]]:
    """The parameter types of each function of a canonical module, by its
    symbol as text writes it, read from the signature line as
    `result_types` reads its results: `%NAME: TYPE` for each parameter."""
    found = {}
    for line in text.split("\n"):
        if not line.startswith("func @") or not line.endswith(" {"):
            continue
        rest = line[len("func ") : -len(" {")]
        end = symbol_end(rest)
        close = closing_paren(rest, end)
        if close is None:
            continue
        inside = rest[end + 1 : close]
        params = split_types(inside) if inside else []
        found[rest[:end]] = [p.partition(": ")[2] for p in params]
    return found


def symbol_end(s: str) -> int:
    """The index just past the symbol at the start of `s`."""
    if not s.startswith('@"'):
        return s.find("(") if "(" in s else len(s)
    i = 2
    while i < len(s) and s[i] != '"':
        i += 2 if s[i] == "\\" else 1
    return i + 1


def closing_paren(s: str, start: int) -> int | None:
    """The index of the `)` that closes the `(` at `start`."""
    if s[start : start + 1] != "(":
        return None
    depth = 0
    for i in range(start, len(s)):
        depth += {"(": 1, ")": -1}.get(s[i], 0)
        if depth == 0:
            return i
    return None


def split_types(s: str) -> list[str]:
    """Splits `T1, T2` at the commas outside parentheses."""
    out, depth, start = [], 0, 0
    for i, ch in enumerate(s):
        depth += {"(": 1, ")": -1}.get(ch, 0)
        if ch == "," and depth == 0:
            out.append(s[start:i].strip())
            start = i + 1
    out.append(s[start:].strip())
    return out
