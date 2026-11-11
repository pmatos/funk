#!/usr/bin/env bash
# Checks fir-ref at depth (#47). check-fir-ref.sh test calls it with the
# fir-ref that it builds: scripts/check-fir-ref-deep.sh FIR_REF. On a 256
# KiB stack, fir-ref fmt and validate give texts nested a million levels
# deep in attributes, in functions, in modules and in regions, and a block
# of a million ops, their verdicts, never an abort, and validate accepts
# valid modules nested a million levels deep and checks an item of a
# dialect's kind whose attribute is nested a million levels deep.
set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "Usage: $0 FIR_REF" >&2
    exit 2
fi
fir_ref=$1

repo_root=$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)
cd "$repo_root"

# fir-ref runs code from this repository; keep CI tokens away.
unset GH_TOKEN GITHUB_TOKEN

status=0
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# fir has no nesting limit (ADR-2026-10-30-1549). The spec's readers,
# decoder and printer take 128 to 384 MB of stack on a text nested a
# million levels deep, and 64 to 256 MB on a block of a million ops.
# fir-ref takes no stack per level or per op, so on a 256 KiB stack it
# gives each text below its verdict, never an abort. The nested texts do
# not parse: an attribute applied a million levels deep, functions nested
# in functions, modules nested in modules and followed by an item of an
# unknown kind, and regions whose innermost op reads an undefined value,
# since regions that parse cannot be printed at that depth. The block of a
# million ops, the one that check-fir-ref.sh reprints, is canonical and
# valid.
ending='}\n\nlocs {\n  @0 = unknown\n}\n'
awk -v end="$ending" 'BEGIN {
    printf "func @f() {\n^e:\n  ret "
    for (i = 0; i < 1000000; i++) printf "h("
    printf "x"
    for (i = 0; i < 1000000; i++) printf ")"
    printf " @0\n%s", end
}' >"$tmp/deep-attrs.fir"
awk -v end="$ending" 'BEGIN {
    printf "toy.cell @c() "
    for (i = 0; i < 1000000; i++) printf "h("
    printf "x"
    for (i = 0; i < 1000000; i++) printf ")"
    printf " {\n%s", end
}' >"$tmp/deep-item-attrs.fir"
awk -v end="$ending" 'BEGIN {
    for (i = 0; i < 1000000; i++) printf "func @a() {\n"
    for (i = 1; i < 1000000; i++) printf "}\n"
    printf "%s", end
}' >"$tmp/deep-items.fir"
awk -v end="$ending" 'BEGIN {
    for (i = 0; i < 1000000; i++) printf "module @a() {\n"
    for (i = 0; i < 1000000; i++) printf "}\n"
    printf "bad @b() {\n%s", end
}' >"$tmp/deep-modules.fir"
awk -v end="$ending" 'BEGIN {
    for (i = 0; i < 1000000; i++) printf "module @a() {\n"
    printf "func @a() {\n^e:\nret @0\n"
    for (i = 0; i < 1000000; i++) printf "}\n"
    printf "%s", end
}' >"$tmp/valid-modules.fir"
awk -v end="$ending" 'BEGIN {
    printf "func @f() {\n^e:\n"
    for (i = 0; i < 1000000; i++) printf "br {\n^b:\n"
    printf "ret %%x @0\n"
    for (i = 0; i < 1000000; i++) printf "} @0\n"
    printf "%s", end
}' >"$tmp/deep-regions.fir"
awk -v end="$ending" 'BEGIN {
    printf "func @f() {\n^e:\n"
    for (i = 0; i < 1000000; i++) printf "  %%c%d: i32 = const %d @0\n", i, i
    printf "  ret @0\n%s", end
}' >"$tmp/ops.fir"
# deep [--validate-only] [--invalid DIAGNOSTICS] NAME WHAT [LINE COLUMN
# MESSAGE]: on a 256 KiB stack, fir-ref fmt --check and validate give
# $tmp/NAME.fir, WHAT, the parse error at LINE and COLUMN with MESSAGE, or,
# without one, accept it, and print exactly that verdict. With
# --validate-only, only validate reads it: a text whose canonical form is
# too large to print. With --invalid, the text is canonical and validate
# rejects it with DIAGNOSTICS, as JSON.
deep() {
    local cmds=("fmt --check" validate) invalid=''
    if [[ $1 == --validate-only ]]; then
        cmds=(validate)
        shift
    fi
    if [[ $1 == --invalid ]]; then
        invalid=$2
        shift 2
    fi
    local file=$tmp/$1.fir what=$2 verdict=accepted diags='' want_rc=0 fail=0
    local cmd rc out err want_out want_err cmd_rc
    shift 2
    if [[ -n $invalid ]]; then
        verdict=validation-error diags=$invalid
    fi
    if [[ $# -gt 0 ]]; then
        verdict=parse-error want_rc=1
        printf -v diags '{"kind":"parse-error","message":"%s","line":%s,"column":%s}' \
            "$3" "$1" "$2"
    fi
    for cmd in "${cmds[@]}"; do
        want_out='' want_err='' cmd_rc=$want_rc
        if [[ $cmd == validate && -n $invalid ]]; then
            cmd_rc=1
        fi
        if [[ $cmd == validate ]]; then
            printf -v want_out '{"file":"%s","verdict":"%s","diagnostics":[%s]}' \
                "$file" "$verdict" "$diags"
        elif [[ $# -gt 0 ]]; then
            want_err="$file:$1:$2: parse error: $3"
        fi
        rc=0
        # shellcheck disable=SC2086 # CMD is a command and its option.
        out=$(ulimit -c 0; LEAN_STACK_SIZE_KB=256 exec "$fir_ref" $cmd "$file" \
            2>"$tmp/deep.err") || rc=$?
        err=$(<"$tmp/deep.err")
        if [[ $rc -ne $cmd_rc || $out != "$want_out" || $err != "$want_err" ]]; then
            echo "On a 256 KiB stack, fir-ref $cmd on $what exits with $rc," \
                "prints '$out' and '$err' on standard error; expected" \
                "$cmd_rc, '$want_out' and '$want_err'" >&2
            fail=1
        fi
    done
    return "$fail"
}
attr_error="op ret does not decode: the dialect has no op with this name and these"
attr_error+=" attributes, operand types and result types"
deep deep-attrs "an attribute applied a million levels deep" 3 3 "$attr_error" || status=1
deep deep-items "functions nested a million levels deep" 2 1 \
    "a func's body holds blocks, not items" || status=1
deep deep-modules "modules nested a million levels deep" 2000001 1 \
    "unknown item kind bad: the kinds are func, module and the words of dialects" || status=1
deep deep-regions "regions nested a million levels deep" 2000003 5 \
    "value %x is not defined in @f" || status=1
deep ops "a block of a million ops" || status=1
# An item of a dialect's kind keeps its attributes at any depth, and
# validate walks them by loops (ADR-2026-11-10-2224). The core registers no
# kind and the module names no dialect, so validate rejects the item.
item_diag() {
    printf '{"kind":"validation-error","message":"%s","func":"c","block":null,"op":null,"loc":null}' \
        "$1"
}
unregistered=$(item_diag 'no dialect registers the kind of item \"toy.cell\"')
outside=$(item_diag \
    "the item writes a word of the dialect toy, which the module's dialect set does not name")
deep --invalid "$unregistered,$outside" deep-item-attrs \
    "an item's attribute applied a million levels deep" || status=1
# Valid modules nested a million levels deep, the innermost holding a
# function, each a symbol table of its own (ADR-2026-11-10-1510). Their
# canonical form indents each level two spaces deeper, so only validate
# reads them.
deep --validate-only valid-modules "valid modules nested a million levels deep" || status=1
exit "$status"
