#!/bin/sh
# Gate for the Lean formalisation of the direct-route proof.
#
# It passes only if
#   1. the trusted files of the Lean project are identical to a fixed reference, and
#   2. `lake comparator` accepts: every theorem named in a list comparator*.json is proved in the solution
#      module with the statement of the challenge module, with no axiom beyond the permitted ones (so no
#      sorry, no axiom, no native_decide), and the kernel accepts the whole solution.
#
# Usage:  scripts/allN/lean_gate.sh REFERENCE [--local] [--final]
#   REFERENCE is one of
#     - a file of SHA-256 digests (the output format of `shasum -a 256`), with paths relative to the
#       project directory; the trusted files are the files that it lists. This is the form for a copy of
#       the repository without the history of the development: lean/direct-route/TRUSTED.sha256.
#     - a git commit or tag; the trusted files must be identical to their state there.
#   --local   no sandbox (macOS has no bwrap). Good for the working loop; not the final verdict.
#   --final   also run the external checkers bundled with Lean (--paranoid).
# The project directory is lean/direct-route, or $LEAN_PROJECT (relative to the repository root).
set -eu

[ $# -ge 1 ] || { echo "usage: $0 REFERENCE [--local] [--final]" >&2; exit 2; }
FREEZE=$1; shift
ARGS=""
for a in "$@"; do
  case "$a" in
    --local) ARGS="$ARGS --inadvisably-no-sandbox" ;;
    --final) ARGS="$ARGS --paranoid" ;;
    *) echo "unknown option $a" >&2; exit 2 ;;
  esac
done

ROOT=$(git rev-parse --show-toplevel 2>/dev/null || (cd "$(dirname "$0")/../.." && pwd))
P=${LEAN_PROJECT:-lean/direct-route}

# 1. The trusted files: the statements, the lists of theorems and permitted axioms, and everything that
#    decides what is built and against which library.
if [ -f "$FREEZE" ]; then
  # a file of digests
  MANIFEST=$(cd "$(dirname "$FREEZE")" && pwd)/$(basename "$FREEZE")
  cd "$ROOT/$P"
  for f in Challenge.lean comparator.json lakefile.toml lake-manifest.json lean-toolchain; do
    grep -q "  $f\$" "$MANIFEST" || { echo "GATE FAIL: $f is not listed in $MANIFEST"; exit 1; }
  done
  if command -v sha256sum >/dev/null 2>&1; then SUM="sha256sum"; else SUM="shasum -a 256"; fi
  $SUM -c "$MANIFEST" >/dev/null 2>&1 \
    || { echo "GATE FAIL: a trusted file differs from $MANIFEST"; $SUM -c "$MANIFEST" 2>&1 | grep -v ': OK$' || true; exit 1; }
  CONFIGS=$(awk '{print $2}' "$MANIFEST" | grep -E '^comparator[A-Z]?\.json$' | sort | tr '\n' ' ')
  for c in $CONFIGS; do
    m=$(sed -n 's/.*"challenge_module": *"\([A-Za-z]*\)".*/\1/p' "$c")
    grep -q "  $m.lean\$" "$MANIFEST" || { echo "GATE FAIL: $m.lean (statements of $c) is not listed in $MANIFEST"; exit 1; }
  done
  cd "$ROOT"
else
  cd "$ROOT"
  CONFIGS="comparator.json"
  TRUSTED="Challenge.lean comparator.json lakefile.toml lake-manifest.json lean-toolchain"
  # A second pair ChallengeA.lean, comparatorA.json (Lemma A) and a third pair ChallengeB.lean,
  # comparatorB.json (the statements in the form of the paper) are checked and judged if the reference has them.
  for x in A B; do
    if git cat-file -e "$FREEZE:$P/comparator$x.json" 2>/dev/null; then
      CONFIGS="$CONFIGS comparator$x.json"
      TRUSTED="$TRUSTED Challenge$x.lean comparator$x.json"
    fi
  done
  for f in $TRUSTED; do
    git cat-file -e "$FREEZE:$P/$f" 2>/dev/null || { echo "GATE FAIL: $P/$f is not in commit $FREEZE"; exit 1; }
    git diff --quiet "$FREEZE" -- "$P/$f" || { echo "GATE FAIL: $P/$f differs from commit $FREEZE"; exit 1; }
  done
fi
# No directory or second lakefile may shadow a trusted file.
for d in Challenge ChallengeA ChallengeB; do
  [ ! -e "$ROOT/$P/$d" ] || { echo "GATE FAIL: $P/$d shadows a trusted file"; exit 1; }
done
[ ! -e "$ROOT/$P/lakefile.lean" ] || { echo "GATE FAIL: $P/lakefile.lean shadows lakefile.toml"; exit 1; }

# 2. The comparator, once for each list of theorems.
cd "$ROOT/$P"
for c in $CONFIGS; do
  # shellcheck disable=SC2086
  if lake comparator --config "$c" $ARGS; then
    echo "accepted: $c"
  else
    rc=$?
    echo "GATE FAIL: lake comparator --config $c exit $rc"
    exit 1
  fi
done
echo "GATE PASS (reference $FREEZE; $CONFIGS;$ARGS)"
