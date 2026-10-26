#!/bin/sh
#
# Regenerate gradual_prog.ml and gradual_prog.mli from gradual_prog.v with
# the gradual fork of Rocq (branch `gradual` of gradual-rocq; GRADUAL.md).
# The generated files are committed, so building the unikernel does not
# need Rocq.
#
# Usage: ROCQ=/path/to/gradual-rocq/_build/install/default/bin/rocq ./extract.sh
#
set -eu
cd "$(dirname "$0")"
ROCQ="${ROCQ:-rocq}"
if ! "${ROCQ}" c -q -h >/dev/null 2>&1; then
    echo "error: ${ROCQ} not found; set ROCQ to the gradual fork's rocq" >&2
    exit 2
fi
"${ROCQ}" c -q gradual_prog.v
rm -f gradual_prog.vo gradual_prog.vos gradual_prog.vok gradual_prog.glob .gradual_prog.aux
echo "extracted gradual_prog.ml"
