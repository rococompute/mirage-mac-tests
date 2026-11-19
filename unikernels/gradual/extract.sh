#!/bin/sh
#
# Regenerate gradual_prog.ml and gradual_prog.mli from gradual_prog.v with
# the gradual fork of Rocq (branch `gradual` of gradual-rocq; GRADUAL.md).
# The generated files are committed, so building the unikernel does not
# need Rocq.
#
# Usage: ROCQ=/path/to/gradual-rocq/_build/install/default/bin/rocq ./extract.sh [--check]
#
set -eu
cd "$(dirname "$0")"
ROCQ="${ROCQ:-rocq}"
if ! command -v "${ROCQ}" >/dev/null 2>&1; then
    echo "error: ${ROCQ} not found; set ROCQ to the gradual fork's rocq" >&2
    exit 2
fi
mode="${1:-}"
case "${mode}" in ''|--check) ;; *) echo "usage: $0 [--check]" >&2; exit 2 ;; esac
[ "$#" -le 1 ] || { echo "usage: $0 [--check]" >&2; exit 2; }
work="$(mktemp -d "${TMPDIR:-/tmp}/gradual-extract.XXXXXX")"
trap 'rm -rf "${work}"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
cp gradual_prog.v "${work}/"
# Resolve a relative executable path before changing directory.
ROCQ="$(command -v "${ROCQ}")"
case "${ROCQ}" in /*) ;; *) ROCQ="$(pwd)/${ROCQ}" ;; esac
(cd "${work}" && "${ROCQ}" c -q gradual_prog.v)
for file in gradual_prog.ml gradual_prog.mli; do
    if [ "${mode}" = --check ]; then
        diff -u "${file}" "${work}/${file}"
    else
        cp "${work}/${file}" "${file}"
    fi
done
echo "extraction ${mode:-updated}"
