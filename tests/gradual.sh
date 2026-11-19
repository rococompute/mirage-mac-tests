#!/bin/sh
# Verify extraction and run the existing unikernel case table on the host.
# Requires the gradual Rocq fork, ocamlfind, cmdliner, logs.fmt and lwt.
set -eu
root="$(cd "$(dirname "$0")/.." && pwd)"
"${root}/unikernels/gradual/extract.sh" --check
work="$(mktemp -d "${TMPDIR:-/tmp}/gradual-host.XXXXXX")"
trap 'rm -rf "${work}"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
cp "${root}"/unikernels/gradual/gradual_prog.ml "${root}"/unikernels/gradual/gradual_prog.mli \
    "${root}"/unikernels/gradual/uint63.ml "${root}"/unikernels/gradual/unikernel.ml "${work}/"
# Only argument registration needs a host adapter; the complete case table,
# exception handling, printers and summary logging come from the unikernel.
cat > "${work}/mirage_runtime.ml" <<'ML'
let register_arg (_ : bool Cmdliner.Term.t) =
  fun () -> Array.exists (String.equal "--omega") Sys.argv
ML
cat > "${work}/main.ml" <<'ML'
let () =
  Logs.set_level (Some Logs.Info);
  Logs.set_reporter (Logs_fmt.reporter ~dst:Format.std_formatter ());
  ignore (Unikernel.start ())
ML
(
    cd "${work}"
    ocamlfind ocamlopt -w -20 -package cmdliner,logs.fmt,lwt -linkpkg \
        uint63.ml gradual_prog.mli gradual_prog.ml mirage_runtime.ml unikernel.ml main.ml -o cases
    ./cases > cases.log 2>&1
    cat cases.log
    grep -q 'gradual: all 16 cases agree with the kernel' cases.log
    grep -q 'gradual: all 9 polymorphic cases agree with the kernel' cases.log
    if grep -q 'disagree with the kernel' cases.log; then exit 1; fi
    status=0
    perl "${root}/run-with-timeout.pl" 0.2 ./cases --omega > omega.log 2>&1 || status=$?
    [ "${status}" = 124 ]
    grep -q 'gradual: running Omega' omega.log
)
echo 'extraction current; 25 case expectations and nonterminating Omega passed'
