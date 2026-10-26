(* Runs code extracted from gradual Rocq (gradual_prog.v), whose casts are
   checked at run time; see run-matrix.sh, cases "gradual" and
   "gradual-omega". *)
open Mirage

let main = main "Unikernel" job
let () = register "gradual" [ main ]
