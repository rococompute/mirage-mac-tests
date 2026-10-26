(* Prints the RNG's entropy sources and generates a key; see run-matrix.sh,
   case "entropy". Adapted from mirage-crypto's mirage/ test unikernel. *)
open Mirage

let main =
  let packages =
    [ package "mirage-crypto-rng"; package "mirage-crypto-pk";
      package "mirage-crypto"; package ~min:"0.8.7" "fmt" ]
  in
  main ~packages "Unikernel" job

let () = register "entropy" [ main ]
