(* Runs the cases of gradual_prog.v and compares each result with the one
   the Rocq kernel computes (the [Goal]s there): first casts at closed
   types, then casts at type parameters, whose runtime descriptions the
   extracted functions take as arguments. [unk] and [raise] at inductive
   types extracted as OCaml variants are values, as in the kernel. With --omega, runs Omega, which
   is well typed in gradual Rocq and never terminates. *)
open Gradual_prog

let omega =
  let doc = Cmdliner.Arg.info ~doc:"Run Omega (never terminates)." [ "omega" ] in
  Mirage_runtime.register_arg Cmdliner.Arg.(value & flag doc)

(* [unk] and [raise] at inductive types are values, as in the kernel: they
   are printed as such, and eliminating them raises. *)
let run f =
  match f () with
  | s -> s
  | exception Gradual_rt.Cast_error _ -> "raise"
  | exception Gradual_rt.Unknown_term _ -> "unk"

(* Printers that look at a value only after checking it is not [unk] or
   [raise] (matching on those is undefined in OCaml). *)
let data show v =
  if Gradual_rt.is_unknown v then "unk" else if Gradual_rt.is_error v then "raise" else show v

let rec nat v = data (fun v ->
    let rec succs k v =
      if Gradual_rt.is_unknown v || Gradual_rt.is_error v then
        let rec wrap k x = if k = 0 then x else if k = 1 then "S " ^ x else "S (" ^ wrap (k - 1) x ^ ")" in
        wrap k (nat v)
      else match v with O -> string_of_int k | S p -> succs (k + 1) p
    in
    succs 0 v) v

let list show v =
  let rec items v = data (fun v -> match v with
      | Nil -> ""
      | Cons (x, Nil) -> show x
      | Cons (x, l) -> show x ^ "; " ^ items l) v
  in
  "[" ^ items v ^ "]"

let ints = list nat
let bools = list string_of_bool
let rec tree v = data (fun (Node (x, f)) -> nat x ^ forest f) v
and forest v = data (function Fnil -> "" | Fcons (t, f) -> "(" ^ tree t ^ ")" ^ forest f) v

(* name, result, what the kernel computes *)
let cases = [
  "succ_dyn 41", (fun () -> nat (t_ok ())), "42";
  "succ_dyn true", (fun () -> nat (t_bad ())), "raise";
  "apply3 S", (fun () -> nat (t_app ())), "4";
  "apply3 negb", (fun () -> nat (t_app_bad ())), "raise";
  "[1; 2] : list nat", (fun () -> ints (t_list ())), "[1; 2]";
  "[1; true] : list nat", (fun () -> ints (t_list_bad ())), "[1; raise]";
  "length of [1; raise]", (fun () -> nat (t_list_bad_length ())), "2";
  "vhead (v3 : vec nat 3)", (fun () -> nat (t_vec ())), "1";
  "vhead (v3 : vec nat 2)", (fun () -> nat (vhead (S O) (t_vec_bad ()))), "raise";
  "rep : forall n, vec nat n", (fun () -> nat (t_dep ())), "2";
  "rep : forall n, vec nat (S n)", (fun () -> nat (t_dep_bad ())), "raise";
  "tree Dyn : tree nat", (fun () -> tree (t_tree ())), "1(2)";
  "tree with true : tree nat", (fun () -> tree (t_tree_bad ())), "1(raise)";
  "succ_dyn unk", (fun () -> nat (t_unk_dyn ())), "unk";
  "2 + unk", (fun () -> nat (t_unk_plus ())), "S (S unk)";
  "cast Type nat bool", (fun () -> nat (t_sort_bad ())), "raise";
]

(* casts at type parameters (bool is mapped to OCaml's bool, which cannot
   hold [raise]: a cast to it raises at once, where the kernel keeps
   [raise] inside data) *)
let poly_cases = [
  "roundtrip 41 : nat", (fun () -> nat (t_poly ())), "41";
  "roundtrip 41 : bool", (fun () -> string_of_bool (t_poly_bad ())), "raise";
  "of_dyn (to_dyn (dyns l)) : list nat", (fun () -> ints (t_poly_list ())), "[1; 2]";
  "dyns [1; 2] : list nat", (fun () -> ints (t_poly_rec ())), "[1; 2]";
  "dyns [1; 2] : list bool", (fun () -> bools (t_poly_rec_bad ())), "raise";
  "local fix at A : list bool", (fun () -> bools (t_poly_local ())), "[true]";
  "mutual fixpoints at A", (fun () -> ints (t_poly_mutual ())), "[1; 2; 3]";
  "poly_fun S : nat -> nat", (fun () -> nat (t_poly_fun ())), "2";
  "poly_fun negb : nat -> nat", (fun () -> nat (t_poly_fun_bad ())), "raise";
]

(* Logs each case, then a summary line that run-matrix.sh looks for. *)
let check what cases =
  let ok =
    List.fold_left (fun ok (name, f, expected) ->
        let got = run f in
        Logs.info (fun f -> f "gradual: %s = %s%s" name got
                      (if got = expected then "" else " (kernel: " ^ expected ^ ")"));
        ok + if got = expected then 1 else 0) 0 cases
  in
  let n = List.length cases in
  if ok = n then Logs.info (fun f -> f "gradual: all %d %s agree with the kernel" n what)
  else Logs.err (fun f -> f "gradual: %d of %d %s disagree with the kernel" (n - ok) n what)

let start () =
  if omega () then begin
    Logs.info (fun f -> f "gradual: running Omega");
    ignore (t_omega ())
  end;
  check "cases" cases;
  check "polymorphic cases" poly_cases;
  Lwt.return_unit
