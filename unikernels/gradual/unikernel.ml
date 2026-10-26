(* Runs the cases of gradual_prog.v and compares each result with the one
   the Rocq kernel computes (the [Goal]s there). With --omega, runs Omega,
   which is well typed in gradual Rocq and never terminates. *)
open Gradual_prog

let omega =
  let doc = Cmdliner.Arg.info ~doc:"Run Omega (never terminates)." [ "omega" ] in
  Mirage_runtime.register_arg Cmdliner.Arg.(value & flag doc)

let run f =
  match f () with
  | s -> s
  | exception Gradual_rt.Cast_error _ -> "raise"
  | exception Gradual_rt.Unknown_term _ -> "unk"

let ints l = "[" ^ String.concat "; " (List.map string_of_int l) ^ "]"
let rec tree (Node (x, f)) = string_of_int x ^ forest f
and forest = function Fnil -> "" | Fcons (t, f) -> "(" ^ tree t ^ ")" ^ forest f

(* name, result, what the kernel computes *)
let cases = [
  "succ_dyn 41", (fun () -> string_of_int (t_ok ())), "42";
  "succ_dyn true", (fun () -> string_of_int (t_bad ())), "raise";
  "apply3 S", (fun () -> string_of_int (t_app ())), "4";
  "apply3 negb", (fun () -> string_of_int (t_app_bad ())), "raise";
  "[1; 2] : list nat", (fun () -> ints (t_list ())), "[1; 2]";
  "[1; true] : list nat", (fun () -> ints (t_list_bad ())), "raise";
  "vhead (v3 : vec nat 3)", (fun () -> string_of_int (t_vec ())), "1";
  "vhead (v3 : vec nat 2)", (fun () -> string_of_int (vhead 1 (t_vec_bad ()))), "raise";
  "rep : forall n, vec nat n", (fun () -> string_of_int (t_dep ())), "2";
  "rep : forall n, vec nat (S n)", (fun () -> string_of_int (t_dep_bad ())), "raise";
  "tree Dyn : tree nat", (fun () -> tree (t_tree ())), "1(2)";
  "succ_dyn unk", (fun () -> string_of_int (t_unk_dyn ())), "unk";
  "cast Type nat bool", (fun () -> string_of_int (t_sort_bad ())), "raise";
]

let start () =
  if omega () then begin
    Logs.info (fun f -> f "gradual: running Omega");
    ignore (t_omega ())
  end;
  let ok =
    List.fold_left (fun ok (name, f, expected) ->
        let got = run f in
        Logs.info (fun f -> f "gradual: %s = %s%s" name got
                      (if got = expected then "" else " (kernel: " ^ expected ^ ")"));
        ok + if got = expected then 1 else 0) 0 cases
  in
  let n = List.length cases in
  if ok = n then Logs.info (fun f -> f "gradual: all %d cases agree with the kernel" n)
  else Logs.err (fun f -> f "gradual: %d of %d cases disagree with the kernel" (n - ok) n);
  Lwt.return_unit
