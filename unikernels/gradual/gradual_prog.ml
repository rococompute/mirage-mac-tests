
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Gradual_rt = struct
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Runtime support for casts in OCaml code extracted from gradual Rocq
   (GCIC^G, see GRADUAL.md). Extraction prints this file as a module
   [Gradual_rt] at the top of every extracted file that contains casts.

   Extraction erases types, so every cast [cast A B t] is extracted with
   runtime descriptions of [A] and [B]. A value of the unknown type [?] is
   a [dyn]: the value together with the description of the type it was
   injected from. The rules are the ones of the kernel (kernel/gradual.ml).

   This file must only depend on the OCaml standard library, so that the
   extracted code also builds for MirageOS unikernels. *)

exception Cast_error of string
(** The error [err_A] was reached: a cast failed at run time. *)

exception Unknown_term of string
(** The unknown term [?_A] at an inductive type was evaluated. Extracted
    code is call-by-value and cannot represent [?_A] as a value of [A], so
    this is raised instead. *)

type ty =
  | Unknown
  | Err
  | Erased  (* propositions and their proofs: nothing to check *)
  | Sort of int  (* 0 = Prop, 1 = Set, 2 = Type *)
  | Pi of ty * (Obj.t -> ty)
  | Ind of ind

and ind = {
  name : string;
  args : arg array;  (* parameters, then indices *)
}

and arg =
  | Ty of ty
  | Val of Obj.t
  | Unk
  | Error

type dyn = { dty : ty; dv : Obj.t }

(* For each inductive type, by name, the function [f] such that [f src tgt v]
   rebuilds [v : src] at [tgt], two instances of the type. Extraction
   generates them and passes them to [cast_with]. *)
let casts : (string, ind -> ind -> Obj.t -> Obj.t) Hashtbl.t = Hashtbl.create 17

(* Same representation as the [__] of extracted code. *)
let dummy = let rec f _ = Obj.repr f in Obj.repr f

let rec to_string = function
  | Unknown -> "?"
  | Err -> "err"
  | Erased -> "_"
  | Sort 0 -> "Prop"
  | Sort 1 -> "Set"
  | Sort _ -> "Type"
  | Pi (a, _) -> to_string a ^ " -> _"
  | Ind { name; args; _ } ->
    if Array.length args = 0 then name
    else
      "(" ^ String.concat " " (name :: Array.to_list (Array.map arg_to_string args)) ^ ")"

and arg_to_string = function
  | Ty t -> to_string t
  | Val _ -> "_"
  | Unk -> "?"
  | Error -> "err"

let fail a b =
  raise (Cast_error ("cannot cast from " ^ to_string a ^ " to " ^ to_string b))

let same_value (a : Obj.t) (b : Obj.t) =
  a == b || (try compare a b = 0 with Invalid_argument _ -> false)

(* Syntactic equality of descriptions; functions are never equal. *)
let rec equal a b =
  a == b ||
  match a, b with
  | Unknown, Unknown | Err, Err | Erased, Erased -> true
  | Sort s1, Sort s2 -> s1 = s2
  | Ind i1, Ind i2 ->
    String.equal i1.name i2.name
    && Array.length i1.args = Array.length i2.args
    && Array.for_all2 equal_arg i1.args i2.args
  | _ -> false

and equal_arg a b = match a, b with
  | Ty a, Ty b -> equal a b
  | Val a, Val b -> same_value a b
  | Unk, Unk | Error, Error -> true
  | _ -> false

let rec unknown_term ty : Obj.t = match ty with
  | Unknown -> Obj.repr { dty = Unknown; dv = dummy }
  | Erased | Sort _ -> dummy
  | Pi (_, b) -> Obj.repr (fun x -> unknown_term (b x))
  | Ind i -> raise (Unknown_term i.name)
  | Err -> raise (Cast_error "unknown term of the error type")

let rec err_term ty : Obj.t = match ty with
  | Unknown -> Obj.repr { dty = Err; dv = dummy }
  | Erased | Sort _ -> dummy
  | Pi (_, b) -> Obj.repr (fun x -> err_term (b x))
  | Ind _ | Err -> raise (Cast_error ("error at type " ^ to_string ty))

let rec cast a b (v : Obj.t) : Obj.t =
  if equal a b then v
  else match a, b with
    | Err, _ | _, Err -> fail a b
    | Erased, Erased -> v
    | Unknown, Unknown -> v
    | Unknown, _ ->
      let d : dyn = Obj.obj v in
      begin match d.dty with
        | Unknown -> unknown_term b
        | Err -> err_term b
        | a -> cast a b d.dv
      end
    | _, Unknown -> Obj.repr { dty = a; dv = v }
    | Pi (a1, b1), Pi (a2, b2) ->
      let f : Obj.t -> Obj.t = Obj.obj v in
      Obj.repr (fun x ->
          let x' = cast a2 a1 x in
          let b1 = b1 x' and b2 = b2 x in
          (* A tail call when there is nothing to cast, so that loops through
             casts (like Omega) run in constant stack. *)
          if equal b1 b2 then f x' else cast b1 b2 (f x'))
    | Sort s1, Sort s2 -> if s1 <= s2 then v else fail a b
    | Ind i1, Ind i2 when String.equal i1.name i2.name ->
      begin match Hashtbl.find_opt casts i1.name with
        | Some f -> f i1 i2 v
        | None -> raise (Cast_error ("no cast function for " ^ i1.name))
      end
    | _ -> fail a b

let cast_with fs a b v =
  List.iter (fun (name, f) ->
      if not (Hashtbl.mem casts name) then Hashtbl.add casts name f) fs;
  cast a b v

(* The indices computed for a rebuilt constructor must be compatible with
   the indices of the target type ([?] is compatible with anything). *)
let check_indices tgt nparams computed v =
  List.iteri (fun k c ->
      match tgt.args.(nparams + k), c with
      | Unk, _ | _, Unk | Ty _, _ | _, Ty _ -> ()
      | Val i, Val c when same_value i c -> ()
      | _ -> raise (Cast_error ("index mismatch at type " ^ to_string (Ind tgt))))
    computed;
  v

(* Builders used by the extracted code. *)
let unknown_ty = Unknown
let err_ty = Err
let erased = Erased
let sort n = Sort n
let pi a b = Pi (a, b)
let ind name args = Ind { name; args = Array.of_list args }
let rnil : (string * (ind -> ind -> Obj.t -> Obj.t)) list = []
let rcons name f l = (name, f) :: l
let anil : arg list = []
let acons (a : arg) l = a :: l
let ty_arg t = Ty t
let val_arg v = Val (Obj.repr v)
let unk_arg = Unk
let err_arg = Error
let erased_arg = Ty Erased

let param_ty (i : ind) k = match i.args.(k) with
  | Ty t -> t
  | Unk -> Unknown
  | Error -> Err
  | Val _ -> Erased

let param_val (i : ind) k = match i.args.(k) with
  | Val v -> v
  | Unk -> raise (Unknown_term (i.name ^ " (parameter)"))
  | Error | Ty _ -> raise (Cast_error ("bad parameter of " ^ i.name))

end

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



(** val add : int -> int -> int **)

let rec add n m =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> m)
    (fun p -> succ (add p m))
    n

(** val succ_dyn : __ -> int **)

let succ_dyn x =
  add
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil) x)
    (succ 0)

(** val apply3 : __ -> int **)

let apply3 g =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
      (Gradual_rt.pi Gradual_rt.unknown_ty (fun _ -> Gradual_rt.unknown_ty))
      g
      (Gradual_rt.cast_with Gradual_rt.rnil
        (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
        Gradual_rt.unknown_ty (Obj.magic (succ (succ (succ 0))))))

(** val t_ok : unit -> int **)

let t_ok _ =
  succ_dyn
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
      Gradual_rt.unknown_ty (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ
      0))))))))))))))))))))))))))))))))))))))))))

(** val t_bad : unit -> int **)

let t_bad _ =
  succ_dyn
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.ind "Corelib.Init.Datatypes.bool" Gradual_rt.anil)
      Gradual_rt.unknown_ty true)

(** val t_app : unit -> int **)

let t_app _ =
  apply3
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.pi
        (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
        (fun _ ->
        Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
      Gradual_rt.unknown_ty (fun x -> succ x))

(** val t_app_bad : unit -> int **)

let t_app_bad _ =
  apply3
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.pi
        (Gradual_rt.ind "Corelib.Init.Datatypes.bool" Gradual_rt.anil)
        (fun _ ->
        Gradual_rt.ind "Corelib.Init.Datatypes.bool" Gradual_rt.anil))
      Gradual_rt.unknown_ty negb)

(** val t_list : unit -> int list **)

let t_list _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Obj.magic v with
      | [] -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic [])
      | x::x0 ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic ((Obj.magic x1)::(Obj.magic x2))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.list"
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.list"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        Gradual_rt.anil))
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
       Gradual_rt.unknown_ty (succ 0))::((Obj.magic Gradual_rt.cast_with
                                           Gradual_rt.rnil
                                           (Gradual_rt.ind
                                             "Corelib.Init.Datatypes.nat"
                                             Gradual_rt.anil)
                                           Gradual_rt.unknown_ty (succ (succ
                                           0)))::[]))

(** val t_list_bad : unit -> int list **)

let t_list_bad _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Obj.magic v with
      | [] -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic [])
      | x::x0 ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic ((Obj.magic x1)::(Obj.magic x2))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.list"
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.list"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        Gradual_rt.anil))
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
       Gradual_rt.unknown_ty (succ 0))::((Obj.magic Gradual_rt.cast_with
                                           Gradual_rt.rnil
                                           (Gradual_rt.ind
                                             "Corelib.Init.Datatypes.bool"
                                             Gradual_rt.anil)
                                           Gradual_rt.unknown_ty true)::[]))

(** val pr : __ * __ **)

let pr =
  (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
    Gradual_rt.unknown_ty (succ 0)),(Obj.magic Gradual_rt.cast_with
                                      Gradual_rt.rnil
                                      (Gradual_rt.ind
                                        "Corelib.Init.Datatypes.bool"
                                        Gradual_rt.anil)
                                      Gradual_rt.unknown_ty true)

(** val t_pair : unit -> int * bool **)

let t_pair _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.prod" (fun src tgt v ->
      let x,x0 = Obj.magic v in
      let x1 =
        Gradual_rt.cast (Gradual_rt.param_ty src 0)
          (Gradual_rt.param_ty tgt 0) (Obj.magic x)
      in
      let x2 =
        Gradual_rt.cast (Gradual_rt.param_ty src 1)
          (Gradual_rt.param_ty tgt 1) (Obj.magic x0)
      in
      Gradual_rt.check_indices tgt 2 Gradual_rt.anil
        (Obj.magic ((Obj.magic x1),(Obj.magic x2))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.prod"
      (Gradual_rt.acons Gradual_rt.unk_arg
        (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil)))
    (Gradual_rt.ind "Corelib.Init.Datatypes.prod"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        (Gradual_rt.acons
          (Gradual_rt.ty_arg
            (Gradual_rt.ind "Corelib.Init.Datatypes.bool" Gradual_rt.anil))
          Gradual_rt.anil)))
    pr

(** val t_pair_bad : unit -> bool * int **)

let t_pair_bad _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.prod" (fun src tgt v ->
      let x,x0 = Obj.magic v in
      let x1 =
        Gradual_rt.cast (Gradual_rt.param_ty src 0)
          (Gradual_rt.param_ty tgt 0) (Obj.magic x)
      in
      let x2 =
        Gradual_rt.cast (Gradual_rt.param_ty src 1)
          (Gradual_rt.param_ty tgt 1) (Obj.magic x0)
      in
      Gradual_rt.check_indices tgt 2 Gradual_rt.anil
        (Obj.magic ((Obj.magic x1),(Obj.magic x2))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.prod"
      (Gradual_rt.acons Gradual_rt.unk_arg
        (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil)))
    (Gradual_rt.ind "Corelib.Init.Datatypes.prod"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.bool" Gradual_rt.anil))
        (Gradual_rt.acons
          (Gradual_rt.ty_arg
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
          Gradual_rt.anil)))
    pr

(** val t_option : unit -> bool option **)

let t_option _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.option" (fun src tgt v ->
      match Obj.magic v with
      | Some x ->
        let x0 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Some (Obj.magic x0)))
      | None ->
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic None))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.option"
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.option"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.bool" Gradual_rt.anil))
        Gradual_rt.anil))
    (Some
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.ind "Corelib.Init.Datatypes.bool" Gradual_rt.anil)
      Gradual_rt.unknown_ty false))

(** val fs : __ list **)

let fs =
  (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
    (Gradual_rt.pi
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil) (fun _ ->
      Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
    Gradual_rt.unknown_ty (fun x -> succ x))::((Obj.magic
                                                 Gradual_rt.cast_with
                                                 Gradual_rt.rnil
                                                 (Gradual_rt.pi
                                                   (Gradual_rt.ind
                                                     "Corelib.Init.Datatypes.bool"
                                                     Gradual_rt.anil)
                                                   (fun _ ->
                                                   Gradual_rt.ind
                                                     "Corelib.Init.Datatypes.bool"
                                                     Gradual_rt.anil))
                                                 Gradual_rt.unknown_ty negb)::[])

(** val t_fs : unit -> (int -> int) list **)

let t_fs _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Obj.magic v with
      | [] -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic [])
      | x::x0 ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic ((Obj.magic x1)::(Obj.magic x2))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.list"
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.list"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.pi
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
            (fun _ ->
            Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)))
        Gradual_rt.anil))
    fs

type point = { px : int; py : bool }

(** val pt : __ **)

let pt =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
    (Gradual_rt.ind "gradual_prog.point" Gradual_rt.anil)
    Gradual_rt.unknown_ty { px = (succ 0); py = true }

(** val t_record : unit -> int **)

let t_record _ =
  (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
    (Gradual_rt.ind "gradual_prog.point" Gradual_rt.anil) pt).px

(** val t_record_bad : unit -> int **)

let t_record_bad _ =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil) pt

(** val pos : __ **)

let pos =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Specif.sig" (fun src tgt v ->
      let x =
        Gradual_rt.cast (Gradual_rt.param_ty src 0)
          (Gradual_rt.param_ty tgt 0) (Obj.magic v)
      in
      Gradual_rt.check_indices tgt 2 Gradual_rt.anil (Obj.magic x))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Specif.sig"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        (Gradual_rt.acons Gradual_rt.erased_arg Gradual_rt.anil)))
    Gradual_rt.unknown_ty (succ 0)

(** val t_sig : unit -> int **)

let t_sig _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Specif.sig" (fun src tgt v ->
      let x =
        Gradual_rt.cast (Gradual_rt.param_ty src 0)
          (Gradual_rt.param_ty tgt 0) (Obj.magic v)
      in
      Gradual_rt.check_indices tgt 2 Gradual_rt.anil (Obj.magic x))
      Gradual_rt.rnil)
    Gradual_rt.unknown_ty
    (Gradual_rt.ind "Corelib.Init.Specif.sig"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        (Gradual_rt.acons Gradual_rt.erased_arg Gradual_rt.anil)))
    pos

type 'a vec =
| Vnil
| Vcons of int * 'a * 'a vec

(** val vhead : int -> 'a1 vec -> 'a1 **)

let vhead _ = function
| Vnil -> Obj.magic ()
| Vcons (_, x, _) -> x

(** val v3 : int vec **)

let v3 =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
      match Obj.magic v with
      | Vnil ->
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic 0))
            Gradual_rt.anil)
          (Obj.magic Vnil)
      | Vcons (n, x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.vec"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Gradual_rt.ind "gradual_prog.vec"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons
            (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic (succ n0)))
            Gradual_rt.anil)
          (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "gradual_prog.vec"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        (Gradual_rt.acons (Gradual_rt.val_arg (succ (succ (succ 0))))
          Gradual_rt.anil)))
    (Gradual_rt.ind "gradual_prog.vec"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil)))
    (Vcons ((succ (succ 0)), (succ 0), (Vcons ((succ 0), (succ (succ 0)),
    (Vcons (0, (succ (succ (succ 0))), Vnil))))))

(** val t_vec : unit -> int **)

let t_vec _ =
  vhead (succ (succ 0))
    (Obj.magic Gradual_rt.cast_with
      (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
        match Obj.magic v with
        | Vnil ->
          Gradual_rt.check_indices tgt 1
            (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic 0))
              Gradual_rt.anil)
            (Obj.magic Vnil)
        | Vcons (n, x, x0) ->
          let x1 =
            Gradual_rt.cast (Gradual_rt.param_ty src 0)
              (Gradual_rt.param_ty tgt 0) (Obj.magic x)
          in
          let x2 =
            Gradual_rt.cast
              (Gradual_rt.ind "gradual_prog.vec"
                (Gradual_rt.acons
                  (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                  (Gradual_rt.acons
                    (Gradual_rt.val_arg
                      (let n0 = Obj.magic n in Obj.magic n0))
                    Gradual_rt.anil)))
              (Gradual_rt.ind "gradual_prog.vec"
                (Gradual_rt.acons
                  (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                  (Gradual_rt.acons
                    (Gradual_rt.val_arg
                      (let n0 = Obj.magic n in Obj.magic n0))
                    Gradual_rt.anil)))
              (Obj.magic x0)
          in
          Gradual_rt.check_indices tgt 1
            (Gradual_rt.acons
              (Gradual_rt.val_arg
                (let n0 = Obj.magic n in Obj.magic (succ n0)))
              Gradual_rt.anil)
            (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1),
              (Obj.magic x2)))))
        Gradual_rt.rnil)
      (Gradual_rt.ind "gradual_prog.vec"
        (Gradual_rt.acons
          (Gradual_rt.ty_arg
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
          (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil)))
      (Gradual_rt.ind "gradual_prog.vec"
        (Gradual_rt.acons
          (Gradual_rt.ty_arg
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
          (Gradual_rt.acons (Gradual_rt.val_arg (succ (succ (succ 0))))
            Gradual_rt.anil)))
      v3)

(** val t_vec_bad : unit -> int vec **)

let t_vec_bad _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
      match Obj.magic v with
      | Vnil ->
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic 0))
            Gradual_rt.anil)
          (Obj.magic Vnil)
      | Vcons (n, x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.vec"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Gradual_rt.ind "gradual_prog.vec"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons
            (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic (succ n0)))
            Gradual_rt.anil)
          (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "gradual_prog.vec"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil)))
    (Gradual_rt.ind "gradual_prog.vec"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        (Gradual_rt.acons (Gradual_rt.val_arg (succ (succ 0)))
          Gradual_rt.anil)))
    v3

(** val rep : int -> int vec **)

let rec rep n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> Vnil)
    (fun k -> Vcons (k, k, (rep k)))
    n

(** val rep_dyn : __ **)

let rep_dyn =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
      match Obj.magic v with
      | Vnil ->
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic 0))
            Gradual_rt.anil)
          (Obj.magic Vnil)
      | Vcons (n, x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.vec"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Gradual_rt.ind "gradual_prog.vec"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons
            (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic (succ n0)))
            Gradual_rt.anil)
          (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.pi
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil) (fun n ->
      Gradual_rt.ind "gradual_prog.vec"
        (Gradual_rt.acons
          (Gradual_rt.ty_arg
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
          (Gradual_rt.acons
            (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
            Gradual_rt.anil))))
    Gradual_rt.unknown_ty rep

(** val t_dep : unit -> int **)

let t_dep _ =
  vhead (succ (succ 0))
    (Obj.magic Gradual_rt.cast_with
      (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
        match Obj.magic v with
        | Vnil ->
          Gradual_rt.check_indices tgt 1
            (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic 0))
              Gradual_rt.anil)
            (Obj.magic Vnil)
        | Vcons (n, x, x0) ->
          let x1 =
            Gradual_rt.cast (Gradual_rt.param_ty src 0)
              (Gradual_rt.param_ty tgt 0) (Obj.magic x)
          in
          let x2 =
            Gradual_rt.cast
              (Gradual_rt.ind "gradual_prog.vec"
                (Gradual_rt.acons
                  (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                  (Gradual_rt.acons
                    (Gradual_rt.val_arg
                      (let n0 = Obj.magic n in Obj.magic n0))
                    Gradual_rt.anil)))
              (Gradual_rt.ind "gradual_prog.vec"
                (Gradual_rt.acons
                  (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                  (Gradual_rt.acons
                    (Gradual_rt.val_arg
                      (let n0 = Obj.magic n in Obj.magic n0))
                    Gradual_rt.anil)))
              (Obj.magic x0)
          in
          Gradual_rt.check_indices tgt 1
            (Gradual_rt.acons
              (Gradual_rt.val_arg
                (let n0 = Obj.magic n in Obj.magic (succ n0)))
              Gradual_rt.anil)
            (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1),
              (Obj.magic x2)))))
        Gradual_rt.rnil)
      Gradual_rt.unknown_ty
      (Gradual_rt.pi
        (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
        (fun n ->
        Gradual_rt.ind "gradual_prog.vec"
          (Gradual_rt.acons
            (Gradual_rt.ty_arg
              (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
            (Gradual_rt.acons
              (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
              Gradual_rt.anil))))
      rep_dyn (succ (succ (succ 0))))

(** val t_dep_bad : unit -> int **)

let t_dep_bad _ =
  vhead (succ (succ (succ 0)))
    (Obj.magic Gradual_rt.cast_with
      (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
        match Obj.magic v with
        | Vnil ->
          Gradual_rt.check_indices tgt 1
            (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic 0))
              Gradual_rt.anil)
            (Obj.magic Vnil)
        | Vcons (n, x, x0) ->
          let x1 =
            Gradual_rt.cast (Gradual_rt.param_ty src 0)
              (Gradual_rt.param_ty tgt 0) (Obj.magic x)
          in
          let x2 =
            Gradual_rt.cast
              (Gradual_rt.ind "gradual_prog.vec"
                (Gradual_rt.acons
                  (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                  (Gradual_rt.acons
                    (Gradual_rt.val_arg
                      (let n0 = Obj.magic n in Obj.magic n0))
                    Gradual_rt.anil)))
              (Gradual_rt.ind "gradual_prog.vec"
                (Gradual_rt.acons
                  (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                  (Gradual_rt.acons
                    (Gradual_rt.val_arg
                      (let n0 = Obj.magic n in Obj.magic n0))
                    Gradual_rt.anil)))
              (Obj.magic x0)
          in
          Gradual_rt.check_indices tgt 1
            (Gradual_rt.acons
              (Gradual_rt.val_arg
                (let n0 = Obj.magic n in Obj.magic (succ n0)))
              Gradual_rt.anil)
            (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1),
              (Obj.magic x2)))))
        Gradual_rt.rnil)
      Gradual_rt.unknown_ty
      (Gradual_rt.pi
        (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
        (fun n ->
        Gradual_rt.ind "gradual_prog.vec"
          (Gradual_rt.acons
            (Gradual_rt.ty_arg
              (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
            (Gradual_rt.acons
              (Gradual_rt.val_arg
                (let n0 = Obj.magic n in Obj.magic (succ n0)))
              Gradual_rt.anil))))
      rep_dyn (succ (succ (succ 0))))

type 'a tree =
| Node of 'a * 'a forest
and 'a forest =
| Fnil
| Fcons of 'a tree * 'a forest

(** val tr : __ tree **)

let tr =
  Node
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
       Gradual_rt.unknown_ty (succ 0)),
    (Fcons ((Node
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
       Gradual_rt.unknown_ty (succ (succ 0))),
    Fnil)), Fnil)))

(** val t_tree : unit -> int tree **)

let t_tree _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "gradual_prog.tree#forest" (fun src tgt v ->
      match Obj.magic v with
      | Fnil ->
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Fnil)
      | Fcons (x, x0) ->
        let x1 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#tree"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#tree"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#forest"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#forest"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Fcons ((Obj.magic x1), (Obj.magic x2)))))
      (Gradual_rt.rcons "gradual_prog.tree#tree" (fun src tgt v ->
        let Node (x, x0) = Obj.magic v in
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#forest"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#forest"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Node ((Obj.magic x1), (Obj.magic x2)))))
        Gradual_rt.rnil))
    (Gradual_rt.ind "gradual_prog.tree#tree"
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "gradual_prog.tree#tree"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        Gradual_rt.anil))
    tr

(** val tr_bad : __ tree **)

let tr_bad =
  Node
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
       Gradual_rt.unknown_ty (succ 0)),
    (Fcons ((Node
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.bool" Gradual_rt.anil)
       Gradual_rt.unknown_ty true),
    Fnil)), Fnil)))

(** val t_tree_bad : unit -> int tree **)

let t_tree_bad _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "gradual_prog.tree#forest" (fun src tgt v ->
      match Obj.magic v with
      | Fnil ->
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Fnil)
      | Fcons (x, x0) ->
        let x1 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#tree"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#tree"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#forest"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#forest"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Fcons ((Obj.magic x1), (Obj.magic x2)))))
      (Gradual_rt.rcons "gradual_prog.tree#tree" (fun src tgt v ->
        let Node (x, x0) = Obj.magic v in
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#forest"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#forest"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Node ((Obj.magic x1), (Obj.magic x2)))))
        Gradual_rt.rnil))
    (Gradual_rt.ind "gradual_prog.tree#tree"
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "gradual_prog.tree#tree"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        Gradual_rt.anil))
    tr_bad

type 'a rose =
| Rnode of 'a * 'a rose list

(** val ro : __ rose **)

let ro =
  Rnode
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
       Gradual_rt.unknown_ty (succ 0)),
    ((Rnode
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)
       Gradual_rt.unknown_ty (succ (succ 0))),
    []))::[]))

(** val t_rose : unit -> int rose **)

let t_rose _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Obj.magic v with
      | [] -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic [])
      | x::x0 ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic ((Obj.magic x1)::(Obj.magic x2))))
      (Gradual_rt.rcons "gradual_prog.rose" (fun src tgt v ->
        let Rnode (x, x0) = Obj.magic v in
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg
                  (Gradual_rt.ind "gradual_prog.rose"
                    (Gradual_rt.acons
                      (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                      Gradual_rt.anil)))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list"
              (Gradual_rt.acons
                (Gradual_rt.ty_arg
                  (Gradual_rt.ind "gradual_prog.rose"
                    (Gradual_rt.acons
                      (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                      Gradual_rt.anil)))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Rnode ((Obj.magic x1), (Obj.magic x2)))))
        Gradual_rt.rnil))
    (Gradual_rt.ind "gradual_prog.rose"
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "gradual_prog.rose"
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
        Gradual_rt.anil))
    ro

(** val t_unk : unit -> int **)

let t_unk _ =
  Obj.magic Gradual_rt.unknown_term
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)

(** val t_unk_fun : unit -> int **)

let t_unk_fun _ =
  Obj.magic Gradual_rt.unknown_term
    (Gradual_rt.pi
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil) (fun _ ->
      Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))
    (succ (succ (succ 0)))

(** val t_unk_dyn : unit -> int **)

let t_unk_dyn _ =
  succ_dyn (Obj.magic Gradual_rt.unknown_term Gradual_rt.unknown_ty)

(** val t_err : unit -> int **)

let t_err _ =
  Obj.magic Gradual_rt.err_term
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil)

(** val t_err_fun : unit -> int -> int **)

let t_err_fun _ =
  Obj.magic Gradual_rt.err_term
    (Gradual_rt.pi
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil) (fun _ ->
      Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil))

(** val t_sort_bad : unit -> int **)

let t_sort_bad _ =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil (Gradual_rt.sort 2)
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" Gradual_rt.anil) __

(** val delta : __ -> __ **)

let delta x =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
    (Gradual_rt.pi Gradual_rt.unknown_ty (fun _ -> Gradual_rt.unknown_ty)) x x

(** val t_omega : unit -> __ **)

let t_omega _ =
  delta
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.pi Gradual_rt.unknown_ty (fun _ -> Gradual_rt.unknown_ty))
      Gradual_rt.unknown_ty delta)
