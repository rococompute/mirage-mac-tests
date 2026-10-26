
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
(** The error [err_A] was eliminated: a cast failed at run time. *)

exception Unknown_term of string
(** The unknown term [?_A] at an inductive type was eliminated. *)

(* As in the kernel, [?_I] and [err_I] at an inductive type [I] are values:
   [cons raise nil] is a list, and [2 + ?] is [S (S ?)]. They are blocks
   with a tag that no extracted constructor uses, holding their kind and a
   message, and they raise only when eliminated: every [match] of a file
   that uses this runtime goes through [check]. Types whose values cannot
   hold them (mapped to OCaml types by Extract Inductive, singleton and
   coinductive types) raise at once instead. *)
let exc_tag = 245

let make_exc (unknown : bool) (msg : string) : Obj.t =
  Obj.with_tag exc_tag (Obj.repr (unknown, msg))

let is_exc (v : Obj.t) = Obj.is_block v && Obj.tag v = exc_tag

let raise_exc (v : Obj.t) =
  let (unknown, msg) : bool * string = Obj.obj (Obj.with_tag 0 v) in
  if unknown then raise (Unknown_term msg) else raise (Cast_error msg)

(** [check v] is [v], unless [v] is [?] or [err] at an inductive type, which
    it raises. Extracted code calls it on everything it matches on. *)
let check (v : 'a) : 'a = let r = Obj.repr v in if is_exc r then raise_exc r else v

let is_unknown (v : 'a) = let r = Obj.repr v in is_exc r && fst (Obj.obj (Obj.with_tag 0 r) : bool * string)
let is_error (v : 'a) = let r = Obj.repr v in is_exc r && not (is_unknown v)

(** [force v] is [v], unless [?] or [err] occurs in the data of [v] (not
    under functions), which it raises. *)
let force (v : 'a) : 'a =
  let rec go r =
    if Obj.is_block r then
      let t = Obj.tag r in
      if t = exc_tag then raise_exc r
      else if t < exc_tag then for i = 0 to Obj.size r - 1 do go (Obj.field r i) done
  in
  go (Obj.repr v); v

type ty =
  | Unknown
  | Err
  | Erased  (* propositions and their proofs: nothing to check *)
  | Sort of int  (* 0 = Prop, 1 = Set, 2 = Type *)
  | Pi of ty * (Obj.t -> ty)
  | Ind of ind

and ind = {
  name : string;
  data : bool;  (* its values can be [?] and [err] (see [exc_tag]) *)
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

(* [err] at type [b]: a value when [b] is an inductive type that can hold
   it. *)
let error_at b msg = match b with
  | Ind { data = true; _ } -> make_exc false msg
  | _ -> raise (Cast_error msg)

let fail a b = error_at b ("cannot cast from " ^ to_string a ^ " to " ^ to_string b)

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
  | Ind i -> if i.data then make_exc true i.name else raise (Unknown_term i.name)
  | Err -> raise (Cast_error "unknown term of the error type")

let rec err_term ty : Obj.t = match ty with
  | Unknown -> Obj.repr { dty = Err; dv = dummy }
  | Erased | Sort _ -> dummy
  | Pi (_, b) -> Obj.repr (fun x -> err_term (b x))
  | Ind _ | Err -> error_at ty ("error at type " ^ to_string ty)

let rec cast a b (v : Obj.t) : Obj.t =
  if equal a b then v
  else if is_exc v then
    (* [?_A] and [err_A] cast to [B] are [?_B] and [err_B] *)
    begin match b with
      | Ind { data = true; _ } -> v
      | Unknown -> Obj.repr { dty = (if is_unknown v then Unknown else Err); dv = dummy }
      | _ -> raise_exc v
    end
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
  let compatible k c = match tgt.args.(nparams + k), c with
    | Unk, _ | _, Unk | Ty _, _ | _, Ty _ -> true
    | Val i, Val c ->
      (* an index computed as [?] is compatible with anything *)
      if is_exc c || is_exc i then is_unknown c || is_unknown i
      else same_value i c
    | (Val _ | Error), _ -> false
  in
  if List.for_all Fun.id (List.mapi compatible computed) then v
  else error_at (Ind tgt) ("index mismatch at type " ^ to_string (Ind tgt))

(* Builders used by the extracted code. *)
let unknown_ty = Unknown
let err_ty = Err
let erased = Erased
let sort n = Sort n
let pi a b = Pi (a, b)
let ind name data args = Ind { name; data; args = Array.of_list args }
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

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length l =
  match Gradual_rt.check l with
  | Nil -> O
  | Cons (_, l') -> S (length l')

(** val add : nat -> nat -> nat **)

let rec add n m =
  match Gradual_rt.check n with
  | O -> m
  | S p -> S (add p m)

(** val succ_dyn : __ -> nat **)

let succ_dyn x =
  add
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil) x)
    (S O)

(** val apply3 : __ -> nat **)

let apply3 g =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
      (Gradual_rt.pi Gradual_rt.unknown_ty (fun _ -> Gradual_rt.unknown_ty))
      g
      (Gradual_rt.cast_with Gradual_rt.rnil
        (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
        Gradual_rt.unknown_ty (Obj.magic (S (S (S O))))))

(** val t_ok : unit -> nat **)

let t_ok _ =
  succ_dyn
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
      Gradual_rt.unknown_ty (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S O))))))))))))))))))))))))))))))))))))))))))

(** val t_bad : unit -> nat **)

let t_bad _ =
  succ_dyn
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil)
      Gradual_rt.unknown_ty true)

(** val t_app : unit -> nat **)

let t_app _ =
  apply3
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.pi
        (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
        (fun _ ->
        Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
      Gradual_rt.unknown_ty (fun x -> S x))

(** val t_app_bad : unit -> nat **)

let t_app_bad _ =
  apply3
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.pi
        (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil)
        (fun _ ->
        Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil))
      Gradual_rt.unknown_ty negb)

(** val t_list : unit -> nat list **)

let t_list _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Nil -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Nil)
      | Cons (x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Cons ((Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        Gradual_rt.anil))
    (Cons
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
       Gradual_rt.unknown_ty (S O)),
    (Cons
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
       Gradual_rt.unknown_ty (S (S O))),
    Nil))))

(** val t_list_bad : unit -> nat list **)

let t_list_bad _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Nil -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Nil)
      | Cons (x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Cons ((Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        Gradual_rt.anil))
    (Cons
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
       Gradual_rt.unknown_ty (S O)),
    (Cons
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil)
       Gradual_rt.unknown_ty true),
    Nil))))

(** val t_list_bad_length : unit -> nat **)

let t_list_bad_length _ =
  length (t_list_bad ())

(** val t_list_bad_head : unit -> nat **)

let t_list_bad_head _ =
  match Gradual_rt.check (t_list_bad ()) with
  | Nil -> O
  | Cons (x, _) -> x

(** val pr : (__, __) prod **)

let pr =
  Pair
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
       Gradual_rt.unknown_ty (S O)),
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil)
      Gradual_rt.unknown_ty true))

(** val t_pair : unit -> (nat, bool) prod **)

let t_pair _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.prod" (fun src tgt v ->
      let Pair (x, x0) = Gradual_rt.check (Obj.magic v) in
      let x1 =
        Gradual_rt.cast (Gradual_rt.param_ty src 0)
          (Gradual_rt.param_ty tgt 0) (Obj.magic x)
      in
      let x2 =
        Gradual_rt.cast (Gradual_rt.param_ty src 1)
          (Gradual_rt.param_ty tgt 1) (Obj.magic x0)
      in
      Gradual_rt.check_indices tgt 2 Gradual_rt.anil
        (Obj.magic (Pair ((Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.prod" true
      (Gradual_rt.acons Gradual_rt.unk_arg
        (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil)))
    (Gradual_rt.ind "Corelib.Init.Datatypes.prod" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        (Gradual_rt.acons
          (Gradual_rt.ty_arg
            (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false
              Gradual_rt.anil))
          Gradual_rt.anil)))
    pr

(** val t_pair_bad : unit -> (bool, nat) prod **)

let t_pair_bad _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.prod" (fun src tgt v ->
      let Pair (x, x0) = Gradual_rt.check (Obj.magic v) in
      let x1 =
        Gradual_rt.cast (Gradual_rt.param_ty src 0)
          (Gradual_rt.param_ty tgt 0) (Obj.magic x)
      in
      let x2 =
        Gradual_rt.cast (Gradual_rt.param_ty src 1)
          (Gradual_rt.param_ty tgt 1) (Obj.magic x0)
      in
      Gradual_rt.check_indices tgt 2 Gradual_rt.anil
        (Obj.magic (Pair ((Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.prod" true
      (Gradual_rt.acons Gradual_rt.unk_arg
        (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil)))
    (Gradual_rt.ind "Corelib.Init.Datatypes.prod" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil))
        (Gradual_rt.acons
          (Gradual_rt.ty_arg
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
          Gradual_rt.anil)))
    pr

(** val t_option : unit -> bool option **)

let t_option _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.option" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
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
    (Gradual_rt.ind "Corelib.Init.Datatypes.option" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.option" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil))
        Gradual_rt.anil))
    (Some
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
      (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil)
      Gradual_rt.unknown_ty false))

(** val fs : __ list **)

let fs =
  Cons
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.pi
         (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
         (fun _ ->
         Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
       Gradual_rt.unknown_ty (fun x -> S x)),
    (Cons
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.pi
         (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil)
         (fun _ ->
         Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil))
       Gradual_rt.unknown_ty negb),
    Nil)))

(** val t_fs : unit -> (nat -> nat) list **)

let t_fs _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Nil -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Nil)
      | Cons (x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Cons ((Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.pi
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
            (fun _ ->
            Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)))
        Gradual_rt.anil))
    fs

type point = { px : nat; py : bool }

(** val pt : __ **)

let pt =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
    (Gradual_rt.ind "gradual_prog.point" true Gradual_rt.anil)
    Gradual_rt.unknown_ty { px = (S O); py = true }

(** val t_record : unit -> nat **)

let t_record _ =
  (Gradual_rt.check
    (Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
      (Gradual_rt.ind "gradual_prog.point" true Gradual_rt.anil) pt)).px

(** val t_record_bad : unit -> nat **)

let t_record_bad _ =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil) pt

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
    (Gradual_rt.ind "Corelib.Init.Specif.sig" false
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        (Gradual_rt.acons Gradual_rt.erased_arg Gradual_rt.anil)))
    Gradual_rt.unknown_ty (S O)

(** val t_sig : unit -> nat **)

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
    (Gradual_rt.ind "Corelib.Init.Specif.sig" false
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        (Gradual_rt.acons Gradual_rt.erased_arg Gradual_rt.anil)))
    pos

type 'a vec =
| Vnil
| Vcons of nat * 'a * 'a vec

(** val vhead : nat -> 'a1 vec -> 'a1 **)

let vhead _ v =
  match Gradual_rt.check v with
  | Vnil -> Obj.magic ()
  | Vcons (_, x, _) -> x

(** val v3 : nat vec **)

let v3 =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Vnil ->
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic O))
            Gradual_rt.anil)
          (Obj.magic Vnil)
      | Vcons (n, x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.vec" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Gradual_rt.ind "gradual_prog.vec" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons
            (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic (S n0)))
            Gradual_rt.anil)
          (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "gradual_prog.vec" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        (Gradual_rt.acons (Gradual_rt.val_arg (S (S (S O)))) Gradual_rt.anil)))
    (Gradual_rt.ind "gradual_prog.vec" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil)))
    (Vcons ((S (S O)), (S O), (Vcons ((S O), (S (S O)), (Vcons (O, (S (S (S
    O))), Vnil))))))

(** val t_vec : unit -> nat **)

let t_vec _ =
  vhead (S (S O))
    (Obj.magic Gradual_rt.cast_with
      (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
        match Gradual_rt.check (Obj.magic v) with
        | Vnil ->
          Gradual_rt.check_indices tgt 1
            (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic O))
              Gradual_rt.anil)
            (Obj.magic Vnil)
        | Vcons (n, x, x0) ->
          let x1 =
            Gradual_rt.cast (Gradual_rt.param_ty src 0)
              (Gradual_rt.param_ty tgt 0) (Obj.magic x)
          in
          let x2 =
            Gradual_rt.cast
              (Gradual_rt.ind "gradual_prog.vec" true
                (Gradual_rt.acons
                  (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                  (Gradual_rt.acons
                    (Gradual_rt.val_arg
                      (let n0 = Obj.magic n in Obj.magic n0))
                    Gradual_rt.anil)))
              (Gradual_rt.ind "gradual_prog.vec" true
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
              (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic (S n0)))
              Gradual_rt.anil)
            (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1),
              (Obj.magic x2)))))
        Gradual_rt.rnil)
      (Gradual_rt.ind "gradual_prog.vec" true
        (Gradual_rt.acons
          (Gradual_rt.ty_arg
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
          (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil)))
      (Gradual_rt.ind "gradual_prog.vec" true
        (Gradual_rt.acons
          (Gradual_rt.ty_arg
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
          (Gradual_rt.acons (Gradual_rt.val_arg (S (S (S O))))
            Gradual_rt.anil)))
      v3)

(** val t_vec_bad : unit -> nat vec **)

let t_vec_bad _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Vnil ->
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic O))
            Gradual_rt.anil)
          (Obj.magic Vnil)
      | Vcons (n, x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.vec" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Gradual_rt.ind "gradual_prog.vec" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons
            (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic (S n0)))
            Gradual_rt.anil)
          (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "gradual_prog.vec" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil)))
    (Gradual_rt.ind "gradual_prog.vec" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        (Gradual_rt.acons (Gradual_rt.val_arg (S (S O))) Gradual_rt.anil)))
    v3

(** val rep : nat -> nat vec **)

let rec rep n =
  match Gradual_rt.check n with
  | O -> Vnil
  | S k -> Vcons (k, k, (rep k))

(** val rep_dyn : __ **)

let rep_dyn =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Vnil ->
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic O))
            Gradual_rt.anil)
          (Obj.magic Vnil)
      | Vcons (n, x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.vec" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Gradual_rt.ind "gradual_prog.vec" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                (Gradual_rt.acons
                  (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
                  Gradual_rt.anil)))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1
          (Gradual_rt.acons
            (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic (S n0)))
            Gradual_rt.anil)
          (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.pi
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
      (fun n ->
      Gradual_rt.ind "gradual_prog.vec" true
        (Gradual_rt.acons
          (Gradual_rt.ty_arg
            (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
          (Gradual_rt.acons
            (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
            Gradual_rt.anil))))
    Gradual_rt.unknown_ty rep

(** val t_dep : unit -> nat **)

let t_dep _ =
  vhead (S (S O))
    (Obj.magic Gradual_rt.cast_with
      (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
        match Gradual_rt.check (Obj.magic v) with
        | Vnil ->
          Gradual_rt.check_indices tgt 1
            (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic O))
              Gradual_rt.anil)
            (Obj.magic Vnil)
        | Vcons (n, x, x0) ->
          let x1 =
            Gradual_rt.cast (Gradual_rt.param_ty src 0)
              (Gradual_rt.param_ty tgt 0) (Obj.magic x)
          in
          let x2 =
            Gradual_rt.cast
              (Gradual_rt.ind "gradual_prog.vec" true
                (Gradual_rt.acons
                  (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                  (Gradual_rt.acons
                    (Gradual_rt.val_arg
                      (let n0 = Obj.magic n in Obj.magic n0))
                    Gradual_rt.anil)))
              (Gradual_rt.ind "gradual_prog.vec" true
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
              (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic (S n0)))
              Gradual_rt.anil)
            (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1),
              (Obj.magic x2)))))
        Gradual_rt.rnil)
      Gradual_rt.unknown_ty
      (Gradual_rt.pi
        (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
        (fun n ->
        Gradual_rt.ind "gradual_prog.vec" true
          (Gradual_rt.acons
            (Gradual_rt.ty_arg
              (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true
                Gradual_rt.anil))
            (Gradual_rt.acons
              (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic n0))
              Gradual_rt.anil))))
      rep_dyn (S (S (S O))))

(** val t_dep_bad : unit -> nat **)

let t_dep_bad _ =
  vhead (S (S (S O)))
    (Obj.magic Gradual_rt.cast_with
      (Gradual_rt.rcons "gradual_prog.vec" (fun src tgt v ->
        match Gradual_rt.check (Obj.magic v) with
        | Vnil ->
          Gradual_rt.check_indices tgt 1
            (Gradual_rt.acons (Gradual_rt.val_arg (Obj.magic O))
              Gradual_rt.anil)
            (Obj.magic Vnil)
        | Vcons (n, x, x0) ->
          let x1 =
            Gradual_rt.cast (Gradual_rt.param_ty src 0)
              (Gradual_rt.param_ty tgt 0) (Obj.magic x)
          in
          let x2 =
            Gradual_rt.cast
              (Gradual_rt.ind "gradual_prog.vec" true
                (Gradual_rt.acons
                  (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                  (Gradual_rt.acons
                    (Gradual_rt.val_arg
                      (let n0 = Obj.magic n in Obj.magic n0))
                    Gradual_rt.anil)))
              (Gradual_rt.ind "gradual_prog.vec" true
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
              (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic (S n0)))
              Gradual_rt.anil)
            (Obj.magic (Vcons ((Obj.magic n), (Obj.magic x1),
              (Obj.magic x2)))))
        Gradual_rt.rnil)
      Gradual_rt.unknown_ty
      (Gradual_rt.pi
        (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
        (fun n ->
        Gradual_rt.ind "gradual_prog.vec" true
          (Gradual_rt.acons
            (Gradual_rt.ty_arg
              (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true
                Gradual_rt.anil))
            (Gradual_rt.acons
              (Gradual_rt.val_arg (let n0 = Obj.magic n in Obj.magic (S n0)))
              Gradual_rt.anil))))
      rep_dyn (S (S (S O))))

type 'a tree =
| Node of 'a * 'a forest
and 'a forest =
| Fnil
| Fcons of 'a tree * 'a forest

(** val tr : __ tree **)

let tr =
  Node
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
       Gradual_rt.unknown_ty (S O)),
    (Fcons ((Node
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
       Gradual_rt.unknown_ty (S (S O))),
    Fnil)), Fnil)))

(** val t_tree : unit -> nat tree **)

let t_tree _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "gradual_prog.tree#forest" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Fnil ->
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Fnil)
      | Fcons (x, x0) ->
        let x1 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#tree" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#tree" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#forest" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#forest" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Fcons ((Obj.magic x1), (Obj.magic x2)))))
      (Gradual_rt.rcons "gradual_prog.tree#tree" (fun src tgt v ->
        let Node (x, x0) = Gradual_rt.check (Obj.magic v) in
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#forest" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#forest" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Node ((Obj.magic x1), (Obj.magic x2)))))
        Gradual_rt.rnil))
    (Gradual_rt.ind "gradual_prog.tree#tree" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "gradual_prog.tree#tree" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        Gradual_rt.anil))
    tr

(** val tr_bad : __ tree **)

let tr_bad =
  Node
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
       Gradual_rt.unknown_ty (S O)),
    (Fcons ((Node
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil)
       Gradual_rt.unknown_ty true),
    Fnil)), Fnil)))

(** val t_tree_bad : unit -> nat tree **)

let t_tree_bad _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "gradual_prog.tree#forest" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Fnil ->
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Fnil)
      | Fcons (x, x0) ->
        let x1 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#tree" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#tree" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#forest" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#forest" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Fcons ((Obj.magic x1), (Obj.magic x2)))))
      (Gradual_rt.rcons "gradual_prog.tree#tree" (fun src tgt v ->
        let Node (x, x0) = Gradual_rt.check (Obj.magic v) in
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "gradual_prog.tree#forest" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "gradual_prog.tree#forest" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Node ((Obj.magic x1), (Obj.magic x2)))))
        Gradual_rt.rnil))
    (Gradual_rt.ind "gradual_prog.tree#tree" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "gradual_prog.tree#tree" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        Gradual_rt.anil))
    tr_bad

(** val t_tree_bad_root : unit -> nat **)

let t_tree_bad_root _ =
  let Node (x, _) = Gradual_rt.check (t_tree_bad ()) in x

type 'a rose =
| Rnode of 'a * 'a rose list

(** val ro : __ rose **)

let ro =
  Rnode
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
       Gradual_rt.unknown_ty (S O)),
    (Cons ((Rnode
    ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
       (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
       Gradual_rt.unknown_ty (S (S O))),
    Nil)), Nil)))

(** val t_rose : unit -> nat rose **)

let t_rose _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Nil -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Nil)
      | Cons (x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Cons ((Obj.magic x1), (Obj.magic x2)))))
      (Gradual_rt.rcons "gradual_prog.rose" (fun src tgt v ->
        let Rnode (x, x0) = Gradual_rt.check (Obj.magic v) in
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg
                  (Gradual_rt.ind "gradual_prog.rose" true
                    (Gradual_rt.acons
                      (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                      Gradual_rt.anil)))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg
                  (Gradual_rt.ind "gradual_prog.rose" true
                    (Gradual_rt.acons
                      (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                      Gradual_rt.anil)))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Rnode ((Obj.magic x1), (Obj.magic x2)))))
        Gradual_rt.rnil))
    (Gradual_rt.ind "gradual_prog.rose" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "gradual_prog.rose" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        Gradual_rt.anil))
    ro

(** val t_unk : unit -> nat **)

let t_unk _ =
  Obj.magic Gradual_rt.unknown_term
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)

(** val t_unk_fun : unit -> nat **)

let t_unk_fun _ =
  Obj.magic Gradual_rt.unknown_term
    (Gradual_rt.pi
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
      (fun _ ->
      Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
    (S (S (S O)))

(** val t_unk_dyn : unit -> nat **)

let t_unk_dyn _ =
  succ_dyn (Obj.magic Gradual_rt.unknown_term Gradual_rt.unknown_ty)

(** val t_unk_plus : unit -> nat **)

let t_unk_plus _ =
  add (S (S O))
    (Obj.magic Gradual_rt.unknown_term
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))

(** val t_unk_elim : unit -> nat **)

let t_unk_elim _ =
  add
    (Obj.magic Gradual_rt.unknown_term
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
    (S (S O))

(** val t_err : unit -> nat **)

let t_err _ =
  Obj.magic Gradual_rt.err_term
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)

(** val t_err_fun : unit -> nat -> nat **)

let t_err_fun _ =
  Obj.magic Gradual_rt.err_term
    (Gradual_rt.pi
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
      (fun _ ->
      Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))

(** val t_sort_bad : unit -> nat **)

let t_sort_bad _ =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil (Gradual_rt.sort 2)
    (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil) __

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

(** val to_dyn : __ -> 'a1 -> __ **)

let to_dyn a x =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil a Gradual_rt.unknown_ty x

(** val of_dyn : __ -> __ -> 'a1 **)

let of_dyn a d =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil Gradual_rt.unknown_ty a d

(** val roundtrip : __ -> __ -> 'a1 -> 'a2 **)

let roundtrip a b x =
  of_dyn (Obj.magic b) (to_dyn (Obj.magic a) x)

(** val dyns : __ -> 'a1 list -> __ list **)

let rec dyns a l =
  match Gradual_rt.check l with
  | Nil -> Nil
  | Cons (x, r) -> Cons ((to_dyn (Obj.magic a) x), (dyns (Obj.magic a) r))

(** val dyns_local : __ -> 'a1 list -> __ list **)

let rec dyns_local a l =
  match Gradual_rt.check l with
  | Nil -> Nil
  | Cons (x, r) ->
    Cons
      ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil a
         Gradual_rt.unknown_ty x),
      (dyns_local a r))

(** val ev : __ -> 'a1 list -> __ list **)

let rec ev a l =
  match Gradual_rt.check l with
  | Nil -> Nil
  | Cons (x, r) -> Cons ((to_dyn (Obj.magic a) x), (od (Obj.magic a) r))

(** val od : __ -> 'a1 list -> __ list **)

and od a l =
  match Gradual_rt.check l with
  | Nil -> Nil
  | Cons (x, r) ->
    Cons
      ((Obj.magic Gradual_rt.cast_with Gradual_rt.rnil a
         Gradual_rt.unknown_ty x),
      (ev (Obj.magic a) r))

(** val poly_fun : __ -> ('a1 -> 'a1) -> __ **)

let poly_fun a f =
  Obj.magic Gradual_rt.cast_with Gradual_rt.rnil
    (Gradual_rt.pi (Obj.magic a) (fun _ -> Obj.magic a))
    Gradual_rt.unknown_ty f

(** val t_poly : unit -> nat **)

let t_poly _ =
  roundtrip
    (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.nat" true
      Gradual_rt.anil)
    (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.nat" true
      Gradual_rt.anil)
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))

(** val t_poly_bad : unit -> bool **)

let t_poly_bad _ =
  roundtrip
    (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.nat" true
      Gradual_rt.anil)
    (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.bool" false
      Gradual_rt.anil)
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))

(** val t_poly_list : unit -> nat list **)

let t_poly_list _ =
  of_dyn
    (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        Gradual_rt.anil))
    (to_dyn
      (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.list" true
        (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
      (dyns
        (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.nat" true
          Gradual_rt.anil)
        (Cons ((S O), (Cons ((S (S O)), Nil))))))

(** val t_poly_rec : unit -> nat list **)

let t_poly_rec _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Nil -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Nil)
      | Cons (x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Cons ((Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        Gradual_rt.anil))
    (dyns
      (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.nat" true
        Gradual_rt.anil)
      (Cons ((S O), (Cons ((S (S O)), Nil)))))

(** val t_poly_rec_bad : unit -> bool list **)

let t_poly_rec_bad _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Nil -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Nil)
      | Cons (x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Cons ((Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil))
        Gradual_rt.anil))
    (dyns
      (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.nat" true
        Gradual_rt.anil)
      (Cons ((S O), (Cons ((S (S O)), Nil)))))

(** val t_poly_local : unit -> bool list **)

let t_poly_local _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Nil -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Nil)
      | Cons (x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Cons ((Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.bool" false Gradual_rt.anil))
        Gradual_rt.anil))
    (dyns_local
      (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.bool" false
        Gradual_rt.anil)
      (Cons (true, Nil)))

(** val t_poly_mutual : unit -> nat list **)

let t_poly_mutual _ =
  Obj.magic Gradual_rt.cast_with
    (Gradual_rt.rcons "Corelib.Init.Datatypes.list" (fun src tgt v ->
      match Gradual_rt.check (Obj.magic v) with
      | Nil -> Gradual_rt.check_indices tgt 1 Gradual_rt.anil (Obj.magic Nil)
      | Cons (x, x0) ->
        let x1 =
          Gradual_rt.cast (Gradual_rt.param_ty src 0)
            (Gradual_rt.param_ty tgt 0) (Obj.magic x)
        in
        let x2 =
          Gradual_rt.cast
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty src 0))
                Gradual_rt.anil))
            (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
              (Gradual_rt.acons
                (Gradual_rt.ty_arg (Gradual_rt.param_ty tgt 0))
                Gradual_rt.anil))
            (Obj.magic x0)
        in
        Gradual_rt.check_indices tgt 1 Gradual_rt.anil
          (Obj.magic (Cons ((Obj.magic x1), (Obj.magic x2)))))
      Gradual_rt.rnil)
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons Gradual_rt.unk_arg Gradual_rt.anil))
    (Gradual_rt.ind "Corelib.Init.Datatypes.list" true
      (Gradual_rt.acons
        (Gradual_rt.ty_arg
          (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
        Gradual_rt.anil))
    (ev
      (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.nat" true
        Gradual_rt.anil)
      (Cons ((S O), (Cons ((S (S O)), (Cons ((S (S (S O))), Nil)))))))

(** val t_poly_fun : unit -> nat **)

let t_poly_fun _ =
  of_dyn
    (Obj.magic Gradual_rt.pi
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
      (fun _ ->
      Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
    (poly_fun
      (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.nat" true
        Gradual_rt.anil)
      (fun x -> S x))
    (S O)

(** val t_poly_fun_bad : unit -> nat **)

let t_poly_fun_bad _ =
  of_dyn
    (Obj.magic Gradual_rt.pi
      (Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil)
      (fun _ ->
      Gradual_rt.ind "Corelib.Init.Datatypes.nat" true Gradual_rt.anil))
    (poly_fun
      (Obj.magic Gradual_rt.ind "Corelib.Init.Datatypes.bool" false
        Gradual_rt.anil)
      negb)
    (S O)
