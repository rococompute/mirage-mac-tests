
type __ = Obj.t

module Gradual_rt : sig
  exception Cast_error of string
  exception Unknown_term of string
  val check : 'a -> 'a
  val force : 'a -> 'a
  val is_unknown : 'a -> bool
  val is_error : 'a -> bool
end

val negb : bool -> bool

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

val length : 'a1 list -> nat

val add : nat -> nat -> nat

val succ_dyn : __ -> nat

val apply3 : __ -> nat

val t_ok : unit -> nat

val t_bad : unit -> nat

val t_app : unit -> nat

val t_app_bad : unit -> nat

val t_list : unit -> nat list

val t_list_bad : unit -> nat list

val t_list_bad_length : unit -> nat

val t_list_bad_head : unit -> nat

val pr : (__, __) prod

val t_pair : unit -> (nat, bool) prod

val t_pair_bad : unit -> (bool, nat) prod

val t_option : unit -> bool option

val fs : __ list

val t_fs : unit -> (nat -> nat) list

type point = { px : nat; py : bool }

val pt : __

val t_record : unit -> nat

val t_record_bad : unit -> nat

val pos : __

val t_sig : unit -> nat

type 'a vec =
| Vnil
| Vcons of nat * 'a * 'a vec

val vhead : nat -> 'a1 vec -> 'a1

val v3 : nat vec

val t_vec : unit -> nat

val t_vec_bad : unit -> nat vec

val rep : nat -> nat vec

val rep_dyn : __

val t_dep : unit -> nat

val t_dep_bad : unit -> nat

type 'a tree =
| Node of 'a * 'a forest
and 'a forest =
| Fnil
| Fcons of 'a tree * 'a forest

val tr : __ tree

val t_tree : unit -> nat tree

val tr_bad : __ tree

val t_tree_bad : unit -> nat tree

val t_tree_bad_root : unit -> nat

type 'a rose =
| Rnode of 'a * 'a rose list

val ro : __ rose

val t_rose : unit -> nat rose

val t_unk : unit -> nat

val t_unk_fun : unit -> nat

val t_unk_dyn : unit -> nat

val t_unk_plus : unit -> nat

val t_unk_elim : unit -> nat

val t_err : unit -> nat

val t_err_fun : unit -> nat -> nat

val t_sort_bad : unit -> nat

val t_int : unit -> Uint63.t

val t_int_bad : unit -> nat

val t_int_float : unit -> float

val delta : __ -> __

val t_omega : unit -> __

val to_dyn : __ -> 'a1 -> __

val of_dyn : __ -> __ -> 'a1

val roundtrip : __ -> __ -> 'a1 -> 'a2

val dyns : __ -> 'a1 list -> __ list

val dyns_local : __ -> 'a1 list -> __ list

val ev : __ -> 'a1 list -> __ list

val od : __ -> 'a1 list -> __ list

val poly_fun : __ -> ('a1 -> 'a1) -> __

val t_poly : unit -> nat

val t_poly_bad : unit -> bool

val t_poly_list : unit -> nat list

val t_poly_rec : unit -> nat list

val t_poly_rec_bad : unit -> bool list

val t_poly_local : unit -> bool list

val t_poly_mutual : unit -> nat list

val t_poly_fun : unit -> nat

val t_poly_fun_bad : unit -> nat
