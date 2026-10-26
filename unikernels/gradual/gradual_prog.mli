
type __ = Obj.t

module Gradual_rt : sig
  exception Cast_error of string
  exception Unknown_term of string
end

val negb : bool -> bool



val add : int -> int -> int

val succ_dyn : __ -> int

val apply3 : __ -> int

val t_ok : unit -> int

val t_bad : unit -> int

val t_app : unit -> int

val t_app_bad : unit -> int

val t_list : unit -> int list

val t_list_bad : unit -> int list

val pr : __ * __

val t_pair : unit -> int * bool

val t_pair_bad : unit -> bool * int

val t_option : unit -> bool option

val fs : __ list

val t_fs : unit -> (int -> int) list

type point = { px : int; py : bool }

val pt : __

val t_record : unit -> int

val t_record_bad : unit -> int

val pos : __

val t_sig : unit -> int

type 'a vec =
| Vnil
| Vcons of int * 'a * 'a vec

val vhead : int -> 'a1 vec -> 'a1

val v3 : int vec

val t_vec : unit -> int

val t_vec_bad : unit -> int vec

val rep : int -> int vec

val rep_dyn : __

val t_dep : unit -> int

val t_dep_bad : unit -> int

type 'a tree =
| Node of 'a * 'a forest
and 'a forest =
| Fnil
| Fcons of 'a tree * 'a forest

val tr : __ tree

val t_tree : unit -> int tree

val tr_bad : __ tree

val t_tree_bad : unit -> int tree

type 'a rose =
| Rnode of 'a * 'a rose list

val ro : __ rose

val t_rose : unit -> int rose

val t_unk : unit -> int

val t_unk_fun : unit -> int

val t_unk_dyn : unit -> int

val t_err : unit -> int

val t_err_fun : unit -> int -> int

val t_sort_bad : unit -> int

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

val t_poly : unit -> int

val t_poly_bad : unit -> bool

val t_poly_list : unit -> int list

val t_poly_rec : unit -> int list

val t_poly_rec_bad : unit -> bool list

val t_poly_local : unit -> bool list

val t_poly_mutual : unit -> int list

val t_poly_fun : unit -> int

val t_poly_fun_bad : unit -> int
