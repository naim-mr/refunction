open Typed_syntax
open VarSet

module Taint = struct
  type t = VarSet.t

  let bot = VarSet.empty
  let join = VarSet.union
  let add x t = VarSet.add x t
  let filter = VarSet.filter
  let meet = VarSet.inter
  let leq = VarSet.subset
  let is_bot = VarSet.is_empty

  (* List of vars in an expression *)
  let vars_in_expr e =
    let rec aux e acc =
      match e with
      | T_var x -> add x acc
      | T_unary (_, (e, _, _)) -> aux e acc
      | T_binary (_, (e1, _, _), (e2, _, _)) -> join (aux e1 acc) (aux e2 acc)
      | _ -> acc
    in
    aux e bot

  (* Test if an expression is tainted *)
  let is_tainted ?(cp = []) e t =
    let rec aux e =
      match e with
      | T_var x -> VarSet.mem x t
      | T_unary (_, (e, _, _)) -> not (is_bot (meet (vars_in_expr e) t))
      | T_binary (_, (e1, _, _), (e2, _, _)) -> aux e1 || aux e2
      | T_input (id, _) -> not (List.mem id cp)
      | _ -> false
    in
    aux e

  let assigned block =
    let rec aux stmt acc =
      match stmt with
      | T_label _ | T_print _
      | T_add_var (_, None)
      | T_del_var _ | T_RETURN | T_assert _ | T_expr _ | T_assume _ ->
          acc
      | T_add_var (v, Some (e, t, ext)) -> add v acc
      | T_assign (lval, rval) -> (
          match lval with T_var v, typ, ext -> add v acc | _ -> failwith "nyi")
      | T_if (b, s1, s2) -> join (aux_block s1 acc) (aux_block s2 acc)
      | T_while ((l, _), b, s) -> aux_block s acc
      | T_call (f, ss) -> aux_block f.func_body acc
      | T_BREAK -> raise (Invalid_argument "bwdStm:T_BREAK")
    and aux_block s acc =
      match s with
      | T_empty (l, _) -> acc
      | T_stat ((l, _), (s, _), b) -> join (aux s acc) (aux_block b acc)
    in
    aux_block block bot
end
