(*
   Processed syntax tree:
   - variable scoping is resolved
   - trees are typed
   - casts are explicit
   - expressions are side-effect free
   - statements are labelled with unique identifiers

   Copyright (C) 2011 Antoine Miné
*)

open Abstract_syntax
open Utils
open Utils.Datatypes
open Apron

(************************************************************************)
(* TYPES *)
(************************************************************************)

(* constant sets *)
type int_set = Intinf.t * Intinf.t [@@deriving yojson, show] (* interval *)
type float_set = Float.t * Float.t [@@deriving yojson, show] (* interval *)
type bool_set = tbool [@@deriving yojson, show] (* 3-valued logic *)

(* expression nodes have type and source location *)
type 'a typed = 'a * typ * extent [@@deriving yojson, show]

(* side-effect free, typed expressions *)
type expr =
  | T_unary of unary_op * expr typed
  | T_binary of binary_op * expr typed * expr typed
  | T_float_const of float_set
  | T_int_const of int_set
  | T_input of string * int_set
  | T_bool_const of bool_set
  | T_var of var
  | T_deref of expr typed
  | T_address_of of expr typed

(* variables *)
and var = {
  var_name : string;
  var_extent : extent;
  var_typ : typ;
  var_id : id;
  var_synthetic : bool; (* added by translation? *)
  var_scope : var_scope;
}
[@@deriving yojson, show]

and var_scope = T_GLOBAL | T_LOCAL | T_INPUT | T_VOLATILE

let dummy_precond =
  (T_bool_const True, Abstract_syntax.A_BOOL, Abstract_syntax.extent_unknown)

(* statements *)
type label = id * position [@@deriving yojson]

let apron_of_var (v : var) : Var.t =
  Var.of_string ("$" ^ Z.to_string v.var_id ^ "#" ^ v.var_name)

let apron_of_string (s : string) : Var.t = Var.of_string s

let label_print fmt l =
  if Z.compare l (Z.of_int 10) = 0 then Format.fprintf fmt "[ %i:]" (Z.to_int l)
  else Format.fprintf fmt "[%i:]" (Z.to_int l)

type stat =
  | T_expr of expr typed
  | T_assign of expr typed * expr typed
  | T_call of func ext (* arguments and return values as local variables *)
  | T_if of expr typed * block * block
  | T_while of label (* loop-invariant label *) * expr typed * block
  | T_add_var of var * expr typed option
  | T_del_var of var
  | T_RETURN (* returned value in func_return *)
  | T_BREAK
  | T_assert of expr typed * label
  | T_assume of expr typed
  | T_print of var ext list
  | T_label of string ext

and block = T_empty of label | T_stat of label * stat ext * block

(* functions *)
and func = {
  func_name : string;
  func_extent : extent;
  func_id : id;
  func_return : var option;
  func_args : var list;
  func_body : block;
}

module VarSet = Set.Make (struct
  type t = var

  let compare = fun x y -> compare_id x.var_id y.var_id
end)

(* whole program *)

type prog =
  block
  * (* global variable creation and initialization *)
  func StringMap.t
  * (* function declarations *)
  var IdMap.t (* variables *)

(************************************************************************)
(* PRINTERS *)
(************************************************************************)

let string_of_unary_op = function
  | A_UNARY_PLUS -> "+"
  | A_UNARY_MINUS -> "-"
  | A_NOT -> "!"
  | A_cast (t, _) -> "(" ^ string_of_typ t ^ ")"

let string_of_binary_op = function
  | A_MULTIPLY -> "*"
  | A_DIVIDE -> "/"
  | A_MODULO -> "%"
  | A_PLUS -> "+"
  | A_MINUS -> "-"
  | A_EQUAL -> "=="
  | A_NOT_EQUAL -> "!="
  | A_LESS -> "<"
  | A_LESS_EQUAL -> "<="
  | A_GREATER -> ">"
  | A_GREATER_EQUAL -> ">="
  | A_AND -> "&&"
  | A_OR -> "||"

let binary_precedence = function
  | A_MULTIPLY | A_DIVIDE | A_MODULO -> 6
  | A_PLUS | A_MINUS -> 5
  | A_EQUAL | A_NOT_EQUAL -> 4
  | A_LESS | A_LESS_EQUAL | A_GREATER | A_GREATER_EQUAL -> 3
  | A_AND -> 2
  | A_OR -> 1

let expr_precedence e =
  match e with
  | T_unary (_, _) -> 99
  | T_binary (op, _, _) -> binary_precedence op
  | _ -> 100

let print_var_name fmt v =
  (*  Format.fprintf fmt "%s#%s" v.var_name (string_of_id "" v.var_id)*)
  Format.fprintf fmt "%s" v.var_name

let print_func_name fmt f =
  (*  Format.fprintf fmt "%s#%s" f.func_name (string_of_id "" f.func_id)*)
  Format.fprintf fmt "%s" f.func_name

let print_list f sep fmt l =
  let rec aux = function
    | [] -> ()
    | [ a ] -> f fmt a
    | a :: b ->
        f fmt a;
        Format.pp_print_string fmt sep;
        aux b
  in
  aux l

let pp_label fmt (l, _) = Format.fprintf fmt "{%s}" (string_of_id "" l)

let string_of_int_set (a, b) =
  if a = b then Intinf.to_string a
  else Printf.sprintf "[%a;%a]" Intinf.sprint a Intinf.sprint b

let string_of_float_set (a, b) =
  if a = b then Float.to_string a
  else Printf.sprintf "[%a;%a]" Float.sprint a Float.sprint b

let rec pp_expr_ext fmt ((e, _, _) : expr typed) =
  match e with
  | T_unary (op, ((e1, _, _) as ee1)) ->
      Format.pp_print_string fmt (string_of_unary_op op);
      if expr_precedence e1 <= expr_precedence e then
        Format.fprintf fmt " (%a)" pp_expr_ext ee1
      else Format.fprintf fmt " %a" pp_expr_ext ee1
  | T_binary (op, ((e1, _, _) as ee1), ((e2, _, _) as ee2)) ->
      if expr_precedence e1 < expr_precedence e then
        Format.fprintf fmt "(%a) " pp_expr_ext ee1
      else Format.fprintf fmt "%a " pp_expr_ext ee1;
      Format.pp_print_string fmt (string_of_binary_op op);
      if expr_precedence e2 <= expr_precedence e then
        Format.fprintf fmt " (%a)" pp_expr_ext ee2
      else Format.fprintf fmt " %a" pp_expr_ext ee2
  | T_float_const f -> Format.pp_print_string fmt (string_of_float_set f)
  | T_int_const i -> Format.pp_print_string fmt (string_of_int_set i)
  | T_bool_const b -> Format.pp_print_string fmt (string_of_tbool b)
  | T_input (id, (min, max)) ->
      Format.fprintf fmt "input('%s',%s)" id (string_of_int_set (min, max))
  | T_var v -> print_var_name fmt v
  | T_deref e -> Format.fprintf fmt " *%a " pp_expr_ext e
  | T_address_of e -> Format.fprintf fmt " &%a " pp_expr_ext e

let rec pp_expr fmt e =
  match e with
  | T_unary (op, (e1, _, _)) ->
      Format.pp_print_string fmt (string_of_unary_op op);
      if expr_precedence e1 <= expr_precedence e then
        Format.fprintf fmt " (%a)" pp_expr e1
      else Format.fprintf fmt " %a" pp_expr e1
  | T_binary (op, (e1, _, _), (e2, _, _)) ->
      if expr_precedence e1 < expr_precedence e then
        Format.fprintf fmt "(%a) " pp_expr e1
      else Format.fprintf fmt "%a " pp_expr e1;
      Format.pp_print_string fmt (string_of_binary_op op);
      if expr_precedence e2 <= expr_precedence e then
        Format.fprintf fmt " (%a)" pp_expr e2
      else Format.fprintf fmt " %a" pp_expr e2
  | T_float_const f -> Format.pp_print_string fmt (string_of_float_set f)
  | T_int_const i -> Format.pp_print_string fmt (string_of_int_set i)
  | T_bool_const b -> Format.pp_print_string fmt (string_of_tbool b)
  | T_input (id, (min, max)) ->
      Format.fprintf fmt "input('%s',%s)" id (string_of_int_set (min, max))
  | T_var v -> print_var_name fmt v
  | T_deref (e, _, _) -> Format.fprintf fmt " *%a " pp_expr e
  | T_address_of (e, _, _) -> Format.fprintf fmt " &%a " pp_expr e

let rec pp_stat ind fmt s =
  match s with
  | T_expr e -> pp_expr_ext fmt e
  | T_assign (lval, rval) ->
      Format.fprintf fmt "%a = %a" pp_expr_ext lval pp_expr_ext rval
  | T_call (f, _) ->
      (match f.func_return with
      | Some v -> Format.fprintf fmt "%a = " print_var_name v
      | None -> ());
      Format.fprintf fmt "%a(" print_func_name f;
      print_list print_var_name "," fmt f.func_args;
      Format.pp_print_string fmt ")"
  | T_if (e, b1, b2) ->
      Format.fprintf fmt "if (%a)@\n" pp_expr_ext e;
      pp_block_with_ind ind fmt b1;
      Format.fprintf fmt "%selse@\n" ind;
      pp_block_with_ind ind fmt b2
  | T_while (lbl, e, b) ->
      Format.fprintf fmt "while %a (%a)@\n" pp_label lbl pp_expr_ext e;
      pp_block_with_ind ind fmt b
  | T_add_var (v, eo) -> (
      Format.fprintf fmt "%s%s %a"
        (match v.var_scope with
        | T_INPUT -> "input "
        | T_VOLATILE -> "volatile "
        | _ -> "")
        (string_of_typ v.var_typ) print_var_name v;
      match eo with
      | Some e -> Format.fprintf fmt " = %a" pp_expr_ext e
      | None -> ())
  | T_del_var v -> Format.fprintf fmt "delete %a" print_var_name v
  | T_RETURN -> Format.pp_print_string fmt "return"
  | T_BREAK -> Format.pp_print_string fmt "break"
  | T_label (s, _) -> Format.fprintf fmt "%s:" s
  | T_assert (e, lbl) ->
      Format.fprintf fmt "assert (%a) FALSE_LABEL=%a" pp_expr_ext e pp_label lbl
  | T_assume e -> Format.fprintf fmt "assume (%a)" pp_expr_ext e
  | T_print l ->
      Format.fprintf fmt "print (%a)"
        (print_list print_var_name ",")
        (List.map fst l)

and pp_stat_end ind fmt s =
  pp_stat ind fmt s;
  match s with T_if _ | T_while _ -> () | _ -> Format.fprintf fmt ";@\n"

and pp_block_with_ind ind fmt s =
  let ind2 = ind ^ "  " in
  let rec aux = function
    | T_stat (l, (s, _), r) ->
        Format.fprintf fmt "%s%a %a" ind2 pp_label l (pp_stat_end ind2) s;
        aux r
    | T_empty l -> Format.fprintf fmt "%s%a@\n" ind2 pp_label l
  in
  Format.fprintf fmt "%s{@\n" ind;
  aux s;
  Format.fprintf fmt "%s}@\n" ind

let pp_block = pp_block_with_ind ""

let pp_func fmt f =
  (match f.func_return with
  | None -> Format.pp_print_string fmt "void"
  | Some v -> Format.pp_print_string fmt (string_of_typ v.var_typ));
  Format.fprintf fmt " %a(" print_func_name f;
  print_list
    (fun fmt v ->
      Format.fprintf fmt "%s %a" (string_of_typ v.var_typ) print_var_name v)
    "," fmt f.func_args;
  Format.pp_print_string fmt ")@\n";
  pp_block fmt f.func_body

let pp_prog fmt (init, funcs, _) =
  pp_block fmt init;
  StringMap.iter (fun _ -> pp_func fmt) funcs;
  Format.pp_print_flush fmt ()

(************************************************************************)
(* EXPRESSION UNBOXING *)
(************************************************************************)

let unbox_un (op : unary_op) (e : expr) : expr option =
  match e with T_unary (eop, (e, _, _)) when eop = op -> Some e | _ -> None

let unbox_un_plus = unbox_un A_UNARY_PLUS
let unbox_un_minus = unbox_un A_UNARY_MINUS
let unbox_not = unbox_un A_NOT

let unbox_cast (e : expr) : (expr * typ) option =
  match e with T_unary (A_cast (t, _), (e, _, _)) -> Some (e, t) | _ -> None

let unbox_bin_op (op : binary_op) (e : expr) : (expr * expr) option =
  match e with
  | T_binary (eop, (e1, _, _), (e2, _, _)) when eop = op -> Some (e1, e2)
  | _ -> None

let unbox_bin_plus = unbox_bin_op A_PLUS
let unbox_bin_minus = unbox_bin_op A_MINUS
let unbox_mul = unbox_bin_op A_MULTIPLY
let unbox_div = unbox_bin_op A_DIVIDE
let unbox_mod = unbox_bin_op A_MODULO
let unbox_eq = unbox_bin_op A_EQUAL
let unbox_neq = unbox_bin_op A_NOT_EQUAL
let unbox_lt = unbox_bin_op A_LESS
let unbox_leq = unbox_bin_op A_LESS_EQUAL
let unbox_gt = unbox_bin_op A_GREATER
let unbox_geq = unbox_bin_op A_GREATER_EQUAL
let unbox_and = unbox_bin_op A_AND
let unbox_or = unbox_bin_op A_OR

let unbox_float_const (e : expr) : float_set option =
  match e with T_float_const f -> Some f | _ -> None

let unbox_int_const (e : expr) : int_set option =
  match e with T_int_const i -> Some i | _ -> None

let unbox_bool_const (e : expr) : bool_set option =
  match e with T_bool_const b -> Some b | _ -> None

let unbox_var (e : expr) : var option =
  match e with T_var v -> Some v | _ -> None

(************************************************************************)
(* POINTER ARITHMETICS *)
(************************************************************************)
let deref_typ (t : typ) : typ =
  match t with
  | A_pointer typ -> typ
  | _ -> raise (Invalid_argument "derefence of scalar value")

(************************************************************************)
(* PREDICATES *)
(************************************************************************)

let prog_contains_loops ((b, funcs, _) : prog) : bool =
  let rec stat_contains_loops (s : stat) : bool =
    match s with
    | T_expr _ | T_assign _ | T_call _ | T_add_var _ | T_del_var _ | T_RETURN
    | T_BREAK | T_assert _ | T_assume _ | T_print _ | T_label _ ->
        false
    | T_if (_, b1, b2) -> block_contains_loops b1 || block_contains_loops b2
    | T_while _ -> true
  and block_contains_loops (b : block) : bool =
    match b with
    | T_empty _ -> false
    | T_stat (_, (s, _), b) -> stat_contains_loops s || block_contains_loops b
  in

  StringMap.exists (fun _ f -> block_contains_loops f.func_body) funcs
  || block_contains_loops b

(************************************************************************)
(* MODIFIERS *)
(************************************************************************)

let nt_prog ((b, funcs, v) : prog) : prog * label list =
  let lnew = ref [] in
  let rec nt_stat (s : stat) : stat =
    match s with
    | T_expr _ | T_assign _ | T_add_var _ | T_del_var _ | T_RETURN | T_BREAK
    | T_assert _ | T_assume _ | T_print _ | T_label _ ->
        s
    | T_if (e, b1, b2) ->
        let b1 = nt_block b1 in
        let b2 = nt_block b2 in
        T_if (e, b1, b2)
    | T_while (l, e, b) ->
        let b = nt_block b in
        let id = new_id () in
        let label = (id, position_unknown) in
        lnew := label :: !lnew;
        let block =
          T_stat (label, (T_label ("loop", extent_unknown), extent_unknown), b)
        in
        T_while (l, e, block)
    | T_call (f, ss) ->
        let f = { f with func_body = nt_block f.func_body } in
        T_call (f, ss)
  and nt_block (b : block) : block =
    match b with
    | T_empty _ -> b
    | T_stat (l, (s, ext), b) ->
        let s = nt_stat s in
        let b = nt_block b in
        T_stat (l, (s, ext), b)
  in
  let f =
    StringMap.update !Config.main
      (Option.map (fun f -> { f with func_body = nt_block f.func_body }))
      funcs
  in
  let p : prog = (b, f, v) in
  (p, !lnew)

(* invert a comparison expression *)
let invert_comp_expr ((e, t, x) as ee : expr typed) : expr typed =
  let e =
    match e with
    | T_binary (A_EQUAL, e1, e2) -> T_binary (A_NOT_EQUAL, e1, e2)
    | T_binary (A_NOT_EQUAL, e1, e2) -> T_binary (A_EQUAL, e1, e2)
    | T_binary (A_LESS, e1, e2) -> T_binary (A_GREATER_EQUAL, e1, e2)
    | T_binary (A_LESS_EQUAL, e1, e2) -> T_binary (A_GREATER, e1, e2)
    | T_binary (A_GREATER, e1, e2) -> T_binary (A_LESS_EQUAL, e1, e2)
    | T_binary (A_GREATER_EQUAL, e1, e2) -> T_binary (A_LESS, e1, e2)
    | _ ->
        raise
          (Invalid_argument
             (Format.asprintf "%s: not comparison op in expr: %a" __LOC__
                pp_expr_ext ee))
  in
  (e, t, x)

let rec neg_bexp (b, t, x) =
  match b with
  | T_bool_const True -> (T_bool_const False, t, x)
  | T_bool_const Maybe -> (T_bool_const Maybe, t, x)
  | T_bool_const False -> (T_bool_const True, t, x)
  | T_var _ | T_int_const _ ->
      ( T_binary
          ( A_NOT_EQUAL,
            (b, t, x),
            (T_int_const (Intinf.zero, Intinf.zero), t, x) ),
        t,
        x )
  | T_binary (A_AND, e1, e2) -> (T_binary (A_OR, neg_bexp e1, neg_bexp e2), t, x)
  | T_binary (A_OR, e1, e2) -> (T_binary (A_AND, neg_bexp e1, neg_bexp e2), t, x)
  | T_binary (op, e1, e2) -> invert_comp_expr (b, t, x)
  | T_unary (A_NOT, e) -> e
  | _ -> raise (Invalid_argument "Unexpected rvalue")

let is_var e = match e with T_var _ -> true | _ -> false

let is_var2 e1 e2 =
  match (e1, e2) with T_var _, T_var _ -> true | _, _ -> false

let rec expr_is_linear e =
  match e with
  | T_unary (op, (e, _, _)) -> expr_is_linear e
  | T_binary (op, (e1, _, _), (e2, _, _)) -> (
      match op with
      | A_MULTIPLY | A_MODULO | A_DIVIDE ->
          expr_is_linear e1 && expr_is_linear e2 && not (is_var2 e1 e2)
      | _ -> expr_is_linear e1 && expr_is_linear e2)
  | _ -> true

let rec expr_is_univariate e =
  match e with
  | T_unary (op, (e, _, _)) -> expr_is_univariate e
  | T_binary (op, (e1, _, _), (e2, _, _)) ->
      expr_is_univariate e1 && expr_is_univariate e2 && not (is_var2 e1 e2)
  | _ -> true

(* [unit_vars e] returns the variables of the arithmetic expression [e] with
   their sign, when [e] is a sum of constants and of variables with coefficient
   +1 or -1, each variable occurring once; [None] otherwise. *)
let rec unit_vars e =
  let combine s (e1, _, _) (e2, _, _) =
    match (unit_vars e1, unit_vars e2) with
    | Some l1, Some l2 ->
        let l2 = List.map (fun (v, k) -> (v, s * k)) l2 in
        let mem (v, _) = List.exists (fun (w, _) -> w.var_id = v.var_id) l1 in
        if List.exists mem l2 then None
        else Some (l1 @ l2)
    | _ -> None
  in
  match e with
  | T_int_const _ -> Some []
  | T_var v -> Some [ (v, 1) ]
  | T_unary (A_UNARY_PLUS, (e, _, _)) -> unit_vars e
  | T_unary (A_UNARY_MINUS, (e, _, _)) ->
      Option.map (List.map (fun (v, k) -> (v, -k))) (unit_vars e)
  | T_binary (A_PLUS, e1, e2) -> combine 1 e1 e2
  | T_binary (A_MINUS, e1, e2) -> combine (-1) e1 e2
  | _ -> None

(* [expr_is_octagonal e] tests if [e] fits the octagon domain: a condition
   whose sides differ by at most two variables of coefficient +1/-1, or an
   arithmetic expression with at most one such variable (so that [x := e] is
   octagonal). *)
let rec expr_is_octagonal e =
  let at_most n = function Some l -> List.length l <= n | None -> false in
  match e with
  | T_bool_const _ -> true
  | T_unary (A_NOT, (e, _, _)) -> expr_is_octagonal e
  | T_binary ((A_AND | A_OR), (e1, _, _), (e2, _, _)) ->
      expr_is_octagonal e1 && expr_is_octagonal e2
  | T_binary
      ( ( A_EQUAL | A_NOT_EQUAL | A_LESS | A_LESS_EQUAL | A_GREATER
        | A_GREATER_EQUAL ),
        e1,
        e2 ) ->
      at_most 2 (unit_vars (T_binary (A_MINUS, e1, e2)))
  | e -> at_most 1 (unit_vars e)

(************************************************************************)
(* MISC *)
(************************************************************************)

(* name of specially inserted labels *)

let break_label (id, _) = string_of_id "break#" id
let return_label id = string_of_id "return#" id
let assert_label (id, _) = string_of_id "assert_false#" id
let prog_literals = ref IdSet.empty

let add_prog_literal (cst : Int.t) =
  prog_literals := IdSet.add cst !prog_literals

let expr_prop_handler e vars =
  let rec aux e =
    match e with
    | T_var v, t, ext ->
        ( T_var
            (List.find (fun x -> String.compare x.var_name v.var_name = 0) vars),
          t,
          ext )
    | T_unary (op, e), t, ext -> (T_unary (op, aux e), t, ext)
    | T_binary (bop, e1, e2), t, ext -> (T_binary (bop, aux e1, aux e2), t, ext)
    | _ -> e
  in
  aux e
