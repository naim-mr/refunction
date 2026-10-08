(*
   Conversion from Abstract_syntax to Typed_syntax.

   Should catch all unknown identifiers, syntax, and typing errors.
   Side-effects in expressions are evaluated left to right.

   Copyright (C) 2011 Antoine Miné
*)

open Utils.Datatypes
open Abstract_syntax
open Typed_syntax
open Utils

(************************************************************************)
(* UTILITIES *)
(************************************************************************)

exception Translate_error of extent * string

(*
let error x =
  Printf.ksprintf
    (fun s -> failwith (Printf.sprintf "%s: error: %s" (string_of_extent x) s))
*)
let error x = Printf.ksprintf (fun s -> raise (Translate_error (x, s)))

(* relative size of int / float *)

let int_rank i s =
  match i with
  | A_CHAR -> 1
  | A_SHORT -> 3
  | A_INT -> 5
  | A_LONG -> 7
  | A_INTEGER -> 99
  | A_DYNINT _ ->
      let itv = Value_semantics.int_type_set i s in
      if Itv_int.subseteq itv (Value_semantics.int_type_set A_CHAR s) then 0
      else if Itv_int.subseteq itv (Value_semantics.int_type_set A_SHORT s) then
        2
      else if Itv_int.subseteq itv (Value_semantics.int_type_set A_INT s) then 4
      else if Itv_int.subseteq itv (Value_semantics.int_type_set A_LONG s) then
        6
      else 8

let float_rank = function A_FLOAT -> 1 | A_DOUBLE -> 2 | A_REAL -> 99

let new_var name synthetic x typ scope =
  let id = new_id () in
  let n = if synthetic then string_of_id name id else name in
  {
    var_name = n;
    var_extent = x;
    var_id = id;
    var_typ = typ;
    var_synthetic = synthetic;
    var_scope = scope;
  }

(************************************************************************)
(* ENVIRONMENT *)
(************************************************************************)

type env = {
  (* Function in which we are to detect recursive calls *)
  env_call_ctx : lvalue;
  (* note: synthetic variables are not in env *)
  env_locals : var StringMap.t;
  env_globals : var StringMap.t;
  (* all functions and variables declared *)
  env_funcs : func StringMap.t;
  env_vars : var IdMap.t;
  (* where to store the value of a "return" statement *)
  env_return : var option;
}

let empty_env =
  {
    env_call_ctx = "init";
    env_locals = StringMap.empty;
    env_globals = StringMap.empty;
    env_funcs = StringMap.empty;
    env_vars = IdMap.empty;
    env_return = None;
  }

(* resolve identifiers *)

let get_var env v x =
  try StringMap.find v env.env_locals
  with Not_found -> (
    try StringMap.find v env.env_globals
    with Not_found -> error x "unknown identifier %s" v)

let get_func env v x =
  try StringMap.find v env.env_funcs
  with Not_found -> error x "unknown function %s" v

(************************************************************************)
(* CASTS *)
(************************************************************************)

let cast ((e, t, _) as ee) t' x =
  if t = t' then ee
  else (
    if t = A_BOOL || t' = A_BOOL then
      error x "invalid cast, from %s to %s" (string_of_typ t) (string_of_typ t');
    match (e, t') with
    (* don't cast constants if they fit the target type *)
    | T_int_const (i1, i2), A_int (c, s)
      when Value_semantics.const_fit_in_type c s i1
           && Value_semantics.const_fit_in_type c s i2 ->
        ee
    | _ -> (T_unary (A_cast (t', x), ee), t', x))

let as_bool ((_, t, x) as ee) =
  if t <> A_BOOL then
    error x "boolean expression expected, found %s" (string_of_typ t);
  ee

(* promotes to signed int, if fits in it *)
let as_int ((_, t, x) as ee) =
  match t with
  | A_int ((A_CHAR | A_SHORT), _) -> cast ee (A_int (A_INT, A_SIGNED)) x
  | A_int _ -> ee
  | A_float _ -> ee
  | _ -> error x "integer expression expected, found %s" (string_of_typ t)

(* int or float *)
let as_num ((_, t, x) as ee) =
  match t with
  | A_float _ -> ee
  | A_int _ -> as_int ee
  | _ ->
      error x "integer or float expression expected, found %s" (string_of_typ t)

(* cast to a common type *)
let promote_compatible ((_, t1, x1) as ee1) ((_, t2, x2) as ee2) x =
  let t =
    match (t1, t2) with
    | A_BOOL, A_BOOL -> A_BOOL
    | A_float f1, A_float f2 -> if float_rank f1 > float_rank f2 then t1 else t2
    | A_float _, A_int _ -> t1
    | A_int _, A_float _ -> t2
    | A_int (i1, s1), A_int (i2, s2) ->
        let i1, s1 =
          if int_rank i1 s1 < int_rank A_INT A_SIGNED then (A_INT, A_SIGNED)
          else (i1, s1)
        and i2, s2 =
          if int_rank i2 s2 < int_rank A_INT A_SIGNED then (A_INT, A_SIGNED)
          else (i2, s2)
        in
        if int_rank i1 s1 < int_rank i2 s2 then A_int (i2, s2)
        else if int_rank i1 s1 > int_rank i2 s2 then A_int (i1, s1)
        else if s1 = s2 then A_int (i1, s1)
        else A_int (i1, if i1 = A_INTEGER then A_SIGNED else A_UNSIGNED)
    | _ ->
        error x "incompatible operand types, %s and %s in expressions %s and %s"
          (string_of_typ t1) (string_of_typ t2)
          (Format.asprintf "%a" pp_expr_ext ee1)
          (Format.asprintf "%a" pp_expr_ext ee2)
  in
  (cast ee1 t x1, cast ee2 t x2, t)

(************************************************************************)
(* TRANSLATION *)
(************************************************************************)

(* expressions *)
(* *********** *)

(* returns an expression free of side-effect;
   side-effects are accumulated in pre / post;
   pre may create temp variables, which are deleted in post;
*)
let rec pure_expr env pre post (e, x) =
  match e with
  | A_identifier s ->
      let v = get_var env s x in
      ((T_var v, v.var_typ, x), pre, post)
  | A_INPUT (id, Some ((min, _), (max, _))) ->
      let i1, i2 = (Int.of_string min, Int.of_string max) in
      add_prog_literal i1;
      add_prog_literal i2;
      let t =
        if Int.fits_int32 i1 && Int.fits_int32 i2 then A_int (A_INT, A_SIGNED)
        else if Int.fits_int64 i1 && Int.fits_int64 i2 then
          A_int (A_LONG, A_SIGNED)
        else A_int (A_INTEGER, A_SIGNED)
      in
      ( (T_input (id, (Finite i1, Finite i2)), A_int (A_INT, A_SIGNED), x),
        pre,
        post )
  | A_INPUT (id, None) ->
      ((T_input (id, (MINF, INF)), A_int (A_INT, A_SIGNED), x), pre, post)
  | A_float_const s ->
      (* always double type *)
      (* TODO: return a sound interval enclosing the decimal literal *)
      let f = Float.of_string s in
      ((T_float_const (f, f), A_float A_DOUBLE, x), pre, post)
  | A_int_const s ->
      let i = Int.of_string s in
      add_prog_literal i;
      (* try these types in order: int, long, integer *)
      let t =
        if Int.fits_int32 i then A_int (A_INT, A_SIGNED)
        else if Int.fits_int64 i then A_int (A_LONG, A_SIGNED)
        else A_int (A_INTEGER, A_SIGNED)
      in
      ((T_int_const (Finite i, Finite i), t, x), pre, post)
  | A_float_itv ((s1, _), (s2, _)) ->
      let f1, f2 = (Float.of_string s1, Float.of_string s2) in
      ((T_float_const (f1, f2), A_float A_DOUBLE, x), pre, post)
  | A_int_itv ((s1, _), (s2, _)) ->
      let i1, i2 = (Int.of_string s1, Int.of_string s2) in
      add_prog_literal i1;
      add_prog_literal i2;
      let t =
        if Int.fits_int32 i1 && Int.fits_int32 i2 then A_int (A_INT, A_SIGNED)
        else if Int.fits_int64 i1 && Int.fits_int64 i2 then
          A_int (A_LONG, A_SIGNED)
        else A_int (A_INTEGER, A_SIGNED)
      in
      ((T_int_const (Finite i1, Finite i2), t, x), pre, post)
  | A_nondet t -> ((Value_semantics.type_set_expr t, t, x), pre, post)
  | A_bool_const b -> ((T_bool_const (tbool_of_bool b), A_BOOL, x), pre, post)
  | A_unary (op, e1) -> (
      let e1, pre, post = pure_expr env pre post e1 in
      match op with
      | A_UNARY_PLUS -> (as_num e1, pre, post)
      | A_UNARY_MINUS ->
          let ((_, t, _) as e1) = as_num e1 in
          ((T_unary (op, e1), t, x), pre, post)
      | A_NOT -> ((T_unary (op, as_bool e1), A_BOOL, x), pre, post)
      | A_cast (t', x) -> (cast e1 t' x, pre, post))
  | A_binary (op, e1, e2) -> (
      let e1, pre, post = pure_expr env pre post e1 in
      let e2, pre, post = pure_expr env pre post e2 in
      match op with
      | A_PLUS | A_MINUS | A_MULTIPLY | A_DIVIDE ->
          let e1, e2, t = promote_compatible (as_num e1) (as_num e2) x in
          ((T_binary (op, e1, e2), t, x), pre, post)
      | A_MODULO ->
          let e1, e2, t = promote_compatible (as_int e1) (as_int e2) x in
          ((T_binary (op, e1, e2), t, x), pre, post)
      | A_LESS | A_LESS_EQUAL | A_GREATER | A_GREATER_EQUAL ->
          let e1, e2, _ = promote_compatible (as_num e1) (as_num e2) x in
          ((T_binary (op, e1, e2), A_BOOL, x), pre, post)
      | A_EQUAL | A_NOT_EQUAL ->
          let e1, e2, _ = promote_compatible e1 e2 x in
          ((T_binary (op, e1, e2), A_BOOL, x), pre, post)
      | A_AND | A_OR ->
          (* TODO: shortcut && and || *)
          let e1, e2 = (as_bool e1, as_bool e2) in
          ((T_binary (op, e1, e2), A_BOOL, x), pre, post))
  | A_call ((s, sx), args) -> (
      let ee, pre, post = call (s, sx) args env pre post x in
      match ee with
      | None -> error x "function %s has no return value" s
      | Some ee -> (ee, pre, post))
  | A_increment (l, i, A_PRE) ->
      (* ++x, --x => x+=1, x-=1 *)
      let op =
        match i with A_INCR -> A_PLUS_ASSIGN | A_DECR -> A_MINUS_ASSIGN
      in
      let e = (A_assign (l, Some op, (A_int_const "1", x)), x) in
      pure_expr env pre post e
  | A_increment (l, i, A_POST) ->
      (* as ++x, --x, but appends effect after expression evaluation *)
      let op =
        match i with A_INCR -> A_PLUS_ASSIGN | A_DECR -> A_MINUS_ASSIGN
      in
      let e = (A_assign (l, Some op, (A_int_const "1", x)), x) in
      let ee, pre1, post1 = pure_expr env [] [] e in
      (ee, pre, pre1 @ post1 @ post)
  | A_assign ((lval, ext), op, (e, ex)) -> (
      (* optionally translate into v = v op e *)
      let e =
        match op with
        | None -> e
        | Some A_PLUS_ASSIGN -> A_binary (A_PLUS, (lval, ext), (e, ex))
        | Some A_MINUS_ASSIGN -> A_binary (A_MINUS, (lval, ext), (e, ex))
        | Some A_MULTIPLY_ASSIGN -> A_binary (A_MULTIPLY, (lval, ext), (e, ex))
        | Some A_DIVIDE_ASSIGN -> A_binary (A_DIVIDE, (lval, ext), (e, ex))
        | Some A_MODULO_ASSIGN -> A_binary (A_MODULO, (lval, ext), (e, ex))
      in
      let ee, pre1, post1 = pure_expr env [] [] (e, ex) in
      (* cast back to the type of v *)
      match lval with
      | A_identifier s ->
          let v = get_var env s ext in
          if v.var_scope = T_INPUT then
            error x "%s is an input and cannot be assigned" s;
          if v.var_scope = T_VOLATILE then
            error x "%s is a volatile and cannot be assigned" s;
          let ee = cast ee v.var_typ x in
          (* pre = assign variable, expr = variable *)
          ( (T_var v, v.var_typ, x),
            pre @ pre1 @ [ (T_assign ((T_var v, v.var_typ, x), ee), x) ] @ post1,
            post )
      | A_deref (A_identifier s) ->
          let v = get_var env s ext in
          if v.var_scope = T_INPUT then
            error x "%s is an input and cannot be assigned" s;
          if v.var_scope = T_VOLATILE then
            error x "%s is a volatile and cannot be assigned" s;
          let v =
            {
              v with
              var_name = Printf.sprintf "*%s" v.var_name;
              var_typ = Typed_syntax.deref_typ v.var_typ;
            }
          in
          let ee = cast ee v.var_typ x in
          ( (T_var v, v.var_typ, x),
            pre @ pre1 @ [ (T_assign ((T_var v, v.var_typ, x), ee), x) ] @ post1,
            post )
      | _ -> failwith "neti")
  | A_deref e ->
      let (ee, typ, ext), pre, post = pure_expr env pre post (e, x) in
      ((T_deref (ee, typ, ext), Typed_syntax.deref_typ typ, ext), pre, post)
  | A_address_of e ->
      let (ee, typ, ext), pre, post = pure_expr env pre post (e, x) in
      ((T_deref (ee, typ, ext), A_pointer typ, ext), pre, post)

and call (s, sx) args env pre post x =
  (* resolve identifier *)
  let f = get_func env s sx in
  (* translate & bind actual arguments *)
  if List.length args <> List.length f.func_args then
    error x "the function expects %i arguments, got %i"
      (List.length f.func_args) (List.length args);
  let pre', post' =
    List.fold_left2
      (fun (pre, post) e v ->
        let ee, pre', post' = pure_expr env [] [] e in
        let ee = cast ee v.var_typ x in
        ( pre @ pre' @ [ (T_add_var (v, Some ee), x) ] @ post',
          [ (T_del_var v, x) ] @ post ))
      ([], []) args f.func_args
  in
  (* handle return value *)
  match f.func_return with
  | None ->
      (* function without return *)
      (None, pre @ pre' @ [ (T_call (f, sx), x) ] @ post', post)
  | Some v ->
      (* function with return value *)
      let v1 = new_var "__returned" true x v.var_typ T_LOCAL in
      (* note: all the formal argument and return variables are deleted
         just after the call;
         the actual argument is copied into a temporary v1 to be used by the
         expression, thus, an expression can safely call the same function
         several times without conflicts in formal arguemnt and return
         variables
      *)
      ( Some (T_var v1, v.var_typ, x),
        pre @ pre'
        @ [
            (T_add_var (v1, None), x);
            (T_add_var (v, None), x);
            (T_call (f, sx), x);
            (T_assign ((T_var v1, v.var_typ, x), (T_var v, v.var_typ, x)), x);
            (T_del_var v, x);
          ]
        @ post',
        [ (T_del_var v1, x) ] @ post )

(* variable declaration and initialisation *)
and add_var env (t, _) (s, sx) i scope =
  let v = new_var s false sx t scope in
  let i =
    match i with
    | None -> [ (T_add_var (v, None), sx) ]
    | Some (e, x) ->
        let ee, pre, post = pure_expr env [] [] (e, x) in
        let ee = cast ee v.var_typ x in
        pre @ [ (T_add_var (v, Some ee), sx) ] @ post
  in
  let env =
    {
      env with
      env_locals =
        (if scope = T_LOCAL then StringMap.add s v env.env_locals
         else env.env_locals);
      env_globals =
        (if scope <> T_LOCAL then StringMap.add s v env.env_globals
         else env.env_globals);
      env_vars = IdMap.add v.var_id v env.env_vars;
    }
  in
  (env, v, i)

(* statements *)
(* ********** *)

(* block from statement list: adds unique labels *)
let mk_block l locs x =
  let rec aux l acc =
    match l with
    | [] -> acc
    | (lbl, s, x) :: l -> aux l (T_stat ((lbl, fst x), (s, x), acc))
  in
  let del =
    List.rev_map (fun v -> (new_id (), T_del_var v, (snd x, snd x))) locs
  in
  aux (del @ List.rev l) (T_empty (new_id (), snd x))

let add_lbl l = List.map (fun (a, b) -> (new_id (), a, b)) l

(* translate a statement;
   also returns the set of created local variables, for easy destruction
*)
let rec stat env (e, x) =
  match e with
  | A_SKIP -> (env, [], [])
  | A_expr (A_call ((s, sx), args), x) ->
      let env = { env with env_call_ctx = s } in
      (* unlike pure_expr, does not fail if there is no return value *)
      let _, pre, post = call (s, sx) args env [] [] x in
      (env, add_lbl (pre @ post), [])
  | A_expr (e1, x) ->
      let _, pre, post = pure_expr env [] [] (e1, x) in
      (env, add_lbl (pre @ post), [])
  | A_if (e1, s1, s2) ->
      let ee, pre, post = pure_expr env [] [] e1 in
      let pre = add_lbl pre in
      let lbl = new_id () in
      let ee = as_bool ee in
      let env', u1, l1 = stat env s1 in
      let b1 = mk_block (add_lbl post @ u1) l1 (snd s1) in
      let env', b2 =
        match s2 with
        | None -> (env', mk_block (add_lbl post) [] (snd s1))
        | Some s2 ->
            let env', u2, l2 = stat env' s2 in
            (env', mk_block (add_lbl post @ u2) l2 (snd s2))
      in
      ( { env with env_vars = env'.env_vars },
        pre @ [ (lbl, T_if (ee, b1, b2), x) ],
        [] )
  | A_while (e1, s1) ->
      let ee, pre, post = pure_expr env [] [] e1 in
      let ((_, _, xx) as ee) = as_bool ee in
      let pre = add_lbl pre in
      let lbl = new_id () in
      let lbl2 = (new_id (), fst xx) in
      let env', u1, l1 = stat env s1 in
      let b1 = mk_block (add_lbl post @ u1) l1 (snd s1) in
      let lbl3 = new_id () in
      ( { env with env_vars = env'.env_vars },
        pre
        @ [
            (lbl, T_while (lbl2, ee, b1), x);
            (lbl3, T_label (break_label lbl2, x), x);
          ],
        [] )
  | A_BREAK -> (env, [ (new_id (), T_BREAK, x) ], [])
  | A_return None -> (env, [ (new_id (), T_RETURN, x) ], [])
  | A_return (Some e1) -> (
      let ee, pre, post = pure_expr env [] [] e1 in
      let pre = add_lbl pre in
      let lbl = new_id () in
      let lbl2 = new_id () in
      let post = add_lbl post in
      match env.env_return with
      | None -> error x "function cannot return a value"
      | Some v ->
          let ee = cast ee v.var_typ x in
          ( env,
            pre
            @ [
                (lbl, T_assign ((T_var v, v.var_typ, x), ee), x);
                (lbl2, T_RETURN, x);
              ]
            @ post,
            [] ))
  | A_block l ->
      let env', r, locs' = stat_list env l in
      let del = List.map (fun v -> (T_del_var v, x)) locs' in
      ({ env with env_vars = env'.env_vars }, r @ add_lbl del, [])
  | A_local (t, l) ->
      let env, rstats, locs =
        List.fold_left
          (fun (env, rstats, locs) (n, i) ->
            let env, v, i = add_var env t n i T_LOCAL in
            (env, List.rev_append i rstats, v :: locs))
          (env, [], []) l
      in
      (env, add_lbl (List.rev rstats), locs)
  | A_label (s, e) -> (env, [ (new_id (), T_label (s, e), x) ], [])
  | A_assert e ->
      let ee, pre, post = pure_expr env [] [] e in
      let ((_, _, xx) as ee) = as_bool ee in
      let pre = add_lbl pre in
      let lbl = new_id () in
      let lbl2 = (new_id (), fst xx) in
      let post = add_lbl post in
      let ee = as_bool ee in
      (env, pre @ [ (lbl, T_assert (ee, lbl2), x) ] @ post, [])
  | A_assume e ->
      let ee, pre, post = pure_expr env [] [] e in
      let pre = add_lbl pre in
      let lbl = new_id () in
      let post = add_lbl post in
      let ee = as_bool ee in
      (env, pre @ [ (lbl, T_assume ee, x) ] @ post, [])
  | A_print l ->
      let l = List.map (fun (s, x) -> (get_var env s x, x)) l in
      (env, [ (new_id (), T_print l, x) ], [])

and stat_list env l =
  let env, rstats, rlocs =
    List.fold_left
      (fun (env, rstats, rlocs) s ->
        let env, stats, locs = stat env s in
        (env, List.rev_append stats rstats, List.rev_append locs rlocs))
      (env, [], []) l
  in
  (env, List.rev rstats, List.rev rlocs)

(* declarations *)
(* ************ *)

let decl env d =
  match d with
  | A_global (((t, l), _), kind) ->
      let scope =
        match kind with
        | A_VARIABLE -> T_GLOBAL
        | A_INPUT -> T_INPUT
        | A_VOLATILE -> T_VOLATILE
      in
      let env, rstats =
        List.fold_left
          (fun (env, rstats) (n, i) ->
            let env, _, i = add_var env t n i scope in
            (env, List.rev_append i rstats))
          (env, []) l
      in
      (env, List.rev rstats, [])
  | A_function ((r, (s, sx), args, body), x) ->
      let fid = new_id () in
      let ret =
        match r with
        | None -> None
        | Some (t, _) -> Some (new_var "__return" true x t T_LOCAL)
      in
      let env_body = { env with env_return = ret; env_call_ctx = s } in
      let args, env_body =
        List.fold_left
          (fun (args, env) ((s, sx), (t, _)) ->
            let v = new_var s false sx t T_LOCAL in
            ( v :: args,
              {
                env with
                env_locals = StringMap.add s v env.env_locals;
                env_vars = IdMap.add v.var_id v env.env_vars;
              } ))
          ([], env_body) (List.rev args)
      in
      let env', r, locs = stat_list env_body body in
      let rlbl = new_id () in
      let xx = (snd x, snd x) in
      let r = r @ [ (rlbl, T_label (return_label fid, xx), xx) ] in
      let b = mk_block r locs x in
      let f =
        {
          func_name = s;
          func_extent = sx;
          func_id = fid;
          func_return = ret;
          func_args = args;
          func_body = b;
        }
      in
      ( {
          env with
          env_funcs = StringMap.add s f env.env_funcs;
          env_vars = env'.env_vars;
        },
        [],
        [ f ] )

(************************************************************************)
(* ENTRY POINTS *)
(************************************************************************)

(* translation entry point *)
let translate_program (input_vars : decl list) (global : decl list)
    (funcs : decl list) : prog =
  let ps =
    [ (input_vars @ global @ funcs, (Lexing.dummy_pos, Lexing.dummy_pos)) ]
  in
  let env =
    List.fold_left
      (fun env d ->
        match d with
        | A_global (((t, l), _), kind) -> env
        | A_function ((r, (s, sx), args, body), x) ->
            let fid = new_id () in
            let ret =
              match r with
              | None -> None
              | Some (t, _) -> Some (new_var "__return" true x t T_LOCAL)
            in
            let env_body = { env with env_return = ret } in
            let args, env_body =
              List.fold_left
                (fun (args, env) ((s, sx), (t, _)) ->
                  let v = new_var s false sx t T_LOCAL in
                  ( v :: args,
                    {
                      env with
                      env_locals = StringMap.add s v env.env_locals;
                      env_vars = IdMap.add v.var_id v env.env_vars;
                    } ))
                ([], env_body) (List.rev args)
            in
            let f =
              {
                func_name = s;
                func_extent = sx;
                func_id = fid;
                func_return = ret;
                func_args = args;
                func_body = T_empty (dummy_id, Lexing.dummy_pos);
              }
            in
            { env with env_funcs = StringMap.add s f env.env_funcs })
      empty_env funcs
  in
  let x = snd (List.hd ps) in
  let env, rstats, rfuncs =
    List.fold_left
      (fun (env, rstats, rfuncs) (p, _) ->
        List.fold_left
          (fun (env, rstats, rfuncs) d ->
            let env, stats, funcs = decl env d in
            let stats = add_lbl stats in
            (env, List.rev_append stats rstats, List.rev_append funcs rfuncs))
          (env, rstats, rfuncs) p)
      (env, [], []) ps
  in
  let init = mk_block (List.rev rstats) [] x in
  let funcs =
    List.fold_left
      (fun acc f -> StringMap.add f.func_name f acc)
      StringMap.empty rfuncs
  in
  (init, funcs, env.env_vars)
