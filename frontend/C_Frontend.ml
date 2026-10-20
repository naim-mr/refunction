open Mopsa_c_parser
open Mopsa_c_parser.Clang_to_C
open Mopsa_c_parser.Clang_parser
open Mopsa_c_parser.C_parser
open Utils
open Datatypes

type kind_hint = H_BOOL | H_INT | H_VOID | H_PTR of kind_hint

let skip_funcs =
  StringSet.of_list
    [
      "assume_abort_if_not";
      "__assert_fail";
      "__assert_perror_fail";
      "__assert";
      "__VERIFIER_assert";
      "reach_error";
    ]

(** NON-DETERMINISTIC FUNCTIONS TO TYPE AND HINT *)
let nondet_func_type_hint =
  StringMap.empty
  |> StringMap.add "__VERIFIER_nondet_uchar"
       (Abstract_syntax.(A_int (A_CHAR, A_UNSIGNED)), H_INT)
  |> StringMap.add "__VERIFIER_nondet_ushort"
       (Abstract_syntax.(A_int (A_SHORT, A_UNSIGNED)), H_INT)
  |> StringMap.add "__VERIFIER_nondet_uint"
       (Abstract_syntax.(A_int (A_INT, A_UNSIGNED)), H_INT)
  |> StringMap.add "__VERIFIER_nondet_int"
       (Abstract_syntax.(A_int (A_INT, A_SIGNED)), H_INT)
  |> StringMap.add "rand" (Abstract_syntax.(A_int (A_INT, A_SIGNED)), H_INT)
  |> StringMap.add "__VERIFIER_nondet_uinteger"
       (Abstract_syntax.(A_int (A_INTEGER, A_UNSIGNED)), H_INT)
  |> StringMap.add "__VERIFIER_nondet_integer"
       (Abstract_syntax.(A_int (A_INTEGER, A_SIGNED)), H_INT)
  |> StringMap.add "?" (Abstract_syntax.(A_int (A_INTEGER, A_SIGNED)), H_INT)
  |> StringMap.add "__VERIFIER_nondet_float"
       (Abstract_syntax.A_float A_FLOAT, H_INT)
  |> StringMap.add "__VERIFIER_nondet_double"
       (Abstract_syntax.A_float A_DOUBLE, H_INT)
  |> StringMap.add "__VERIFIER_nondet_bool" (Abstract_syntax.A_BOOL, H_BOOL)

type state = {
  (* list of statements to place in the input block *)
  input_vars : (Abstract_syntax.typ * string * Abstract_syntax.expr) list ref;
}

(** HELPERS *)
let attach_position ast =
  let fake_pos = Lexing.dummy_pos in
  (ast, (fake_pos, fake_pos))

(** AST TRANSLATION *)
let rec convert_type_qual ((typ, _) : C_AST.type_qual) : Abstract_syntax.typ =
  match typ with
  | C_AST.T_bool -> Abstract_syntax.A_BOOL
  | C_AST.T_integer int_type -> (
      match int_type with
      | C_AST.SIGNED_CHAR ->
          A_int (Abstract_syntax.A_CHAR, Abstract_syntax.A_SIGNED)
      | C_AST.SIGNED_SHORT ->
          A_int (Abstract_syntax.A_SHORT, Abstract_syntax.A_SIGNED)
      | C_AST.SIGNED_INT ->
          A_int (Abstract_syntax.A_INT, Abstract_syntax.A_SIGNED)
      | C_AST.SIGNED_LONG ->
          A_int (Abstract_syntax.A_LONG, Abstract_syntax.A_SIGNED)
      | C_AST.SIGNED_LONG_LONG | C_AST.UNSIGNED_LONG_LONG ->
          raise (UnsupportedFeature "long long")
      | C_AST.UNSIGNED_LONG
        (* A_int (Abstract_syntax.A_LONG, Abstract_syntax.A_UNSIGNED) *)
      | C_AST.UNSIGNED_SHORT
        (* A_int (Abstract_syntax.A_SHORT, Abstract_syntax.A_UNSIGNED) *)
      | C_AST.UNSIGNED_CHAR
        (* A_int (Abstract_syntax.A_CHAR, Abstract_syntax.A_UNSIGNED) *)
      | C_AST.UNSIGNED_INT ->
          (* A_int (Abstract_syntax.A_INT, Abstract_syntax.A_UNSIGNED) *)
          raise (UnsupportedConversion "Unsigned integer are supported")
      | C_AST.Char signedness ->
          if signedness = C_AST.UNSIGNED then
            raise (UnsupportedConversion "unsupported int type")
          else A_int (Abstract_syntax.A_CHAR, Abstract_syntax.A_SIGNED)
      | _ -> raise (UnsupportedConversion "unsupported int type"))
  | C_AST.T_float float_type -> (
      match float_type with
      | C_AST.FLOAT -> A_float Abstract_syntax.A_FLOAT
      | C_AST.DOUBLE -> A_float Abstract_syntax.A_DOUBLE
      | C_AST.LONG_DOUBLE ->
          A_float Abstract_syntax.A_DOUBLE (* FIXME -> add this type *)
      | _ -> raise (UnsupportedConversion "unsupported float type"))
  | C_AST.T_pointer (typ, qual) -> A_pointer (convert_type_qual (typ, qual))
  | C_AST.T_array _ -> raise (UnsupportedFeature "array")
  | C_AST.T_record _ -> raise (UnsupportedFeature "struct")
  (* A typedef is only an alias: follow it to the type it denotes instead of
     rejecting it. Benchmarks that #include a standard header (stdio.h, ...)
     drag in typedefs they never actually use in analysed code, and refusing
     them outright made the whole file unanalysable. Unsupported *targets*
     still raise below, so nothing is silently accepted. *)
  | C_AST.T_typedef td -> convert_type_qual td.C_AST.typedef_def
  | _ -> raise (UnsupportedConversion "unsupported type")

let convert_un_op (op : C_AST.unary_operator) : Abstract_syntax.unary_op =
  match op with
  | C_AST.NEG -> Abstract_syntax.A_UNARY_MINUS
  | C_AST.LOGICAL_NOT -> Abstract_syntax.A_NOT
  | _ -> raise (UnsupportedConversion "unsupported unary op")

let un_op_out_hint (op : C_AST.unary_operator) : kind_hint =
  match op with
  | C_AST.NEG -> H_INT
  | C_AST.LOGICAL_NOT -> H_BOOL
  | _ -> raise (UnsupportedConversion "unsupported unary op")

let un_op_in_hint (op : C_AST.unary_operator) : kind_hint =
  match op with
  | C_AST.NEG -> H_INT
  | C_AST.LOGICAL_NOT -> H_BOOL
  | _ -> raise (UnsupportedConversion "unsupported unary op")

let convert_bin_op (op : C_AST.binary_operator) : Abstract_syntax.binary_op =
  match op with
  | C_AST.O_arithmetic op -> (
      match op with
      | C_AST.ADD -> Abstract_syntax.A_PLUS
      | C_AST.SUB -> Abstract_syntax.A_MINUS
      | C_AST.MUL -> Abstract_syntax.A_MULTIPLY
      | C_AST.DIV -> Abstract_syntax.A_DIVIDE
      | C_AST.MOD -> Abstract_syntax.A_MODULO
      | C_AST.RIGHT_SHIFT | C_AST.LEFT_SHIFT ->
          raise (UnsupportedFeature "shift")
      | C_AST.BIT_AND | C_AST.BIT_OR | C_AST.BIT_XOR ->
          raise (UnsupportedFeature "shift"))
  | C_AST.O_logical op -> (
      match op with
      | C_AST.LESS -> Abstract_syntax.A_LESS
      | C_AST.LESS_EQUAL -> Abstract_syntax.A_LESS_EQUAL
      | C_AST.GREATER -> Abstract_syntax.A_GREATER
      | C_AST.GREATER_EQUAL -> Abstract_syntax.A_GREATER_EQUAL
      | C_AST.EQUAL -> Abstract_syntax.A_EQUAL
      | C_AST.NOT_EQUAL -> Abstract_syntax.A_NOT_EQUAL
      | C_AST.LOGICAL_AND -> Abstract_syntax.A_AND
      | C_AST.LOGICAL_OR -> Abstract_syntax.A_OR)

let bin_op_out_hint (op : C_AST.binary_operator) : kind_hint =
  match op with C_AST.O_arithmetic _ -> H_INT | C_AST.O_logical _ -> H_BOOL

let bin_op_in_hint (op : C_AST.binary_operator) : kind_hint =
  match op with
  | C_AST.O_arithmetic _ -> H_INT
  | C_AST.O_logical op -> (
      match op with
      | C_AST.LESS | C_AST.LESS_EQUAL | C_AST.GREATER | C_AST.GREATER_EQUAL
      | C_AST.EQUAL | C_AST.NOT_EQUAL ->
          H_INT
      | C_AST.LOGICAL_AND | C_AST.LOGICAL_OR -> H_BOOL)

let cast_if_necessary (e_hint : kind_hint) (op_in_hint : kind_hint)
    (e : Abstract_syntax.expr) : Abstract_syntax.expr =
  match (op_in_hint, e_hint) with
  | H_BOOL, H_INT ->
      Abstract_syntax.A_binary
        ( Abstract_syntax.A_NOT_EQUAL,
          e |> attach_position,
          Abstract_syntax.A_int_const "0" |> attach_position )
  | H_BOOL, H_BOOL -> e
  | H_INT, H_BOOL -> raise (UnsupportedFeature "bool to int")
  | H_INT, H_INT -> e
  | H_PTR _, _ | _, H_PTR _ -> e
  | _ -> raise (UnsupportedConversion "unexpected hint in cast_if_necessary")

let var_name (var : C_AST.variable) : string = var.var_org_name

let var_typ (var : C_AST.variable) : Abstract_syntax.typ =
  convert_type_qual var.var_type

let rec typ_to_hint (typ : C_AST.typ) : kind_hint =
  match typ with
  | T_integer _ | T_float _ -> H_INT
  | T_bool -> H_BOOL
  | T_void -> H_VOID
  | T_pointer (t, _) -> H_PTR (typ_to_hint t)
  | _ -> raise (UnsupportedConversion "unsupported type in typ_to_hint")

let rec convert_expr (st : state) ((kind, typ, _) : C_AST.expr) :
    Abstract_syntax.expr * kind_hint =
  match kind with
  | C_AST.E_variable var ->
      ( Abstract_syntax.A_identifier (var_name var),
        typ_to_hint (fst var.var_type) )
  | C_AST.E_integer_literal z ->
      (Abstract_syntax.A_int_const (Z.to_string z), H_INT)
  | C_AST.E_float_literal f -> (Abstract_syntax.A_float_const f, H_INT)
  | C_AST.E_unary (op, e) ->
      (* convert int -> bool if necessary (e.g., in !(10+1)) *)
      let e, e_hint = convert_expr st e in
      let e = cast_if_necessary e_hint (un_op_in_hint op) e in

      ( Abstract_syntax.A_unary (convert_un_op op, e |> attach_position),
        un_op_out_hint op )
  | C_AST.E_binary (op, e1, e2) ->
      let e1, e1_hint = convert_expr st e1 in
      let e2, e2_hint = convert_expr st e2 in
      let e1 = cast_if_necessary e1_hint (bin_op_in_hint op) e1 in
      let e2 = cast_if_necessary e2_hint (bin_op_in_hint op) e2 in

      ( Abstract_syntax.A_binary
          (convert_bin_op op, e1 |> attach_position, e2 |> attach_position),
        bin_op_out_hint op )
  | C_AST.E_cast (((_, e_typ, _) as ee), _) ->
      let e_typ = convert_type_qual e_typ in
      let ee = convert_expr st ee |> fst in
      let cast_typ = convert_type_qual typ in
      let hint = fst typ |> typ_to_hint in
      (* if the cast type is the same of the underlying expression, do not emit
         the cast *)
      if cast_typ = e_typ then (ee, hint)
      else
        (* the parser emits some unnecessary casts of constants into integer types
           containing the constant itself. Do not emit them. *)
        let e =
          match (ee, convert_type_qual typ) with
          | Abstract_syntax.A_int_const n, Abstract_syntax.A_int (t, s)
            when Intinf.of_string n |> Value_semantics.const_fit_in_type t s ->
              ee
          | _ ->
              Abstract_syntax.A_unary
                ( Abstract_syntax.A_cast (attach_position e_typ),
                  attach_position ee )
        in
        (e, hint)
  | C_AST.E_call ((e, _, _), args) ->
      (* `e` is an expr. It contains an (implicit) cast and than a E_function
         with the name of the callee function *)
      (* TODO -> check that the cast is compatible with the type of the
         expression *)
      let func_name, func_ret_typ =
        match e with
        | C_AST.E_cast ((e, _, _), _) -> (
            match e with
            | C_AST.E_function func -> (func.func_org_name, func.func_return)
            | _ -> raise (Unexpected "unexpected expr_kind in E_call/E_cast"))
        | _ -> raise (Unexpected "unexpected expr_kind in E_call")
      in
      (* hook the non determinisitc assignement *)
      if StringMap.mem func_name nondet_func_type_hint then (
        (* create a fresh input variable to be placed in the init block*)
        let input_v_name =
          Format.sprintf "nondet_in_%d" (List.length !(st.input_vars) + 1)
        in
        (* get the range of the input variable and the hint type *)
        let typ, hint = StringMap.find func_name nondet_func_type_hint in
        let assign_expr, hint =
          if Array.length args = 0 then (Abstract_syntax.A_nondet typ, hint)
          else (
            assert (Array.length args = 2);
            assert (
              StringMap.find func_name nondet_func_type_hint |> snd = H_INT);
            match (convert_expr st args.(0), convert_expr st args.(1)) with
            | ( (Abstract_syntax.A_int_const l, _),
                (Abstract_syntax.A_int_const h, _) ) ->
                ( Abstract_syntax.A_int_itv
                    (l |> attach_position, h |> attach_position),
                  H_INT )
            | ( (Abstract_syntax.A_float_const l, _),
                (Abstract_syntax.A_float_const h, _) ) ->
                ( Abstract_syntax.A_float_itv
                    (l |> attach_position, h |> attach_position),
                  H_INT )
            | _ ->
                raise
                  (UnsupportedConversion
                     "unexpected kind of arguments of nondet func"))
        in

        (* collect the input variable with its type and initialization *)
        st.input_vars := (typ, input_v_name, assign_expr) :: !(st.input_vars);
        (* return the variable *)
        (Abstract_syntax.A_identifier input_v_name, hint))
      else if String.compare func_name "input" = 0 then
        let rec strip_cast (e, _, _) =
          match e with
          | C_AST.E_cast ((e', t', r'), _) -> strip_cast (e', t', r')
          | _ -> e
        in
        let id =
          if Array.length args >= 1 then
            match strip_cast args.(0) with
            | C_AST.E_string_literal (s, _) -> s
            | _ ->
                raise
                  (UnsupportedFeature
                     "input() expects a string literal agent id")
          else raise (UnsupportedFeature "input() expects an agent id")
        in
        if Array.length args = 1 then (Abstract_syntax.A_INPUT (id, None), H_INT)
        else (
          assert (Array.length args = 3);
          (* args.(0) is the agent-id string, so the bounds are args.(1)/args.(2).
             A bound is a numeric literal, possibly negated: in C a literal like
             -1 is parsed as a unary minus applied to 1, so we add that case and
             fold it back into a constant string, per bound. *)
          let const_str arg =
            match convert_expr st arg with
            | ( (Abstract_syntax.A_int_const s | Abstract_syntax.A_float_const s),
                _ ) ->
                s
            | ( Abstract_syntax.A_unary
                  ( Abstract_syntax.A_UNARY_MINUS,
                    ( ( Abstract_syntax.A_int_const s
                      | Abstract_syntax.A_float_const s ),
                      _ ) ),
                _ ) ->
                "-" ^ s
            | _ ->
                raise
                  (UnsupportedConversion
                     "unexpected kind of arguments of input func")
          in
          let bound =
            ( const_str args.(1) |> attach_position,
              const_str args.(2) |> attach_position )
          in
          (Abstract_syntax.A_INPUT (id, Some bound), H_INT))
      else
        let args =
          List.map
            (fun arg -> convert_expr st arg |> fst |> attach_position)
            (Array.to_list args)
        in
        ( Abstract_syntax.A_call (attach_position func_name, args),
          typ_to_hint (fst func_ret_typ) )
  | C_AST.E_assign (lfs, rhs) ->
      ( A_assign
          ( convert_expr st lfs |> fst |> attach_position,
            None,
            convert_expr st rhs |> fst |> attach_position ),
        H_VOID )
  | C_AST.E_address_of exp ->
      let e, hint = convert_expr st exp in
      (A_address_of e, H_PTR hint)
  | C_AST.E_deref exp ->
      let e, hint = convert_expr st exp in
      (A_deref e, hint)
  | C_AST.E_array_subscript _ -> raise (UnsupportedFeature "array")
  | _ -> raise (UnsupportedConversion "unsupported expr")

(* Similar to `convert_expr` but ensure that the result is a bool.

   In C there is not boolean type, thus int expressions are freely used as
   IF/LOOP conditions. In Banal we need to perform a int -> bool. This is
   simply implemented as a comparison with non-zero *)
let expr_to_guard (st : state) (e : C_AST.expr) : Abstract_syntax.expr =
  let e, hint = convert_expr st e in
  match hint with
  | H_BOOL -> e
  | H_INT ->
      Abstract_syntax.A_binary
        ( Abstract_syntax.A_NOT_EQUAL,
          e |> attach_position,
          Abstract_syntax.A_int_const "0" |> attach_position )
  | H_VOID -> raise (UnsupportedConversion "unexpected hint in expr_to_guard")

let var_init_expr (st : state) (var : C_AST.variable) :
    Abstract_syntax.expr Abstract_syntax.ext option =
  Option.bind var.var_init (fun init ->
      match init with
      | C_AST.I_init_expr e -> Some (convert_expr st e |> fst |> attach_position)
      | C_AST.I_init_list _ -> raise (UnsupportedFeature "array")
      | _ -> raise (UnsupportedConversion "unknown variable init"))

let rec convert_stmt (st : state) ((stmt, _) : C_AST.statement) :
    Abstract_syntax.stat =
  match stmt with
  | C_AST.S_local_declaration var ->
      A_local
        ( var_typ var |> attach_position,
          [ (var_name var |> attach_position, var_init_expr st var) ] )
  | C_AST.S_block stmts -> convert_block st stmts
  | C_AST.S_for (init, cond, incr, body) ->
      (* for (init; cond; incr) { body }
         is converted in a while loop as banal does not
         suppport natively for loops.

         init;
         while (cond) { body; incr } *)
      let init = convert_block st init in
      let cond =
        match cond with
        | Some cond -> expr_to_guard st cond |> attach_position
        | None -> Abstract_syntax.A_bool_const true |> attach_position
      in

      (* make a new body containing the body of the for loop
         plus at the end `incr` *)
      let old_body_stmts =
        match convert_block st body with
        | Abstract_syntax.A_block stmts -> stmts
        | _ -> raise (Invalid_argument "convert_block returned a non-A_block")
      in

      let new_body =
        match incr with
        | Some incr ->
            old_body_stmts
            @ [
                Abstract_syntax.A_expr
                  (convert_expr st incr |> fst |> attach_position)
                |> attach_position;
              ]
        | None -> old_body_stmts
      in

      let while_loop =
        Abstract_syntax.A_while
          (cond, Abstract_syntax.A_block new_body |> attach_position)
      in

      (* join the init and the while loop *)
      Abstract_syntax.A_block (List.map attach_position [ init; while_loop ])
  | C_AST.S_while (cond, body) ->
      let stmt = convert_block st body |> attach_position in
      Abstract_syntax.A_while (expr_to_guard st cond |> attach_position, stmt)
  | C_AST.S_if (cond, then_blk, else_blk) ->
      let then_stmt = convert_block st then_blk |> attach_position in
      let else_stmt = Some (convert_block st else_blk |> attach_position) in
      Abstract_syntax.A_if
        (expr_to_guard st cond |> attach_position, then_stmt, else_stmt)
  (* HACK -> hook calls to assert and inject a A_assert statement *)
  | C_AST.S_expression
      ( C_AST.E_call
          ((C_AST.E_cast ((C_AST.E_function func, _, _), _), _, _), args),
        _,
        _ )
    when func.func_unique_name = "__VERIFIER_assert"
         || func.func_unique_name = "assert" ->
      assert (Array.length args = 1);
      Abstract_syntax.A_assert (expr_to_guard st args.(0) |> attach_position)
  (* HACK -> hook calls to `assume_abort_if_not` and inject a statement to emulate it *)
  | C_AST.S_expression
      ( C_AST.E_call
          ((C_AST.E_cast ((C_AST.E_function func, _, _), _), _, _), args),
        _,
        _ )
    when func.func_unique_name = "assume_abort_if_not" ->
      assert (Array.length args = 1);
      Abstract_syntax.A_if
        ( Abstract_syntax.A_unary
            (Abstract_syntax.A_NOT, expr_to_guard st args.(0) |> attach_position)
          |> attach_position,
          Abstract_syntax.A_assert
            (Abstract_syntax.A_bool_const false |> attach_position)
          |> attach_position,
          None )
  (* HACK -> hook calls to `reach_error` and inject a statement to emulate it *)
  | C_AST.S_expression
      ( C_AST.E_call
          ((C_AST.E_cast ((C_AST.E_function func, _, _), _), _, _), args),
        _,
        _ )
    when func.func_unique_name = "reach_error" ->
      assert (Array.length args = 0);
      Abstract_syntax.A_assert
        (Abstract_syntax.A_bool_const false |> attach_position)
  | C_AST.S_expression
      ( C_AST.E_call
          ((C_AST.E_cast ((C_AST.E_function func, _, _), _), _, _), args),
        _,
        _ )
    when func.func_unique_name = "exit" ->
      assert (Array.length args = 1);
      Abstract_syntax.A_return
        (Option.bind None (fun e ->
             convert_expr st e |> fst |> attach_position |> Option.some))
  | C_AST.S_expression
      ( C_AST.E_call
          ((C_AST.E_cast ((C_AST.E_function func, _, _), _), _, _), args),
        _,
        _ )
    when func.func_unique_name = "abort" ->
      assert (Array.length args = 0);
      Abstract_syntax.A_return
        (Option.bind None (fun e ->
             convert_expr st e |> fst |> attach_position |> Option.some))
  | C_AST.S_expression e ->
      Abstract_syntax.A_expr (convert_expr st e |> fst |> attach_position)
  | C_AST.S_jump (C_AST.S_return (ret_val, _)) ->
      Abstract_syntax.A_return
        (Option.bind ret_val (fun e ->
             convert_expr st e |> fst |> attach_position |> Option.some))
  | C_AST.S_jump (C_AST.S_break _) -> Abstract_syntax.A_BREAK
  | C_AST.S_jump (C_AST.S_goto _) -> raise (UnsupportedFeature "goto")
  | C_AST.S_target (C_AST.S_label s) -> A_label (s |> attach_position)
  | _ -> raise (UnsupportedConversion "unsupported stat kind")

and convert_block (st : state) (block : C_AST.block) : Abstract_syntax.stat =
  A_block
    (List.map (fun s -> convert_stmt st s |> attach_position) block.blk_stmts)

let convert_func (st : state) (func : C_AST.func) :
    Abstract_syntax.fundecl option =
  (* Bail out on a body-less function BEFORE converting any of its types.
     Such a function is a declaration only -- typically dragged in by a header
     (`#include <stdio.h>`) and never analysed -- and its signature routinely
     uses features we do not model (unsigned, pointers, variadics). Converting
     it first made a whole file unanalysable because of a prototype the
     analysis never looks at, even though the result was discarded right
     after. *)
  match func.func_body with
  | None -> None
  | Some stmts -> (
      (* MOPSA handles functions without a return value with the special
         type `void` (as in C), but in Banal we return an `None` optional.
         Handle this special case explicitly, for the other types
         use `convert_type_qual` *)
      let return_typ =
        match func.func_return with
        | C_AST.T_void, _ -> None
        | _ ->
            convert_type_qual func.func_return |> attach_position |> Option.some
      in

      let name = func.func_org_name |> attach_position in
      let args =
        List.map
          (fun var ->
            ( attach_position C_AST.(var.var_org_name),
              convert_type_qual var.var_type |> attach_position ))
          (Array.to_list func.func_parameters)
      in

      match convert_block st stmts with
      | Abstract_syntax.A_block stmts -> Some (return_typ, name, args, stmts)
      | _ -> raise (Invalid_argument "convert_block returned a non-A_block"))

let parse_file (f : string) : Typed_syntax.prog =
  let target = get_target_info (get_default_target_options ()) in
  let ctx = create_context "project" target in
  parse_file "clang" !Config.filename [ "-fbracket-depth=512" ] false false
    false false ctx;
  let prj = link_project ctx in
  (* C_print.print_project stdout prj; *)
  let st = { input_vars = ref [] } in
  (* StringMap.to_seq returns the functions in random order. This may
     cause some problems as a function calling another one may be
     analyzed first, causing the typed_syntax translator to fail.
     Heuristic -> delay `main` to the end *)
  let funcs =
    prj.proj_funcs |> C_AST.StringMap.bindings
    |> List.map (fun (_, f) -> f)
    |> List.filter (fun f ->
           not (StringSet.mem C_AST.(f.func_org_name) skip_funcs))
    |> List.filter (fun f -> C_AST.(f.func_org_name <> "main"))
    |> List.filter_map (convert_func st)
    |> List.map attach_position
    |> List.map (fun f -> Abstract_syntax.A_function f)
  in
  let funcs =
    funcs
    @ [
        ( C_AST.StringMap.find "main" prj.proj_funcs
        |> convert_func st |> Option.get |> attach_position
        |> fun f -> Abstract_syntax.A_function f );
      ]
  in
  (* declaration of global variables both from the program and
     for input variables
   *)
  let global_decl =
    C_AST.StringMap.bindings prj.proj_vars
    |> List.map (fun (_, v) -> v)
    (* Drop extern globals we cannot type. `#include <stdio.h>` declares
       stdin/stdout/stderr as FILE*, i.e. pointers to a struct, which killed
       the whole analysis even though the benchmark never mentions them. An
       extern is "declared but not defined", so there is nothing to analyse in
       it anyway. The filter is deliberately narrow: a global of the program
       itself still raises, so an unsupported type in analysed code is not
       silently swallowed. *)
    |> List.filter (fun var ->
           match C_AST.(var.var_kind) with
           | C_AST.Variable_extern -> (
               try
                 ignore (var_typ var);
                 true
               with UnsupportedFeature _ | UnsupportedConversion _ -> false)
           | _ -> true)
    |> List.map (fun var ->
           Abstract_syntax.A_global
             ( ( var_typ var |> attach_position,
                 [ (var_name var |> attach_position, var_init_expr st var) ] )
               |> attach_position,
               Abstract_syntax.A_VARIABLE ))
  in
  let input_decl =
    List.map
      (fun (typ, v, init) ->
        Abstract_syntax.A_global
          ( ( typ |> attach_position,
              [ (v |> attach_position, Some (init |> attach_position)) ] )
            |> attach_position,
            Abstract_syntax.A_INPUT ))
      !(st.input_vars)
  in
  Abstract_to_typed_syntax.translate_program input_decl global_decl funcs
