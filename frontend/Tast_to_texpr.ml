open Typed_syntax
open Utils
open Utils.Datatypes
open Apron

let rec exp_to_apron ((e, t, ext) : expr typed) =
  match e with
  | T_int_const ((Finite a as inf), (Finite b as sup)) ->
      Texpr1.Cst
        (Coeff.Interval
           (Interval.of_mpqf (Intinf.to_mpqf inf) (Intinf.to_mpqf sup)))
  | T_int_const (INF, (Finite b as sup)) ->
      Texpr1.Cst
        (Coeff.Interval
           (Interval.of_scalar (Scalar.of_infty (-1))
              (Intinf.to_mpqf sup |> Scalar.of_mpqf)))
  | T_int_const ((Finite a as inf), INF) ->
      Texpr1.Cst
        (Coeff.Interval
           (Interval.of_scalar
              (Intinf.to_mpqf inf |> Scalar.of_mpqf)
              (Scalar.of_infty 1)))
  | T_int_const (INF, INF) -> Texpr1.Cst (Coeff.Interval Interval.top)
  | T_int_const (MINF, INF) -> Texpr1.Cst (Coeff.Interval Interval.top)
  | T_input (_, (min, max)) -> exp_to_apron (T_int_const (min, max), t, ext)
  | T_bool_const True -> Texpr1.Cst (Coeff.s_of_int 1)
  | T_bool_const False -> Texpr1.Cst (Coeff.s_of_int 0)
  | T_bool_const Maybe -> Texpr1.Cst (Coeff.i_of_int 0 1)
  | T_var x when String.starts_with ~prefix:"nondet_" x.var_name -> (
      match x.var_typ with
      | A_int (_, _) ->
          exp_to_apron
            (T_int_const (Value_semantics.int_type_set A_INT A_SIGNED), t, ext)
      | A_BOOL -> exp_to_apron (T_bool_const Maybe, t, ext)
      | _ -> raise (Invalid_argument "Float not handle yet"))
  | T_var x -> Texpr1.Var (apron_of_var x)
  | T_float_const _ -> raise (Invalid_argument "Float not handle yet")
  | T_unary (A_UNARY_MINUS, e) ->
      let e = exp_to_apron e in
      Texpr1.Unop (Texpr1.Neg, e, Texpr1.Int, Texpr1.Zero)
  | T_unary (A_UNARY_PLUS, e) | T_unary (A_cast _, e) -> exp_to_apron e
  | T_binary (o, e1, e2) -> (
      let e1 = exp_to_apron e1 in
      let e2 = exp_to_apron e2 in
      match o with
      | A_PLUS -> Texpr1.Binop (Texpr1.Add, e1, e2, Texpr1.Int, Texpr1.Zero)
      | A_MINUS -> Texpr1.Binop (Texpr1.Sub, e1, e2, Texpr1.Int, Texpr1.Zero)
      | A_MULTIPLY -> Texpr1.Binop (Texpr1.Mul, e1, e2, Texpr1.Int, Texpr1.Zero)
      | A_DIVIDE -> Texpr1.Binop (Texpr1.Div, e1, e2, Texpr1.Int, Texpr1.Zero)
      | A_MODULO -> Texpr1.Cst (Coeff.Interval Interval.top)
      | _ ->
          raise
            (UnsupportedFeature "not supported or not supposed to be supported")
      )
  | T_deref (T_var v, _, _) -> Texpr1.Var (Var.of_string v.var_name)
  | _ ->
      raise (UnsupportedFeature "not supported or not supposed to be supported")
