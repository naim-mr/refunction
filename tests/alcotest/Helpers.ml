(* Building test values from outside the domain modules: variables, an
   environment and linear constraints. Partitions and functions are then built
   with the functions of each instance ([B.inner], [AP.zero], ...). *)

open Domains
open Abstract_syntax
open Typed_syntax
module C = AP_LinearConstraint.AP_LinearConstraint

let mk_var id name =
  {
    var_name = name;
    var_extent = extent_unknown;
    var_typ = A_int (A_INTEGER, A_SIGNED);
    var_id = Z.of_int id;
    var_synthetic = false;
    var_scope = T_LOCAL;
  }

let x = mk_var 1 "x"
let y = mk_var 2 "y"
let env = C.add_dim_to_env (C.add_dim_to_env (C.init_env ()) x) y

(* [cons [ (a1, v1); ... ] c] is the constraint a1·v1 + ... + c >= 0. The APRON
   names of the variables are [apron_of_var v], so the APRON parser cannot be
   used here. *)
let cons coeffs c : C.t =
  let e = Linexpr1.make env.ap_env in
  List.iter
    (fun (a, v) -> Linexpr1.set_coeff e (apron_of_var v) (Coeff.s_of_int a))
    coeffs;
  Linexpr1.set_cst e (Coeff.s_of_int c);
  { cons = Lincons1.make e Lincons1.SUPEQ; env }

(* Typed expressions, for the transfer functions. [itv a b] is the
   non-deterministic constant [a, b]. *)
let int_t = A_int (A_INTEGER, A_SIGNED)
let var v : expr typed = (T_var v, int_t, extent_unknown)

let itv a b : expr typed =
  ( T_int_const (Datatypes.Finite (Z.of_int a), Datatypes.Finite (Z.of_int b)),
    int_t,
    extent_unknown )

let cst n = itv n n
let bin op e1 e2 : expr typed = (T_binary (op, e1, e2), int_t, extent_unknown)
let cmp op e1 e2 : expr typed = (T_binary (op, e1, e2), A_BOOL, extent_unknown)

(* Runs a QCheck test as an Alcotest case, without qcheck-alcotest. *)
let of_qcheck ?(speed = `Slow) (QCheck2.Test.Test cell as t) =
  let name = QCheck.Test.get_name cell in
  Alcotest.test_case name speed (fun () -> QCheck.Test.check_exn t)
