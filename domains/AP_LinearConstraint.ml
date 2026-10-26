(*   
             ********* (Linear) Constraints ************
   Copyright (C) 2012-2014 by Caterina Urban. All rights reserved.
*)

open Typed_syntax
open Apron
open Sig.Constraints
open Banal.Banal_apron_domain
open Utils.Apron_utils

module AP_LinearConstraint : AP_CONSTRAINT = struct
  type cons = Lincons1.t
  type env = lincons_env
  type t = { cons : cons; env : env }
  type dim = var

  let init_env () = { vars = []; ap_env = Environment.make [||] [||] }

  let add_dim_to_env env dim =
    {
      vars = dim :: env.vars;
      ap_env = Environment.add env.ap_env [| apron_of_var dim |] [||];
    }

  let remove_dim_of_env env dim =
    {
      vars = List.filter (fun v -> Z.compare v.var_id dim.var_id <> 0) env.vars;
      ap_env = [| apron_of_var dim |] |> Environment.remove env.ap_env;
    }

  let env t = t.env
  let set_env env t = { t with env }

  (**)
  let is_bot t = Lincons1.is_unsat t.cons
  let make_unsat env = { cons = Lincons1.make_unsat env.ap_env; env }

  let compare_typ t1 t2 =
    match (t1, t2) with
    | Lincons1.EQ, _ | _, Lincons1.EQ -> raise (Invalid_argument "is_eqTyp:EQ")
    | Lincons1.SUPEQ, Lincons1.SUPEQ -> 0
    | Lincons1.SUP, _ | _, Lincons1.SUP ->
        raise (Invalid_argument "is_eqTyp:SUP")
    | Lincons1.DISEQ, _ | _, Lincons1.DISEQ ->
        raise (Invalid_argument "is_eqTyp:DISEQ")
    | Lincons1.EQMOD _, _ | _, Lincons1.EQMOD _ ->
        raise (Invalid_argument "is_eqTyp:EQMOD")

  let compare t1 t2 =
    let c1 = t1.cons and c2 = t2.cons in
    let rec aux l1 l2 =
      match (l1, l2) with
      | [], [] ->
          let c = compare_coeff (Lincons1.get_cst c1) (Lincons1.get_cst c2) in
          if c = 0 then compare_typ (Lincons1.get_typ c1) (Lincons1.get_typ c2)
          else c
      | [], (x2, v2) :: l2s ->
          let c = compare_coeff (Coeff.s_of_int 0) v2 in
          if c = 0 then aux l1 l2s else c
      | (x1, v1) :: l1s, [] ->
          let c = compare_coeff v1 (Coeff.s_of_int 0) in
          if c = 0 then aux l1s l2 else c
      | (x1, v1) :: l1s, (x2, v2) :: l2s when Var.compare x1 x2 < 0 ->
          let c = compare_coeff v1 (Coeff.s_of_int 0) in
          if c = 0 then aux l1s l2 else c
      | (x1, v1) :: l1s, (x2, v2) :: l2s when Var.compare x1 x2 = 0 ->
          let c = compare_coeff v1 v2 in
          if c = 0 then aux l1s l2s else c
      | (x1, v1) :: l1s, (x2, v2) :: l2s (*when (Var.compare x1 x2) > 0*) ->
          let c = compare_coeff (Coeff.s_of_int 0) v2 in
          if c = 0 then aux l1 l2s else c
    in
    let l1 = ref [] and l2 = ref [] in
    Lincons1.iter (fun v x -> l1 := (x, v) :: !l1) c1;
    Lincons1.iter (fun v x -> l2 := (x, v) :: !l2) c2;
    aux (List.rev !l1) (List.rev !l2)

  let is_eq c1 c2 = compare c1 c2 = 0
  let is_leq c1 c2 = compare c1 c2 <= 0

  let similar t1 t2 =
    let c1 = t1.cons and c2 = t2.cons in
    let rec aux l1 l2 =
      match (l1, l2) with
      | [], [] -> 0
      | [], (x2, v2) :: l2s ->
          let c = compare_coeff (Coeff.s_of_int 0) v2 in
          if c = 0 then aux l1 l2s else c
      | (x1, v1) :: l1s, [] ->
          let c = compare_coeff v1 (Coeff.s_of_int 0) in
          if c = 0 then aux l1s l2 else c
      | (x1, v1) :: l1s, (x2, v2) :: l2s when Var.compare x1 x2 < 0 ->
          let c = compare_coeff v1 (Coeff.s_of_int 0) in
          if c = 0 then aux l1s l2 else c
      | (x1, v1) :: l1s, (x2, v2) :: l2s when Var.compare x1 x2 = 0 ->
          let c = compare_coeff v1 v2 in
          if c = 0 then aux l1s l2s else c
      | (x1, v1) :: l1s, (x2, v2) :: l2s (*when (Var.compare x1 x2) > 0*) ->
          let c = compare_coeff (Coeff.s_of_int 0) v2 in
          if c = 0 then aux l1 l2s else c
    in
    let t1 = Lincons1.get_typ c1 and t2 = Lincons1.get_typ c2 in
    match (t1, t2) with
    | Lincons1.SUPEQ, Lincons1.SUPEQ ->
        let l1 = ref [] and l2 = ref [] in
        Lincons1.iter (fun v x -> l1 := (x, v) :: !l1) c1;
        Lincons1.iter (fun v x -> l2 := (x, v) :: !l2) c2;
        aux !l1 !l2 = 0
    | _ -> false

  let var v t =
    let v = apron_of_var v in
    let c = Lincons1.get_coeff t.cons v in
    compare_coeff c (Coeff.s_of_int 0) != 0

  let add_scalar c1 c2 =
    match (c1, c2) with
    | Scalar.Float c1, Scalar.Float c2 -> Scalar.Float (c1 +. c2)
    | Scalar.Float c1, Scalar.Mpqf c2 -> Scalar.Float (c1 +. Mpqf.to_float c2)
    | Scalar.Float c1, Scalar.Mpfrf c2 -> Scalar.Float (c1 +. Mpfrf.to_float c2)
    | Scalar.Mpqf c1, Scalar.Float c2 -> Scalar.Float (Mpqf.to_float c1 +. c2)
    | Scalar.Mpqf c1, Scalar.Mpqf c2 -> Scalar.Mpqf (Mpqf.add c1 c2)
    | Scalar.Mpqf c1, Scalar.Mpfrf c2 ->
        Scalar.Mpqf (Mpqf.add c1 (Mpfrf.to_mpqf c2))
    | Scalar.Mpfrf c1, Scalar.Float c2 -> Scalar.Float (Mpfrf.to_float c1 +. c2)
    | Scalar.Mpfrf c1, Scalar.Mpqf c2 ->
        Scalar.Mpqf (Mpqf.add (Mpfrf.to_mpqf c1) c2)
    | Scalar.Mpfrf c1, Scalar.Mpfrf c2 ->
        Scalar.Mpfrf (Mpfrf.add c1 c2 Mpfr.Zero)

  let add_coeff c1 c2 =
    match (c1, c2) with
    | Coeff.Scalar c1, Coeff.Scalar c2 -> Coeff.Scalar (add_scalar c1 c2)
    | Coeff.Scalar c1, Coeff.Interval c2 ->
        Coeff.reduce
          (Coeff.i_of_scalar
             (add_scalar c1 c2.Interval.inf)
             (add_scalar c1 c2.Interval.sup))
    | Coeff.Interval c1, Coeff.Scalar c2 ->
        Coeff.reduce
          (Coeff.i_of_scalar
             (add_scalar c1.Interval.inf c2)
             (add_scalar c1.Interval.sup c2))
    | Coeff.Interval c1, Coeff.Interval c2 ->
        Coeff.reduce
          (Coeff.i_of_scalar
             (add_scalar c1.Interval.inf c2.Interval.inf)
             (add_scalar c1.Interval.sup c2.Interval.sup))

  let negate t =
    let n = Lincons1.copy t.cons in
    let ty = Lincons1.get_typ n in
    match ty with
    | Lincons1.EQ -> raise (Invalid_argument "negate:EQ")
    | Lincons1.SUPEQ ->
        Lincons1.iter (fun v x -> Lincons1.set_coeff n x (Coeff.neg v)) n;
        Lincons1.set_cst n
          (Coeff.neg (add_coeff (Lincons1.get_cst n) (Coeff.s_of_int 1)));
        { t with cons = n }
    | Lincons1.SUP -> raise (Invalid_argument "negate:SUP")
    | Lincons1.DISEQ -> raise (Invalid_argument "negate:DISEQ")
    | Lincons1.EQMOD _ -> raise (Invalid_argument "negate:EQMOD")

  let expand t =
    let ty = Lincons1.get_typ t.cons in
    match ty with
    | Lincons1.EQ ->
        let c1 = Lincons1.copy t.cons in
        let c2 = Lincons1.copy t.cons in
        Lincons1.set_typ c1 Lincons1.SUPEQ;
        Lincons1.iter (fun v x -> Lincons1.set_coeff c2 x (Coeff.neg v)) c2;
        Lincons1.set_cst c2 (Coeff.neg (Lincons1.get_cst c2));
        Lincons1.set_typ c2 Lincons1.SUPEQ;
        ({ t with cons = c1 }, { t with cons = c2 })
    | Lincons1.SUPEQ -> raise (Invalid_argument "SUPEQ")
    | Lincons1.SUP -> raise (Invalid_argument "SUP")
    | Lincons1.DISEQ -> raise (Invalid_argument "DISEQ")
    | Lincons1.EQMOD _ -> raise (Invalid_argument "EQMOD")

  let shadow (k : Coeff.t -> Coeff.t -> Coeff.t) env t x inf sup =
    let vx = apron_of_var x in
    let cx c = Lincons1.get_coeff c.cons vx in
    (* bounds of the input: x - inf >= 0 and sup - x >= 0, when finite *)
    let bound coef cst =
      let e = Linexpr1.make env.ap_env in
      Linexpr1.set_coeff e vx (Coeff.s_of_int coef);
      Linexpr1.set_cst e (Coeff.Scalar cst);
      { cons = Lincons1.make e Lincons1.SUPEQ; env }
    in
    let t =
      (if Scalar.is_infty inf = 0 then [ bound 1 (Scalar.neg inf) ] else [])
      @ (if Scalar.is_infty sup = 0 then [ bound (-1) sup ] else [])
      @ t
    in
    let with_x, others = List.partition (var x) t in
    let lows, ups =
      List.partition (fun c -> Coeff.cmp (cx c) (Coeff.s_of_int 0) > 0) with_x
    in
    let combine l u =
      let a = cx l and b = Coeff.neg (cx u) in
      (* a, b > 0 *)
      let e = Linexpr1.make env.ap_env in
      (* fresh, no sharing *)
      let add c coef v =
        Linexpr1.set_coeff e v
          (add_coeff (Linexpr1.get_coeff e v) (mul_coeff coef c))
      in
      Lincons1.iter (fun c v -> add c b v) l.cons;
      (* b·L *)
      Lincons1.iter (fun c v -> add c a v) u.cons;
      (* a·U *)
      Linexpr1.set_coeff e vx (Coeff.s_of_int 0);
      Linexpr1.set_cst e
        (add_coeff
           (add_coeff
              (mul_coeff b (Lincons1.get_cst l.cons))
              (mul_coeff a (Lincons1.get_cst u.cons)))
           (k a b));
      (* dark: −(a−1)(b−1)/ real: 0 *)
      { cons = Lincons1.make e Lincons1.SUPEQ; env }
    in
    others @ List.concat_map (fun l -> List.map (combine l) ups) lows

  let print fmt t =
    let c = t.cons in
    let vars = t.env.vars in
    let first = ref true in
    let rec aux c v =
      match c with
      | Coeff.Scalar s ->
          if v <> "" && Scalar.sgn s = 0 then ()
          else (
            if Scalar.sgn s < 0 then
              if v <> "" && Scalar.equal_int s (-1) then Format.fprintf fmt "-"
              else Format.fprintf fmt "-%s" (Scalar.to_string (Scalar.neg s))
            else if !first then
              if v <> "" && Scalar.equal_int s 1 then ()
              else Format.fprintf fmt "%s" (Scalar.to_string s)
            else if v <> "" && Scalar.equal_int s 1 then Format.fprintf fmt "+"
            else Format.fprintf fmt "+%s" (Scalar.to_string s);
            if v <> "" then Format.fprintf fmt "%s" v;
            first := false)
      | Coeff.Interval i ->
          if Scalar.equal i.Interval.inf i.Interval.sup then
            aux (Coeff.Scalar i.Interval.inf) v
          else (
            if not !first then Format.fprintf fmt "+";
            Format.fprintf fmt "[%s,%s]"
              (Scalar.to_string i.Interval.inf)
              (Scalar.to_string i.Interval.sup);
            if v <> "" then Format.fprintf fmt "%s" v);
          first := false
    in
    Lincons1.iter
      (fun v x ->
        try
          let x =
            List.find
              (fun y ->
                String.compare (Var.to_string x)
                  (apron_of_var y |> Var.to_string)
                = 0)
              vars
          in
          Format.fprintf Format.str_formatter "$%s{%s}" (Z.to_string x.var_id)
            x.var_name;
          aux v (Format.flush_str_formatter ())
        with Not_found -> ())
      c;
    let k = Coeff.neg (Lincons1.get_cst c) in
    if !first then Format.fprintf fmt "0";
    first := true;
    match Lincons1.get_typ c with
    | Lincons1.EQ ->
        Format.fprintf fmt " == ";
        aux k ""
    | Lincons1.SUPEQ ->
        Format.fprintf fmt " >= ";
        aux k ""
    | Lincons1.SUP ->
        Format.fprintf fmt " > ";
        aux k ""
    | Lincons1.DISEQ -> raise (Invalid_argument "print:DISEQ")
    | Lincons1.EQMOD s -> raise (Invalid_argument "print:EQMOD")
end

module C = AP_LinearConstraint
