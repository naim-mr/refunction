open Apron

let lincons1_cmp c1 c2 =
  Linexpr0.cmp c1.Lincons1.lincons0.Lincons0.linexpr0
    c2.Lincons1.lincons0.Lincons0.linexpr0

let compare_coeff c1 c2 =
  match (c1, c2) with
  | Coeff.Interval c1, Coeff.Interval c2 ->
      let inf = Scalar.cmp c1.Interval.inf c2.Interval.inf in
      let sup = Scalar.cmp c1.Interval.sup c2.Interval.sup in
      if inf = 0 then if sup = 0 then 0 else sup else inf
  | Coeff.Interval c1, Coeff.Scalar c2 ->
      let inf = Scalar.cmp c1.Interval.inf c2 in
      let sup = Scalar.cmp c1.Interval.sup c2 in
      if inf = 0 then if sup = 0 then 0 else sup else inf
  | Coeff.Scalar c1, Coeff.Interval c2 ->
      let inf = Scalar.cmp c1 c2.Interval.inf in
      let sup = Scalar.cmp c1 c2.Interval.sup in
      if inf = 0 then if sup = 0 then 0 else sup else inf
  | Coeff.Scalar c1, Coeff.Scalar c2 -> Scalar.cmp c1 c2

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
  | Scalar.Mpfrf c1, Scalar.Mpfrf c2 -> Scalar.Mpfrf (Mpfrf.add c1 c2 Mpfr.Zero)

let div_scalar c1 c2 =
  match (c1, c2) with
  | Scalar.Float c1, Scalar.Float c2 -> Scalar.Float (c1 /. c2)
  | Scalar.Float c1, Scalar.Mpqf c2 -> Scalar.Float (c1 /. Mpqf.to_float c2)
  | Scalar.Float c1, Scalar.Mpfrf c2 -> Scalar.Float (c1 /. Mpfrf.to_float c2)
  | Scalar.Mpqf c1, Scalar.Float c2 -> Scalar.Float (Mpqf.to_float c1 /. c2)
  | Scalar.Mpqf c1, Scalar.Mpqf c2 -> Scalar.Mpqf (Mpqf.div c1 c2)
  | Scalar.Mpqf c1, Scalar.Mpfrf c2 ->
      Scalar.Mpqf (Mpqf.div c1 (Mpfrf.to_mpqf c2))
  | Scalar.Mpfrf c1, Scalar.Float c2 -> Scalar.Float (Mpfrf.to_float c1 /. c2)
  | Scalar.Mpfrf c1, Scalar.Mpqf c2 ->
      Scalar.Mpqf (Mpqf.div (Mpfrf.to_mpqf c1) c2)
  | Scalar.Mpfrf c1, Scalar.Mpfrf c2 -> Scalar.Mpfrf (Mpfrf.div c1 c2 Mpfr.Zero)

let mul_scalar c1 c2 =
  match (c1, c2) with
  | Scalar.Float c1, Scalar.Float c2 -> Scalar.Float (c1 *. c2)
  | Scalar.Float c1, Scalar.Mpqf c2 -> Scalar.Float (c1 *. Mpqf.to_float c2)
  | Scalar.Float c1, Scalar.Mpfrf c2 -> Scalar.Float (c1 *. Mpfrf.to_float c2)
  | Scalar.Mpqf c1, Scalar.Float c2 -> Scalar.Float (Mpqf.to_float c1 *. c2)
  | Scalar.Mpqf c1, Scalar.Mpqf c2 -> Scalar.Mpqf (Mpqf.mul c1 c2)
  | Scalar.Mpqf c1, Scalar.Mpfrf c2 ->
      Scalar.Mpqf (Mpqf.mul c1 (Mpfrf.to_mpqf c2))
  | Scalar.Mpfrf c1, Scalar.Float c2 -> Scalar.Float (Mpfrf.to_float c1 *. c2)
  | Scalar.Mpfrf c1, Scalar.Mpqf c2 ->
      Scalar.Mpqf (Mpqf.mul (Mpfrf.to_mpqf c1) c2)
  | Scalar.Mpfrf c1, Scalar.Mpfrf c2 -> Scalar.Mpfrf (Mpfrf.mul c1 c2 Mpfr.Zero)

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

let mul_coeff c1 c2 =
  match (c1, c2) with
  | Coeff.Scalar c1, Coeff.Scalar c2 -> Coeff.Scalar (mul_scalar c1 c2)
  | Coeff.Scalar c1, Coeff.Interval c2 | Coeff.Interval c2, Coeff.Scalar c1 ->
      let s = Scalar.sgn c1 in
      if s < 0 then
        Coeff.reduce
          (Coeff.i_of_scalar
             (mul_scalar c1 c2.Interval.sup)
             (mul_scalar c1 c2.Interval.inf))
      else if s = 0 then Coeff.Scalar (Scalar.of_int 0)
      else
        Coeff.reduce
          (Coeff.i_of_scalar
             (mul_scalar c1 c2.Interval.inf)
             (mul_scalar c1 c2.Interval.sup))
  | Coeff.Interval c1, Coeff.Interval c2 ->
      let x1 = mul_scalar c1.Interval.inf c2.Interval.inf in
      let x2 = mul_scalar c1.Interval.inf c2.Interval.sup in
      let x3 = mul_scalar c1.Interval.sup c2.Interval.inf in
      let x4 = mul_scalar c1.Interval.sup c2.Interval.sup in
      let smin x y = if Scalar.cmp x y < 0 then x else y in
      let smax x y = if Scalar.cmp x y < 0 then y else x in
      Coeff.reduce
        (Coeff.i_of_scalar
           (smin x1 (smin x2 (smin x3 x4)))
           (smax x1 (smax x2 (smax x3 x4))))

let inv_scalar = function
  | Scalar.Float c -> Scalar.Float (1. /. c)
  | Scalar.Mpqf f -> Scalar.Mpqf (Mpqf.inv f)
  | Scalar.Mpfrf f -> Scalar.Mpfrf (raise (Invalid_argument "invScalar: mpfrf"))

let inv_coeff = function
  | Coeff.Scalar s -> Coeff.Scalar (inv_scalar s)
  | _ -> raise (Invalid_argument "invCoeff: interval")

type sgn = Zero | Positive | Negative | Unknown

let mul_sign sgn1 sgn2 =
  match (sgn1, sgn2) with
  | Zero, _ | _, Zero -> Zero
  | Positive, Positive | Negative, Negative -> Positive
  | Positive, Negative | Negative, Positive -> Negative
  | Unknown, _ | _, Unknown -> Unknown

let sign_coeff = function
  | Coeff.Scalar c ->
      let s = Scalar.sgn c in
      if s > 0 then Positive else if s = 0 then Zero else Negative
  | Coeff.Interval c ->
      let si = Scalar.sgn c.Interval.inf in
      let ss = Scalar.sgn c.Interval.sup in
      if si > 0 then Positive
      else if ss < 0 then Negative
      else if si = 0 && ss = 0 then Zero
      else Unknown
