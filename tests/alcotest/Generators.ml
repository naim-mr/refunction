(* QCheck generators over [Helpers.env]. Coefficients are kept small and the
   environment has two variables: wider draws mostly give empty partitions, on
   which every law holds trivially. *)

open Helpers

let coeff = QCheck.Gen.int_range (-3) 3
let const = QCheck.Gen.int_range (-5) 5

let cons : C.t QCheck.Gen.t =
  QCheck.Gen.map3 (fun a b c -> cons [ (a, x); (b, y) ] c) coeff coeff const

let print_cons = Format.asprintf "%a" C.print
let arb_cons = QCheck.make ~print:print_cons cons

(* Conjunctions of 0 to [n] constraints, to be passed to an instance's
   [inner env]. *)
let conj ?(n = 3) = QCheck.Gen.list_size (QCheck.Gen.int_range 0 n) cons
