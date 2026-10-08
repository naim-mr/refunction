(*   
   ********* Ordinal-Valued Ranking Functions Abstract Domain ************
       Copyright (C) 2012-2014 by Caterina Urban. All rights reserved.
*)

open Apron
open AP_Affines
open Sig.Ranking

module AP_OrdinalValued (F : FUNCTION) : FUNCTION = struct
  module B = F.B

  type rank = F.rank
  type env = F.env
  type t = F.t * F.t list
  type dim = F.dim

  let env (f, _) = F.env f

  let set_env (env : env) ((f, ff) : t) : t =
    (F.set_env env f, List.map (fun f -> F.set_env env f) ff)

  let init_env () = F.init_env ()
  let bot e = (F.bot e, [])
  let zero e = (F.zero e, [])
  let top e = (F.top e, [])
  let is_bot (f, _) = F.is_bot f
  let defined (f, _) = F.defined f
  let is_top (f, _) = F.is_top f
  let reinit (f, ff) = (F.reinit f, ff)

  let rec is_eq b (f1, ff1) (f2, ff2) =
    let env = F.env f1 in
    match (ff1, ff2) with
    | [], [] -> F.is_eq b f1 f2
    | [], y :: ys -> F.is_eq b (F.zero env) y && is_eq b (f1, []) (f2, ys)
    | x :: xs, [] -> F.is_eq b x (F.zero env) && is_eq b (f1, xs) (f2, [])
    | x :: xs, y :: ys -> F.is_eq b x y && is_eq b (f1, xs) (f2, ys)

  let domain_eq b (f1, ff1) (f2, ff2) =
    let env = B.env b in
    let rec aux b ff1 ff2 =
      match (ff1, ff2) with
      | [], [] -> b
      | [], _ -> aux b [ F.zero env ] ff2
      | _, [] -> aux b ff1 [ F.zero env ]
      | x :: xs, y :: ys -> aux (F.domain_eq b x y) xs ys
    in
    aux (F.domain_eq b f1 f2) ff1 ff2

  let is_leq k b (f1, ff1) (f2, ff2) =
    let env = B.env b in
    (* aux ff1 ff2 returns the domain on which ff1 and ff2 are equal,
       and raises an Exit exception if there is a point where ff1 > ff2. *)
    let rec aux ff1 ff2 =
      match (ff1, ff2) with
      | [], [] -> b
      | [], _ -> aux [ F.zero env ] ff2
      | _, [] -> aux ff1 [ F.zero env ]
      | x :: xs, y :: ys ->
          let r = aux xs ys in
          if F.is_leq k r x y then F.domain_eq r x y else raise Exit
    in
    if F.defined f1 && F.defined f2 then
      try
        let r = aux ff1 ff2 in
        F.is_leq k r f1 f2
      with Exit -> false
    else F.is_leq k b f1 f2

  let join ?(controllable = false) k b (f1, ff1) (f2, ff2) =
    let env = B.env b in
    let rec aux i ff1 ff2 =
      match (ff1, ff2) with
      | [], [] -> ( match i with 0 -> [] | _ -> [ F.successor (F.zero env) ])
      | [], y :: ys -> (
          let x = F.zero env in
          let z = F.join ~controllable k b x y in
          match i with
          | 0 -> if F.defined z then z :: aux 0 [] ys else x :: aux 1 [] ys
          | _ ->
              if F.defined z then F.successor z :: aux 0 [] ys
              else F.successor x :: aux 1 [] ys)
      | x :: xs, [] -> (
          let y = F.zero env in
          let z = F.join ~controllable k b x y in
          match i with
          | 0 -> if F.defined z then z :: aux 0 xs [] else y :: aux 1 xs []
          | _ ->
              if F.defined z then F.successor z :: aux 0 xs []
              else F.successor y :: aux 1 xs [])
      | x :: xs, y :: ys -> (
          let z = F.join ~controllable k b x y in
          match i with
          | 0 ->
              if F.defined z then z :: aux 0 xs ys
              else F.zero env :: aux 1 xs ys
          | _ ->
              if F.defined z then F.successor z :: aux 0 xs ys
              else F.successor (F.zero env) :: aux 1 xs ys)
    in
    let f = F.join ~controllable k b f1 f2 in
    if F.defined f then
      let ff = aux 0 ff1 ff2 in
      if List.length ff > !Config.ordmax then (F.top env, []) else (f, ff)
    else if
      (* f = Bot OR f = Top *)
      F.is_bot f
    then (f, []) (* f = Bot *)
    else if
      (* f = Top *)
      F.defined f1 && F.defined f2
    then
      let ff = aux 1 ff1 ff2 in
      if List.length ff > !Config.ordmax then (f, []) else (F.zero env, ff)
    else (f, [])

  let plus b (f1, ff1) (f2, ff2) =
    let env = B.env b in
    let rec aux i ff1 ff2 =
      match (ff1, ff2) with
      | [], [] -> ( match i with 0 -> [] | _ -> [ F.successor (F.zero env) ])
      | [], y :: ys -> (
          let x = F.zero env in
          let z = F.plus b x y in
          match i with
          | 0 -> if F.defined z then z :: aux 0 [] ys else x :: aux 1 [] ys
          | _ ->
              if F.defined z then F.successor z :: aux 0 [] ys
              else F.successor x :: aux 1 [] ys)
      | x :: xs, [] -> (
          let y = F.zero env in
          let z = F.plus b x y in
          match i with
          | 0 -> if F.defined z then z :: aux 0 xs [] else y :: aux 1 xs []
          | _ ->
              if F.defined z then F.successor z :: aux 0 xs []
              else F.successor y :: aux 1 xs [])
      | x :: xs, y :: ys -> (
          let z = F.plus b x y in
          match i with
          | 0 ->
              if F.defined z then z :: aux 0 xs ys
              else F.zero env :: aux 1 xs ys
          | _ ->
              if F.defined z then F.successor z :: aux 0 xs ys
              else F.successor (F.zero env) :: aux 1 xs ys)
    in
    let f = F.plus b f1 f2 in
    if F.defined f then
      let ff = aux 0 ff1 ff2 in
      if List.length ff > !Config.ordmax then (F.top env, []) else (f, ff)
    else if
      (* f = Bot OR f = Top *)
      F.is_bot f
    then (f, []) (* f = Bot *)
    else if
      (* f = Top *)
      F.defined f1 && F.defined f2
    then
      let ff = aux 1 ff1 ff2 in
      if List.length ff > !Config.ordmax then (f, []) else (F.zero env, ff)
    else (f, [])

  let learn b (f1, ff1) (f2, ff2) =
    let env = B.env b in
    let rec aux i ff1 ff2 =
      match (ff1, ff2) with
      | [], [] -> ( match i with 0 -> [] | _ -> [ F.successor (F.zero env) ])
      | [], y :: ys -> (
          let x = F.zero env in
          let z = F.learn b x y in
          match i with
          | 0 -> if F.defined z then z :: aux 0 [] ys else x :: aux 1 [] ys
          | _ ->
              if F.defined z then F.successor z :: aux 0 [] ys
              else F.successor x :: aux 1 [] ys)
      | x :: xs, [] -> (
          let y = F.zero env in
          let z = F.learn b x y in
          match i with
          | 0 -> if F.defined z then z :: aux 0 xs [] else y :: aux 1 xs []
          | _ ->
              if F.defined z then F.successor z :: aux 0 xs []
              else F.successor y :: aux 1 xs [])
      | x :: xs, y :: ys -> (
          let z = F.learn b x y in
          match i with
          | 0 ->
              if F.defined z then z :: aux 0 xs ys
              else F.zero env :: aux 1 xs ys
          | _ ->
              if F.defined z then F.successor z :: aux 0 xs ys
              else F.successor (F.zero env) :: aux 1 xs ys)
    in
    let f = F.learn b f1 f2 in
    if F.defined f then
      let ff = aux 0 ff1 ff2 in
      if List.length ff > !Config.ordmax then (F.top env, []) else (f, ff)
    else if
      (* f = Bot OR f = Top *)
      F.is_bot f
    then (f, []) (* f = Bot *)
    else if
      (* f = Top *)
      F.defined f1 && F.defined f2
    then
      let ff = aux 1 ff1 ff2 in
      if List.length ff > !Config.ordmax then (f, []) else (F.zero env, ff)
    else (f, [])

  let widen ?(jokers = 0) b (f1, ff1) (f2, ff2) =
    let env = B.env b in
    (*let rec aux ff1 ff2 =
      match ff1,ff2 with
      | [],[] -> []
      | [],y::ys -> y::(aux [] ys)
      | x::xs,[] -> x::(aux xs [])
      | x::xs,y::ys -> (F.widen b x y)::(aux xs ys)
      in
      let f = F.widen b f1 f2 in
      if (F.defined f)
      then
      let ff = aux ff1 ff2 in
      if (List.exists (fun x -> F.is_top x) ff)
      then (F.top env,[])
      else (f,ff)
      else (f,[])*)
    let succ ff =
      match ff with
      | [] -> [ F.successor (F.zero env) ]
      | x :: xs -> F.successor x :: xs
    in
    let rec aux i ff1 ff2 =
      match (ff1, ff2) with
      | [], [] -> []
      | [], y -> aux i y ff2
      | x, [] -> aux i ff1 x
      | x :: xs, y :: ys ->
          let z = if i > 0 then F.widen b x y else y in
          if F.is_top z then F.zero env :: aux (i - 1) xs (succ ys)
          else z :: aux (i - 1) xs ys
    in
    let i = !Config.ordmax + 1 - jokers in
    if F.is_top f1 || F.is_top f2 then (F.widen b f1 f2, [])
    else
      let f = if i > 0 then F.widen b f1 f2 else f2 in
      if F.is_top f then
        let ff = aux (i - 1) ff1 (succ ff2) in
        if List.length ff > !Config.ordmax then top env else (F.zero env, ff)
      else if F.defined f then
        let ff = aux (i - 1) ff1 ff2 in
        if List.length ff > !Config.ordmax then top env else (f, ff)
      else (f, [])

  let extend b1 b2 (f1, ff1) (f2, ff2) =
    let env = B.env b1 in
    let rec aux ff1 ff2 =
      match (ff1, ff2) with
      | [], [] -> []
      (*| [],y::ys -> y::(aux [] ys)
        | x::xs,[] -> x::(aux xs [])*)
      | [], y :: ys -> aux [ F.zero env ] ff2
      | x :: xs, [] -> aux ff1 [ F.zero env ]
      | x :: xs, y :: ys -> F.extend b1 b2 x y :: aux xs ys
    in
    let f = F.extend b1 b2 f1 f2 in
    if F.defined f then
      let ff = aux ff1 ff2 in
      if List.exists (fun x -> F.is_top x) ff then (F.top env, []) else (f, ff)
    else (f, [])

  (**)

  let reset (f, ff) = (F.reset f, [])
  let predecessor (f, ff) = (F.predecessor f, ff)
  let successor (f, ff) = (F.successor f, ff)

  let bwd_assign (f, ff) e =
    let env = F.env f in
    let rec aux i ff =
      match ff with
      | [] -> ( match i with 0 -> [] | _ -> [ F.successor (F.zero env) ])
      | x :: xs -> (
          let x = F.predecessor (F.bwd_assign x e) in
          match i with
          | 0 -> if F.defined x then x :: aux 0 xs else F.zero env :: aux 1 xs
          | _ ->
              if F.defined x then F.successor x :: aux 0 xs
              else F.successor (F.zero env) :: aux 1 xs)
    in
    if F.defined f then
      let f = F.bwd_assign f e in
      if F.defined f then
        let ff = aux 0 ff in
        if List.length ff > !Config.ordmax then (F.top env, []) else (f, ff)
      else if
        (* f = Bot OR f = Top *)
        F.is_bot f
      then (f, []) (* f = Bot *)
      else (* f = Top *)
        let ff = aux 1 ff in
        if List.length ff > !Config.ordmax then (f, []) else (F.zero env, ff)
    else (f, [])

  let filter (f, ff) e = (F.filter f e, ff)

  (**)

  let print fmt (f, ff) =
    let rec aux fmt (ff, i) =
      match ff with
      | [] -> ()
      | x :: xs ->
          if i > 1 then
            Format.fprintf fmt "%a (%a)⍵^%i + " aux (xs, i + 1) F.print x i
          else Format.fprintf fmt "%a (%a)⍵ + " aux (xs, i + 1) F.print x
    in
    Format.fprintf fmt "%a%a" aux (ff, 1) F.print f
end

module OB = AP_OrdinalValued (AB)
module OO = AP_OrdinalValued (AO)
module OP = AP_OrdinalValued (AP)
