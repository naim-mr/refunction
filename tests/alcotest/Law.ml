(* Shared vocabulary of the law functors. A law functor takes a domain and its
   samples, and returns its tests as a [Law.S]. *)

module type S = sig
  val tests : unit Alcotest.test_case list
end

(* [case prefix name f] names the test "prefix: name". *)
let case prefix name f = Alcotest.test_case (prefix ^ ": " ^ name) `Quick f

(* [holds what b] fails with message [what] when [b] is false. *)
let holds what b = Alcotest.(check bool) what true b

(* [forall xs p]: [p] holds on every sample; [forall2 xs p]: on every pair. *)
let forall xs p = List.for_all p xs
let forall2 xs p = List.for_all (fun a -> List.for_all (p a) xs) xs
