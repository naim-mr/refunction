let joinbwd = ref 2
let joinfwd = ref 2
let learn = ref false (* conflict-driven conditional termination *)
let meetbwd = ref 2
let version = ref false
let minimal = ref false
let refine = ref false
let retrybwd = ref 5
let analysis = ref "termination"
let domain = ref "boxes"
let fundom = ref "polyhedra"
let filename = ref ""
let main = ref "main"
let minimal = ref false
let compress = ref false (* false *)
let ordinals = ref false
let ordmax = ref 3
let cda = ref false
let cdamax = ref 2
let property = ref ""
let precondition = ref "true"
let time = ref true
let noinline = ref false
let size = ref 2 (* conflict-driven conditional termination *)
let start = ref 0.0
let stop = ref 0.0
let timebwd = ref false
let timefwd = ref false
let fmt = ref Format.std_formatter
let timeout = ref 300.0
let ctl_existential_equivalence = ref false
let tracefwd = ref false
let tracebwd = ref false
let dot = ref false (* output trees in graphviz dot format *)
let abort = ref false
let vulnerability = ref false
let resilience = ref false
let nowrap = ref false

exception Abort
exception Timeout

let json_output = ref false
let output_dir = ref "logs/"
let exectime = ref "1"
let ctltype = ref ""
let logfile = ref ""
let result = ref false
let f_log = ref stdout
let tree : Yojson.Safe.t ref = ref `Null
let vuln_res : Yojson.Safe.t ref = ref @@ `String "Not analyzed"

let from_json filename =
  let json = Yojson.Safe.from_file filename in
  let rec aux (json : Yojson.Safe.t) =
    match json with
    | `Assoc [] -> ()
    | `Assoc (("analysis", `String a) :: q) ->
        analysis := a;
        (* mirror the -atl flag, which also turns on resilience *)
        if String.equal a "atl" then resilience := true;
        aux (`Assoc q)
    | `Assoc (("property", `String a) :: q) ->
        property := a;
        aux (`Assoc q)
    | `Assoc (("domain", `String a) :: q) ->
        domain := a;
        aux (`Assoc q)
    | `Assoc (("precondition", `String a) :: q) ->
        precondition := a;
        aux (`Assoc q)
    | `Assoc (("ordinals", `Int i) :: q) ->
        ordmax := i;
        ordinals := true;
        aux (`Assoc q)
    | `Assoc (("joinbwd", `Int i) :: q) ->
        joinbwd := i;
        aux (`Assoc q)
    (* skip unknown keys (e.g. "description", "model") instead of aborting *)
    | `Assoc (_ :: q) -> aux (`Assoc q)
    | _ -> ()
  in
  aux json
