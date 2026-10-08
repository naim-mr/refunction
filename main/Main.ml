(***************************************************)
(*                                                 *)
(*                        Main                     *)
(*                                                 *)
(*                  Caterina Urban                 *)
(*     École Normale Supérieure, Paris, France     *)
(*                   2012 - 2015                   *)
(*                                                 *)
(***************************************************)
open TerminationIterator
open CTLIterator
open ATLIterator
open Config
open C_Frontend
open Typed_syntax
open Domains

let parsePropertyStringNew str =
  let lex = Lexing.from_string str in
  try PropertyParserNew.file PropertyLexerNew.start lex with
  | PropertyParserNew.Error ->
      Format.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Format.eprintf "Parse Error (Invalid Token) near %s\n"
          (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseProperty filename =
  let f = open_in filename in
  let lex = Lexing.from_channel f in
  try
    lex.Lexing.lex_curr_p <-
      { lex.Lexing.lex_curr_p with Lexing.pos_fname = filename };
    let r = PropertyParserNew.file PropertyLexerNew.start lex in
    close_in f;
    r
  with
  | PropertyParserNew.Error ->
      Format.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Format.eprintf "Parse Error (Invalid Token) near %s\n"
          (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseCTLPropertyNew filename =
  let f = open_in filename in
  let lex = Lexing.from_channel f in
  try
    lex.Lexing.lex_curr_p <-
      { lex.Lexing.lex_curr_p with Lexing.pos_fname = filename };
    let res = CTLPropertyParser.prog CTLPropertyLexer.read lex in
    close_in f;
    CTLProperty.map (fun p -> parsePropertyStringNew p) res
  with
  | CTLPropertyParser.Error ->
      Format.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Format.eprintf "Parse Error (Invalid Token) near %s\n"
          (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseATLProperty filename =
  let f = open_in filename in
  let lex = Lexing.from_channel f in
  try
    lex.Lexing.lex_curr_p <-
      { lex.Lexing.lex_curr_p with Lexing.pos_fname = filename };
    let res = ATLPropertyParser.prog ATLPropertyLexer.read lex in
    close_in f;
    ATLProperty.map (fun p -> parsePropertyStringNew p) res
  with
  | ATLPropertyParser.Error ->
      Format.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Format.eprintf "Parse Error (Invalid Token) near %s\n"
          (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseCTLPropertyString_plain (property : string) =
  let lex = Lexing.from_string property in
  try
    lex.Lexing.lex_curr_p <-
      { lex.Lexing.lex_curr_p with Lexing.pos_fname = "string" };
    CTLPropertyParser.prog CTLPropertyLexer.read lex
  with
  | CTLPropertyParser.Error ->
      Format.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Format.eprintf "Parse Error (Invalid Token) near %s\n"
          (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseATLPropertyStringNew_plain (property : string) =
  let lex = Lexing.from_string property in
  try
    lex.Lexing.lex_curr_p <-
      { lex.Lexing.lex_curr_p with Lexing.pos_fname = "string" };
    ATLPropertyParser.prog ATLPropertyLexer.read lex
  with
  | ATLPropertyParser.Error ->
      Format.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Format.eprintf "Parse Error (Invalid Token) near %s\n"
          (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseCTLPropertyStringNew_plain (property : string) =
  let lex = Lexing.from_string property in
  try
    lex.Lexing.lex_curr_p <-
      { lex.Lexing.lex_curr_p with Lexing.pos_fname = "string" };
    CTLPropertyParser.prog CTLPropertyLexer.read lex
  with
  | CTLPropertyParser.Error ->
      Format.eprintf "Parse Error (Invalid Syntax) near %s\n"
        (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
      failwith "Parse Error"
  | Failure e ->
      if e == "lexing: empty token" then (
        Format.eprintf "Parse Error (Invalid Token) near %s\n"
          (Abstract_syntax.position_tostring lex.Lexing.lex_start_p);
        failwith "Parse Error")
      else failwith e

let parseCTLPropertyStringNew (property : string) =
  CTLProperty.map (fun p -> parsePropertyStringNew p)
  @@ parseCTLPropertyString_plain property

let parseATLPropertyString (property : string) =
  ATLProperty.map (fun p -> parsePropertyStringNew p)
  @@ parseATLPropertyStringNew_plain property

let parse_args () =
  Arg.parse
    [
      ( "-config",
        Arg.String (fun s -> Config.from_json s),
        "Set analysis configuration with a json file" );
      ( "-domain",
        Arg.String (fun s -> Config.domain := s),
        "Numerical Abstract Domain used" );
      ( "-nowrap",
        Arg.Unit (fun _ -> Config.nowrap := true),
        "Refine the backward analysis" );
      ( "-timeout",
        Arg.Float (fun d -> Config.timeout := d),
        "Maximal analysis time in seconds" );
      ( "-joinfwd",
        Arg.Int (fun i -> Config.joinfwd := i),
        "Widening delay in forward analysis" );
      ( "-joinbwd",
        Arg.Int (fun i -> Config.joinbwd := i),
        "Widening delay in backward analysis" );
      ("-main", Arg.String (fun s -> Config.main := s), "Analysis entry point");
      ( "-meetbwd",
        Arg.Int (fun i -> Config.meetbwd := i),
        "Dual widening delay in backward analysis" );
      ( "-minimal",
        Arg.Unit (fun _ -> Config.minimal := true),
        "Output analysis result only" );
      ( "-ordinals",
        Arg.Int
          (fun i ->
            Config.ordmax := i;
            Config.ordinals := true),
        "Set ordinals based analysis" );
      ( "-refine",
        Arg.Unit (fun _ -> Config.refine := true),
        "Refine the backward analysis" );
      ( "-retrybwd",
        Arg.Int (fun i -> Config.retrybwd := i),
        "Retry widening heuristic" );
      ( "-tracefwd",
        Arg.Unit (fun _ -> Config.tracefwd := true),
        "Forward analysis trace" );
      ( "-tracebwd",
        Arg.Unit (fun _ -> Config.tracebwd := true),
        "Backward analysis trace" );
      ( "-cda",
        Arg.Int
          (fun i ->
            Config.cda := true;
            Config.refine := true;
            Config.size := i),
        "Conflict-driven analysis" );
      ( "-termination",
        Arg.Unit (fun _ -> Config.analysis := "termination"),
        "Termination analysis" );
      ( "-nontermination",
        Arg.Unit (fun _ -> Config.analysis := "non-termination"),
        "Non-termination analysis" );
      ("-time", Arg.Unit (fun _ -> Config.time := true), "Track analysis time");
      ( "-timefwd",
        Arg.Unit (fun _ -> Config.timefwd := true),
        "Track forward analysis time" );
      ( "-timebwd",
        Arg.Unit (fun _ -> Config.timefwd := true),
        "Track backward analysis time" );
      ( "-ctl",
        Arg.String
          (fun s ->
            Config.analysis := "ctl";
            Config.property := s),
        "CTL analysis" );
      ( "-atl",
        Arg.String
          (fun s ->
            Config.analysis := "atl";
            Config.resilience := true;
            Config.property := s),
        "ATL analysis" );
      ( "-dot",
        Arg.Unit (fun _ -> Config.dot := true),
        "Output decision trees in dot format" );
      ( "-precondition",
        Arg.String (fun s -> Config.precondition := s),
        "Optional precondition that holds at the starts of the program" );
      ( "-ctl_existential_equivalence",
        Arg.Unit (fun _ -> Config.ctl_existential_equivalence := true),
        "Convert existential ctl properties to universal" );
      ( "-vulnerability",
        Arg.Unit (fun _ -> Config.vulnerability := true),
        "Vulnerability analysis" );
      ( "-resilience",
        Arg.Unit
          (fun _ ->
            Config.analysis := "termination";
            Config.resilience := true),
        "Termination Resilience analysis" );
      ( "-json_output",
        Arg.String
          (fun s ->
            Config.json_output := true;
            Config.output_dir := s),
        "Summary of the analysis in a json file" );
      ( "-json_output_std",
        Arg.Unit (fun _ -> Config.json_output := true),
        "Summary of the analysis as a json in stdout" );
    ]
    (fun s -> Config.filename := s)
    ""

let check_args () =
  if
    !Config.resilience
    && String.compare !Config.analysis "termination" <> 0
    && String.compare !Config.analysis "atl" <> 0
  then
    raise
      (Invalid_argument "Resilience analysis is avalaible only for termination");
  if String.compare !Config.filename "" = 0 && not !Config.version then
    raise (Invalid_argument "No Source File Specified");
  if
    String.compare !analysis "ctl" == 0
    && String.compare !domain "polyhedra" <> 0
  then (
    Config.domain := "polyhedra";
    Format.fprintf !fmt "Defaulting to Polyhedra for CTL analysis \n");
  if
    String.compare !property "" = 0
    && String.compare !analysis "termination" <> 0
    && String.compare !analysis "non-termination" <> 0
  then raise (Invalid_argument "No Property File Specified")

(* Factorised function to run termination analysis *)
let run_analysis analysis_function program () =
  try
    let start = Sys.time () in
    Config.result := analysis_function program !main;
    let stop = Sys.time () in
    let res = if !Config.result then "TRUE" else "UNKNOW" in
    Format.fprintf !fmt "Final Analysis Result: %s\n" res;
    if !time then exectime := string_of_float (stop -. start);
    Format.fprintf !fmt "Time: %f s\n" (stop -. start);
    Format.fprintf !fmt "\nDone.\n"
  with Config.Timeout ->
    Format.fprintf !fmt "\nThe Analysis Timed Out!\n";
    Format.fprintf !fmt "\nDone.\n"

(** The ranking domain selected by [-domain] and [-ordinals]. Built here, after
    the command line is parsed, so that [ordmax] is given to the domain as a
    functor argument instead of being read from [Config] by the domain. *)
let ranking_domain () : (module Sig.Ranking.RANKING_FUNCTION) =
  let affine : (module Sig.Ranking.FUNCTION) =
    match !domain with
    | "boxes" -> (module AP_Affines.AB)
    | "octagons" -> (module AP_Affines.AO)
    | "polyhedra" -> (module AP_Affines.AP)
    | _ -> raise (Invalid_argument "Unknown Abstract Domain")
  in
  let module F = (val affine) in
  let leaf : (module Sig.Ranking.FUNCTION) =
    if !ordinals then
      (module AP_Ordinals.AP_OrdinalValued
                (struct
                  let ordmax = !Config.ordmax
                end)
                (F))
    else (module F)
  in
  let module L = (val leaf) in
  (module Decision_Tree.Decision_Tree (L))

let termination_iterator_new () : (module Semantics.SEMANTIC) =
  let module D = (val ranking_domain ()) in
  (module TerminationIterator (D))

let ctl_iterator_new () : (module Semantics.SEMANTIC) =
  let module D = (val ranking_domain ()) in
  (module CTLIterator (D))

let atl_iterator_new () : (module Semantics.SEMANTIC) =
  let module D = (val ranking_domain ()) in
  (module ATLIterator (D))

let run_termination_new program =
  let module S = (val termination_iterator_new ()) in
  try
    let parsedPrecondition =
      if !precondition <> "" then Some (parsePropertyStringNew !precondition)
      else None
    in
    Config.result := S.analyze ~precondition:parsedPrecondition program;
    if !Config.result then Format.printf "\nFinal Analysis Result: TRUE\n"
    else Format.printf "\nFinal Analysis Result: UNKNOWN\n"
  with Config.Timeout ->
    Format.fprintf !fmt "\nThe Analysis Timed Out!\n";
    Format.fprintf !fmt "\nDone.\n"
(* TODO: precondition analysis *)

let run_non_termination program =
  let ntprog, labels = Typed_syntax.nt_prog program in
  let parsedPrecondition =
    if !precondition <> "" then Some (parsePropertyStringNew !precondition)
    else None
  in
  let nonterm label =
    CTLProperty.AG
      (CTLProperty.EF
         (CTLProperty.Atomic
            ( ( Typed_syntax.T_bool_const True,
                Abstract_syntax.A_BOOL,
                Abstract_syntax.extent_unknown ),
              Some (Z.to_string label) )))
  in
  let rec create_prop label =
    match label with
    | [] -> None
    | l :: [] -> Some (nonterm l)
    | l :: q -> Some (CTLProperty.OR (nonterm l, Option.get (create_prop q)))
  in
  match create_prop (List.map fst labels) with
  | None -> Format.printf "\nFinal Analysis Result: UNKNOWN\n"
  | Some p -> (
      try
        let module Nonterm = (val ctl_iterator_new ()) in
        Config.result :=
          Nonterm.analyze ~precondition:parsedPrecondition
            ~property:(Semantics.Ctl p) ntprog;
        if !Config.result then
          Format.printf "\nFinal Analysis Result: false(TERM)\n"
        else Format.printf "\nFinal Analysis Result: UNKNOWN\n"
      with Config.Timeout ->
        Format.fprintf !fmt "\nThe Analysis Timed Out!\n";
        Format.fprintf !fmt "\nDone.\n")

(* TODO: precondition analysis *)
let run_ctl_ast_new (module S : Semantics.SEMANTIC) prog property =
  let starttime = Sys.time () in
  (* let parsedPrecondition = parsePropertyString !precondition in
  let precondition =
    fst
    @@ AbstractSyntax.StringMap.find ""
    @@ ItoA.property_itoa_of_prog prog !main parsedPrecondition
  in *)
  let parsedPrecondition =
    if !precondition <> "" then Some (parsePropertyStringNew !precondition)
    else None
  in
  let analyze = S.analyze in
  Config.result :=
    analyze ~precondition:parsedPrecondition ~property:(Ctl property) prog;
  if !time then (
    let stoptime = Sys.time () in
    exectime := string_of_float (stoptime -. starttime);
    Format.fprintf !fmt "\nTime: %f" (stoptime -. starttime));
  if !Config.result then Format.fprintf !fmt "\nFinal Analysis Result: TRUE\n"
  else Format.fprintf !fmt "\nFinal Analysis Result: UNKNOWN\n"

let run_cda s : (module Cda.CDA_ITERATOR) =
  let module D = (val s : Semantics.SEMANTIC) in
  (module Cda.Make (D))

let run_atl_ast (module S : Semantics.SEMANTIC) prog property =
  let starttime = Sys.time () in
  (* let parsedPrecondition = parsePropertyString !precondition in
    let precondition =
      fst
      @@ AbstractSyntax.StringMap.find ""
      @@ ItoA.property_itoa_of_prog prog !main parsedPrecondition
    in *)
  let parsedPrecondition =
    if !precondition <> "" then Some (parsePropertyStringNew !precondition)
    else None
  in
  let analyze = S.analyze in
  Config.result :=
    analyze ~precondition:parsedPrecondition ~property:(Atl property) prog;
  if !time then (
    let stoptime = Sys.time () in
    exectime := string_of_float (stoptime -. starttime);
    Format.fprintf !fmt "\nTime: %f" (stoptime -. starttime));
  if !Config.result then Format.fprintf !fmt "\nFinal Analysis Result: TRUE\n"
  else Format.fprintf !fmt "\nFinal Analysis Result: UNKNOWN\n"

let get_semantic_new () =
  match !analysis with
  | "termination" -> termination_iterator_new ()
  | "non-termination" | "ctl" -> ctl_iterator_new ()
  | "atl" -> atl_iterator_new ()
  | _ -> raise (Invalid_argument "Unknown Analysis")

let doit () =
  (* Parsing cli args -> into Config ref variables*)
  parse_args ();
  check_args ();
  (* Get the iterator for the demanded analysis *)
  (* parse the program*)
  let prog = C_Frontend.parse_file !Config.filename in

  let semantic = get_semantic_new () in

  if not !minimal then (
    Format.fprintf !fmt "\nAbstract typed Syntax:\n";
    Typed_syntax.pp_prog !fmt prog);
  let module S = (val semantic : Semantics.SEMANTIC) in
  (* Launch the analysis and get the returned output "true" or "unknow" *)
  (if !Config.cda then
     let module C = (val run_cda semantic : Cda.CDA_ITERATOR) in
     let precondition = parsePropertyStringNew !precondition in
     let property =
       match !analysis with
       | "termination" -> Semantics.Other
       | "ctl" -> Ctl (parseCTLPropertyStringNew !Config.property)
       | "atl" -> Atl (parseATLPropertyString !Config.property)
       | _ -> raise (Invalid_argument "Unknow Property")
     in
     Config.result := C.analyze ~property ~precondition:(Some precondition) prog
   else
     match !analysis with
     | "termination" -> run_termination_new prog
     | "non-termination" ->
         Config.refine := false;
         run_non_termination prog
     | "ctl" ->
         run_ctl_ast_new
           (module S)
           prog
           (parseCTLPropertyStringNew !Config.property)
     | "atl" ->
         run_atl_ast (module S) prog (parseATLPropertyString !Config.property)
     | _ -> raise (Invalid_argument "Unknow Property"));
  if !Config.json_output then Regression.output_json ()
(* if !Config.vulnerability then ( *)
(* Launch the vulnerability analysisand output the infered variables *)
(* let varlist =
      List.map snd @@ List.of_seq @@ AbstractSyntax.StringMap.to_seq vars
    in
    Vulnerability.analyse S.D.vulnerable varlist func !S.bwdInvMap;
    Format.fprintf !fmt " \n %s \n"
      (Yojson.Safe.pretty_to_string !Config.vuln_res));  *)

let _ = doit ()
