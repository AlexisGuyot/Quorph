open Cmdliner

let parse_cmd =
  let file = Arg.(required & pos 0 (some file) None & info [] ~docv:"PROG" ~doc:"Program file (.qp)") in
  Cmd.v (Cmd.info "parse" ~doc:"Parse a Quorph pipeline file")
    (Cmdliner.Term.(term_result (const Cmd_parse.run $ file)))

let type_cmd =
  let file = Arg.(required & pos 0 (some file) None & info [] ~docv:"PROG" ~doc:"Program file (.qp)") in
  Cmd.v (Cmd.info "type" ~doc:"Type-check a Quorph pipeline file")
    (Cmdliner.Term.(term_result (const Cmd_type.run $ file)))

let pp_cmd =
  let file = Arg.(required & pos 0 (some file) None & info [] ~docv:"PROG" ~doc:"Program file (.qp)") in
  Cmd.v (Cmd.info "pp" ~doc:"Pretty-print the program")
    (Cmdliner.Term.(term_result (const Cmd_pp.run $ file)))

let laws_cmd =
  Cmd.v (Cmd.info "laws" ~doc:"Run algebraic law checks (internal)")
    (Cmdliner.Term.(term_result (const Cmd_laws.run $ const ())))

let default_cmd =
  let doc = "Quorph-core validator CLI" in
  Cmd.group (Cmd.info "quorph" ~doc) [parse_cmd; type_cmd; pp_cmd; laws_cmd]

let () = exit (Cmd.eval default_cmd)
