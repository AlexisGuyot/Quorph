{
(* Minimal whitespace skipper for placeholder *)
}

rule token = parse
| [' ' '\t' '\r' '\n'] { token lexbuf }
| _ { token lexbuf }
