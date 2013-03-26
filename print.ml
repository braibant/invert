include PPrintEngine 
include PPrintCombinators

let format fmt =  Printf.ksprintf string fmt 

let int i = string (string_of_int i)
    
let bool = function true ->  string "true"
  | false -> string "false"

let run out doc = ToChannel.pretty 1. 80 out doc

let stripes doc = 
  let fringe = repeat 6 (char '=') in 
  group (fringe ^/^ doc ^/^  fringe )

let print doc = 
  Printf.printf "%a" run doc 

let eprint doc =
  Printf.eprintf "%a\n" run doc

  (* from a coq pp_command to a Pprint document *)
let pp x = string ( Pp.string_of_ppcmds x)
  
let constr x = pp (Printer.pr_constr x)
let goal gl  = pp (Printer.pr_goal gl)  
let id  x    = pp (Names.Id.print x)
let name   = function 
  | Names.Anonymous -> string "_"
  | Names.Name x -> id x
    
let constrs l = separate_map hardline constr l
let rel_context ctx = 
  surround_separate_map 2 1
    (brackets empty) 				(* when void *)
    lbracket
    (semi ^^ break 1)
    rbracket
    (fun (n, _, ty) -> 
      name n ^/^ colon ^/^ constr ty
    )
    (
      ctx
    )   
