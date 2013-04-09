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
   
(** I have reimplemented part of a pretty printer for Coq, in order to
    print the telescopes in a meaningful manner. I think it is quite
    risky to have two printers at the same time, but I do not want to
    reimplement everything at once. *)
let rec constr' (env: Names.Name.t list) t = 
  match Term.kind_of_term t with 
  | Term.Rel i -> 
    begin try (match List.nth env (i - 1) with 
    | Names.Anonymous -> underscore ^^ int i 
    | n -> name n)
      with _ -> at ^^ int i
    end
  | Term.Var x -> id x 
  | Term.App (hd,args) -> 
    surround_separate_map 2 1 
      (constr' env hd)
      (constr' env hd)
      (break 1)
      (empty)
      (fun c -> parens (constr' env c))
      (Array.to_list args)
  | Term.Lambda (n,ty,c) -> 
    group (group (group (string "fun" ^/^ parens (name n ^/^ colon ^/^ constr' env ty))
    ^/^ string "=>" )
    ^/^ parens (constr' (n :: env) c))
  | Term.Prod (n,ty,c) -> 
    group (string "forall" ^/^ parens (name n ^/^ colon ^/^ constr' env ty))
    ^/^ string "," 
    ^/^ parens (constr' (n :: env) c)
  | Term.LetIn (n,body,ty,c) -> 
    group (string "let" ^/^ parens (name n ^/^ colon ^/^ constr' env ty))
    ^/^ string ":=" ^/^  group (constr' (env)c) 
    ^/^ string "in" ^/^ parens (constr' (n::env)c)
  | Term.Const c -> pp (Printer.pr_constant (Global.env ()) c)
  | Term.Ind c  -> pp (Printer.pr_inductive (Global.env ()) c) 
  | Term.Construct c  -> pp (Printer.pr_constructor (Global.env ()) c) 
  | Term.Case (ci,p,c,ac) -> 
    group (group (string "match" ^/^ constr' env c) 
    ^/^ group (string "returnclause" ^/^ constr' env p))
    ^^
      group (surround 2 2 
	       (string "with" )  
	       (string "TODO")
	       (string "end"))
    
  | Term.Sort s -> pp (Printer.pr_sort s)
  | _ -> string "TODO"
  
  
let telescope ctx = 
  let rec aux env = function 
    | [] -> empty
    | (n,_,ty) :: q  ->
      group (name n ^/^ colon ^/^ constr' env ty) 
      ^^ semi  ^^ break 1
      ^^ aux (n::env) q
  in 
  brackets (aux [] ctx)
    
      

let messages l =     
  separate_map hardline (fun (msg,body) -> group (string msg ^/^ body)) l
  
