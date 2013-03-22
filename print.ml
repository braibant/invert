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
