
open Tacmach
open Tacticals
open Tacexpr
open Tacinterp
open Genarg

TACTIC EXTEND invert
| ["invert" ident(h)] ->     [Invert_tactic.invert h]
END;;

