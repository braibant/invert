
open Tacmach
open Tacticals
open Tacexpr
open Tacinterp
open Genarg

TACTIC EXTEND invert
| ["invert"  ident(h)] ->     [Invert_tactic.invert h]
  END

TACTIC EXTEND invert2
| ["diag" ident(h) ident(name)] ->     [Invert_tactic.pose_diag h name]
END;;
