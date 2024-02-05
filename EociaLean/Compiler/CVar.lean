import Std.Data.RBMap
import EociaLean.Basic

namespace CVar

inductive Atom : Type
| int : Int → Atom
| var : Var → Atom
deriving Repr

inductive Op : Type
| read : Op
| add : Atom → Atom → Op
| sub : Atom → Atom → Op
| neg : Atom → Op
deriving Repr

inductive Exp : Type
| atm : Atom → Exp
| op : Op → Exp
deriving Repr

inductive Stmt : Type
| assign : Var → Exp → Stmt
deriving Repr

inductive Tail : Type
| ret : Exp → Tail
| seq : Stmt → Tail → Tail
deriving Repr

abbrev Env : Type := Std.RBMap Var Int compare

structure CVar : Type where
  mk :: (env : Env) (blocks : Std.RBMap Label Tail compare)

end CVar
