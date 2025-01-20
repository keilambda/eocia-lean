import Batteries.Data.RBMap
import EociaLean.Basic

namespace CVar

inductive Atom : Type
| int : Int → Atom
| var : Var → Atom
deriving Repr

namespace Atom

instance : ToString Atom where
  toString
  | int i => toString i
  | var v => v

end Atom

inductive Op : Type
| read : Op
| add : Atom → Atom → Op
| sub : Atom → Atom → Op
| neg : Atom → Op
deriving Repr

namespace Op
open Atom

instance : ToString Op where
  toString
  | read => "(read)"
  | add lhs rhs => s!"(+ {lhs} {rhs})"
  | sub lhs rhs => s!"(- {lhs} {rhs})"
  | neg e => s!"(- {e})"

end Op

inductive Exp : Type
| atm : Atom → Exp
| op : Op → Exp
deriving Repr

namespace Exp

instance : ToString Exp where
  toString
  | atm a => toString a
  | op o => toString o

end Exp

inductive Stmt : Type
| assign : Var → Exp → Stmt
deriving Repr

namespace Stmt

instance : ToString Stmt where
  toString
  | assign name exp => s!"{name} = {exp};"

end Stmt

inductive Tail : Type
| ret : Exp → Tail
| seq : Stmt → Tail → Tail
deriving Repr

abbrev Env : Type := Batteries.RBMap Var Exp compare

namespace Tail
open Stmt Exp Op Atom

protected def toString' : Tail → String
| ret e => s!"return {e};"
| seq s t => s!"{s}\n{t.toString'}"

instance : ToString Tail where
  toString := Tail.toString'

end Tail

structure CVar : Type where
  mk :: (env : Env) (blocks : Batteries.RBMap Label Tail compare)

end CVar
