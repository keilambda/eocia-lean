import Std.Data.RBMap
import EociaLean.Basic

namespace LVarMon

inductive Atom : Type
| int : Int → Atom
| var : Var → Atom
deriving Repr

namespace Atom

instance : ToString Atom where
  toString
  | int i => toString i
  | var name => name

end Atom

inductive Op : Type
| read : Op
| add : Atom → Atom → Op
| sub : Atom → Atom → Op
| neg : Atom → Op
deriving Repr

namespace Op

instance : ToString Op where
  toString
  | read => "(read)"
  | add a b => s!"(+ {a} {b})"
  | sub a b => s!"(- {a} {b})"
  | neg a => s!"(- {a})"

end Op

inductive Exp : Type
| atm : Atom → Exp
| let_ : Var → Exp → Exp → Exp
| op : Op → Exp
deriving Repr

abbrev Env : Type := Std.RBMap Var Atom compare

namespace Exp
open Atom Op

protected def toString' : Exp → String
| atm a => toString a
| let_ name val body => s!"(let ([{name} {val.toString'}]) {body.toString'})"
| op o => toString o

instance : ToString Exp where
  toString := Exp.toString'

end Exp

structure Program where
  mk :: (env : Env) (exp : Exp)

end LVarMon
