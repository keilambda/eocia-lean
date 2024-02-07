import Std.Data.RBMap
import EociaLean.Basic

namespace LVar

-- AST
mutual
inductive Exp : Type
| int : Int → Exp
| var : Var → Exp
| let_ : Var → Exp → Exp → Exp
| op : Op → Exp
deriving Repr, DecidableEq

inductive Op : Type
| read : Op
| add : Exp → Exp → Op
| sub : Exp → Exp → Op
| neg : Exp → Op
deriving Repr
end

abbrev Env : Type := Std.RBMap Var Exp compare

mutual
open Exp Op

def Op.toString' : Op → String
| Op.read => "(read)"
| Op.add lhs rhs => s!"(+ {lhs.toString'} {rhs.toString'})"
| Op.sub lhs rhs => s!"(- {lhs.toString'} {rhs.toString'})"
| Op.neg e => s!"(- {e.toString'})"

def Exp.toString' : Exp → String
| int i => toString i
| var name => name
| let_ name val body => s!"(let ([{name} {val.toString'}]) {body.toString'})"
| op o => o.toString'

instance : ToString Exp where
  toString := Exp.toString'

instance : ToString Op where
  toString := Op.toString'

end

namespace Exp
open Op

partial def interpret (exp : Exp) : StateT Env IO Int := match exp with
| int i => pure i
| var name => do
  match (← get).find? name with
  | some e => e.interpret
  | none => throw ∘ IO.userError $ "unbound variable: " ++ name
| let_ name val body => do
  modify (·.insert name val)
  body.interpret
| op Op.read => String.toInt! <$> (IO.getStdin >>= (·.getLine))
| op (add lhs rhs) => Int.add <$> lhs.interpret <*> rhs.interpret
| op (sub lhs rhs) => Int.sub <$> lhs.interpret <*> rhs.interpret
| op (neg e) => Int.neg <$> e.interpret

private def peAdd : Exp → Exp → Exp
| int a, int b => int (a + b)
| a, b => op $ add a b

private def peSub : Exp → Exp → Exp
| int a, int b => int (a - b)
| a, b => op $ sub a b

private def peNeg : Exp → Exp
| int i => int (Int.neg i)
| other => op $ neg other

def evaluate (exp : Exp) (env : Env) : Exp := match exp with
| i@(int _) => i
| v@(var name) => env.find? name |>.getD v
| l@(let_ _ _ _) => l
| o@(op Op.read) => o
| op (add a b) => peAdd a b
| op (sub a b) => peSub a b
| op (neg a) => peNeg a

/-- `rebind` traverses `exp` and rebinds each occurrence of the `old` binding (both `Exp.var` and
`Exp.let_`) to `new`. -/
def rebind (exp : Exp) (old new : Var) : Exp := match exp with
| i@(int _) => i
| v@(var name) => if name == old then var new else v
| let_ name val body => let_ (if name == old then new else name) (val.rebind old new) (body.rebind old new)
| o@(op Op.read) => o
| op (add lhs rhs) => op $ add (lhs.rebind old new) (rhs.rebind old new)
| op (sub lhs rhs) => op $ sub (lhs.rebind old new) (rhs.rebind old new)
| op (neg e) => op $ neg (e.rebind old new)

/-- `uniquify` traverses `exp` and returns a new `Exp` with all variable names made unique.
It keeps track of the environment and the number of unique variables generated. -/
partial def uniquify : Exp → StateM (Env × Nat) Exp
| let_ name val body => do
  let name' ← getModify (·.map id Nat.succ) <&> (λ (_, n) => s!"{name}.{n}") -- poor man's `gensym`
  let val' ← val.rebind name name' |>.uniquify
  let body' ← body.rebind name name' |>.uniquify
  modify (·.map (λ env => env.erase name |>.insert name' val') id)
  pure (let_ name' val' body')
| i@(int _) => pure i
| v@(var _) => pure v
| e@(op Op.read) => pure e
| op (add lhs rhs) => op <$> (add <$> lhs.uniquify <*> rhs.uniquify)
| op (sub lhs rhs) => op <$> (sub <$> lhs.uniquify <*> rhs.uniquify)
| op (neg e) => (op ∘ neg) <$> e.uniquify

#eval
  ((let_  "x"   (int 1) (let_ "y"   (int 2) (op (add (var "x")   (var "y"))))) |>.uniquify |>.run' default |>.run)
  = (let_ "x.0" (int 1) (let_ "y.1" (int 2) (op (add (var "x.0") (var "y.1")))))

#eval
  ((let_  "x"   (int 32) (op (add (let_ "x"     (int 10) (var "x"))     (var "x")))) |>.uniquify |>.run' default |>.run)
  = (let_ "x.0" (int 32) (op (add (let_ "x.0.1" (int 10) (var "x.0.1")) (var "x.0"))))

end Exp

structure Program where
  mk :: (env : Env) (exp : Exp)

namespace Program

def interpret : Program → IO Int
| ⟨env, exp⟩ => exp.interpret |>.run' env

def evaluate : Program → Program
| ⟨env, exp⟩ => ⟨env, exp.evaluate env⟩

def uniquify : Program → Program
| ⟨env, exp⟩ => let (exp', env', _) := exp.uniquify |>.run (env, 0) |>.run; ⟨env', exp'⟩

end Program
end LVar
