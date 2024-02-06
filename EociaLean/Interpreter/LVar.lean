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
deriving Repr

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

def leaf? : Exp → Prop
| int _ => True
| var _ => True
| let_ _ _ _ => False
| op Op.read => True
| op (add _ _) => False
| op (sub _ _) => False
| op (neg _) => False

def exp? : Exp → Prop
| int _ => True
| var _ => True
| let_ _ a b => leaf? a ∧ exp? b
| op Op.read => True
| op (add a b) => exp? a ∧ exp? b
| op (sub a b) => exp? a ∧ exp? b
| op (neg a) => exp? a

partial def interpret (exp : Exp) (env : Env) : IO Int := match exp with
| int i => pure i
| var name => match env.find? name with
  | some e => e.interpret env
  | none => throw ∘ IO.userError $ "unbound variable: " ++ name
| let_ name val body => body.interpret (env.insert name val)
| op Op.read => String.toInt! <$> (IO.getStdin >>= (·.getLine))
| op (add lhs rhs) => Int.add <$> lhs.interpret env <*> rhs.interpret env
| op (sub lhs rhs) => Int.sub <$> lhs.interpret env <*> rhs.interpret env
| op (neg e) => Int.neg <$> e.interpret env

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
| exp@(int _) => exp
| var name => match env.find? name with
  | some i => i
  | none => var name
| exp@(let_ _ _ _) => exp
| exp@(op Op.read) => exp
| op (add a b) => peAdd a b
| op (sub a b) => peSub a b
| op (neg a) => peNeg a

def rebind (exp : Exp) (old new : Var) : Exp := match exp with
| i@(int _) => i
| v@(var name) => if name == old then var new else v
| let_ name val body => let_ (if name == old then new else name) (val.rebind old new) (body.rebind old new)
| o@(op Op.read) => o
| op (add lhs rhs) => op $ add (lhs.rebind old new) (rhs.rebind old new)
| op (sub lhs rhs) => op $ sub (lhs.rebind old new) (rhs.rebind old new)
| op (neg e) => op $ neg (e.rebind old new)

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
  (let_ "x" (int 1) (let_ "y" (int 2) (op (add (var "x") (var "y")))))
  |>.uniquify
  |>.run' default
  |>.run
  |> toString

#eval
  (let_ "x" (int 32) (op $ add (let_ "x" (int 10) (var "x")) (var "x")))
  |>.uniquify
  |>.run' default
  |>.run
  |> toString

end Exp

structure Program where
  mk :: (info : Env) (exp : Exp)

namespace Program

def LInt? : Program → Prop
| ⟨_, exp⟩ => exp.exp?

def interpret : Program → IO Int
| ⟨env, exp⟩ => exp.interpret env

def evaluate : Program → Program
| ⟨env, exp⟩ => ⟨env, exp.evaluate env⟩

def uniquify : Program → Program
| ⟨env, exp⟩ => let (exp', env', _) := exp.uniquify |>.run (env, 0) |>.run; ⟨env', exp'⟩

end Program
end LVar
