namespace Lint

-- AST
mutual
inductive Exp : Type
| int : Int → Exp
| op : Op → Exp
deriving Repr

inductive Op : Type
| read : Op
| add : Exp → Exp → Op
| sub : Exp → Exp → Op
| neg : Exp → Op
deriving Repr
end

structure Program where
  mk :: (info : α) (exp : Exp)

open Exp Op

def leaf? : Exp → Prop
| int _ => True
| op Op.read => True
| op (add _ _) => False
| op (sub _ _) => False
| op (neg _) => False

def exp? : Exp → Prop
| int _ => True
| op Op.read => True
| op (add a b) => exp? a ∧ exp? b
| op (sub a b) => exp? a ∧ exp? b
| op (neg a) => exp? a

def Lint? : Program → Prop
| ⟨_, exp⟩ => exp? exp

def interpExp : Exp → IO Int
| int i => pure i
| op Op.read => String.toInt! <$> (IO.getStdin >>= IO.FS.Stream.getLine)
| op (add a b) => Int.add <$> (interpExp a) <*> (interpExp b)
| op (sub a b) => Int.sub <$> (interpExp a) <*> (interpExp b)
| op (neg i) => Int.neg <$> interpExp i

def interpLint : Program → IO Int
| ⟨_, exp⟩ => interpExp exp

def peAdd : Exp → Exp → Exp
| int a, int b => int (a + b)
| a, b => op $ add a b

def peSub : Exp → Exp → Exp
| int a, int b => int (a - b)
| a, b => op $ sub a b

def peNeg : Exp → Exp
| int i => int (Int.neg i)
| other => op $ neg other

def peExp : Exp → Exp
| int a => int a
| op Op.read => op $ Op.read
| op (add a b) => peAdd a b
| op (sub a b) => peSub a b
| op (neg a) => peNeg a

def peLint : Program → Program
| ⟨i, exp⟩ => ⟨i, peExp exp⟩

end Lint
