inductive Exp : Type -> Type where
| IntE : Int -> Exp IntE
| Read : Exp IntE
| Negate : Exp IntE -> Exp IntE
| Minus : Exp IntE -> Exp IntE -> Exp IntE
| Plus : Exp IntE -> Exp IntE -> Exp IntE

open Exp

structure Program (info : Type) := exp : (Exp Int)

def leaf? : Exp Int -> Prop
| IntE _ => True
| Read => False
| Negate _ => False
| Plus _ _ => False
| Minus _ _ => False

def exp? : Exp Int -> Prop
| IntE _ => True
| Read => True
| Negate e => exp? e
| Plus e1 e2 => exp? e1 ∧ exp? e2
| Minus e1 e2 => exp? e1 ∧ exp? e2

def Lint? : Program info -> Prop
| {exp} => exp? exp

def interpExp : Exp Int -> IO Int
| IntE i => pure i
| Read => String.toInt! <$> (IO.getStdin >>= IO.FS.Stream.getLine)
| Negate i => Int.neg <$> interpExp i
| Minus a b => do
  let a ← interpExp a
  let b ← interpExp b
  pure $ a - b
| Plus a b => do
  let a ← interpExp a
  let b ← interpExp b
  pure $ a + b

def interpLint : Program info -> IO Int
| {exp} => interpExp exp

def peNegate : Exp Int -> Exp Int
| IntE i => IntE (-i)
| other => Negate other

def peMinus : Exp Int -> Exp Int -> Exp Int
| IntE a, IntE b => IntE (a - b)
| a, b => Minus a b

def pePlus : Exp Int -> Exp Int -> Exp Int
| IntE a, IntE b => IntE (a + b)
| a, b => Plus a b

def peExp : Exp Int -> Exp Int
| IntE a => IntE a
| Read => Read
| Negate a => peNegate a
| Minus a b => peMinus a b
| Plus a b => pePlus a b

def peLint : Program info -> Program info
| {exp} => {exp := peExp exp}
