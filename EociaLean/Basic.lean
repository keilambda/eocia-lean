abbrev Var : Type := String
abbrev Label : Type := String

def gensym : StateM Nat Var := do
  let n ← get
  modify (· + 1)
  pure s!"a{n}"
