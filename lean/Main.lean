import «AoC»

def main (args : List String) : IO Unit := do
  let extra := args.get? 1
  match (args.get? 0) with
  | some day => run day.toNat! extra
  | none => let _ ← do (solved.mapM (run · extra))
