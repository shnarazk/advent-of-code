import AoC.Color

-- @[test]
def myTest : IO Unit := do
  if 2 + 2 ≠ 4 then
    throw (IO.userError "Math is broken!")

def main (args : List String) : IO UInt32 := do
  IO.println s!"{AoC.Color.blue}Test driver works.{AoC.Color.reset}"
  return 0
