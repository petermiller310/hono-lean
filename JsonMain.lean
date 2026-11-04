import HonoLean.Adapter.Json

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  (← IO.getStdout).putStrLn ((HonoLean.Adapter.runDocument input).compress)
