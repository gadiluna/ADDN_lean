import Counting.Simulation

/-! Command-line demonstration. Run from `lean/` with
`lake env lean --run Counting/Demo.lean examples/cycle3.json`.
The simulator executes a finite input prefix; it is not a correctness proof.
-/

private def usage : String :=
  "Usage: lake env lean --run Counting/Demo.lean INPUT.json\n\n" ++
  "INPUT contains {\"leaders\":[true,false,...],\"rounds\":[matrix,...]}.\n" ++
  "Each matrix[sender][receiver] is a natural arc multiplicity.\n" ++
  "Output is one JSON document with initial and per-round snapshots.\n"

def main (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] then
    IO.print usage
    return 0
  let [path] := args
    | do
      (← IO.getStderr).putStr usage
      return 2
  try
    let contents ← IO.FS.readFile path
    match Counting.Simulation.Input.parse contents >>= Counting.Simulation.simulate with
    | .error message =>
      (← IO.getStderr).putStrLn s!"Invalid simulation: {message}"
      return 1
    | .ok result =>
      IO.println result.compress
      return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"Simulation failed: {error}"
    return 1
