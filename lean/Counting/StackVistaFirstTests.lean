import Counting.MachineVistaFirst
import Counting.DagRawIdentity
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.VistaFirst.Tests

def tests : IO Unit := do
  let first := Executable.initialVista true
  let second := Executable.initialVista false
  let large : Executable.Vista := ⟨#[⟨0,none,true,0,[]⟩,
    ⟨1,some 0,true,2^130,[(0,2^129)]⟩],1⟩
  let cases := [(first,[]),(second,[first]),(first,[second,first]),
    (large,[first,second]),(first,[large,large,second])]
  let program := complete.program
  let mut maximum := 0
  for (vista,rest) in cases do
    let initial := Routine.inputStore 18 (inputWord vista rest)
    let expected := Routine.outputStore 18 (outputWord vista)
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,initial⟩ with
    | none => throw (IO.userError "First-vista extraction exceeded fuel")
    | some (steps,last) =>
      unless (List.finRange 20).all (fun r => last.store r == expected r) do
        throw (IO.userError "First-vista extraction full-store mismatch")
      maximum := max maximum steps
  let inputs : List Simulation.Input :=
    [⟨#[true],#[#[#[0]],#[#[0]]]⟩,
     ⟨#[true],#[#[#[2^65]],#[#[2^130]]]⟩,
     ⟨#[true,false],#[#[#[0,1],#[1,0]],#[#[1,1],#[1,1]]]⟩]
  for input in inputs do
    let views := Encoding.rawInputVistas input
    unless views.all (fun vista => vista.valid) do
      throw (IO.userError "Raw physical reconstruction produced an invalid vista")
    for vista in views do
      let expected := (vista.nodes,(List.range vista.nodes.size).toArray)
      unless Executable.importVista #[] vista == expected do
        throw (IO.userError "Reimporting a valid vista changed its signature pool")
  IO.println s!"Raw reconstruction/extraction: {cases.length} full-store cases and {inputs.length} network prefixes passed; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.VistaFirst.Tests
