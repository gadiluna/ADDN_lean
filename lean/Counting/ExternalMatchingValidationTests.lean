import Counting.ExternalMatchingValidation
import Counting.StackMachineTestLazy

namespace Counting.External.MatchingValidation.Tests
open StackMachine SATVerification

private def workspace : SATWorkspace 2 :=
  ⟨fun i => ⟨i.val,by omega⟩,by intro a b same;exact Fin.ext (congrArg (fun x : Fin 34 => x.val) same)⟩

private def requireCase (program : Program) (name : String) (input : List Bool) (accepted : Bool) : IO Nat := do
  let store : Fin 34 → List Bool := fun r =>
    if r=0 then input else if r=1 then [true]
    else if r=32 then [false,true,false] else if r=33 then [true,false,true,true] else []
  let expected := result 2 workspace store
  unless check input == accepted do
    throw (IO.userError s!"matching validation predicate differs: {name}")
  let executionStore : Register program → List Bool := fun r =>
    if inside : r.val < 34 then store ⟨r.val,inside⟩ else []
  match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,executionStore⟩ with
  | none => throw (IO.userError s!"matching validation fuel exhausted: {name}")
  | some (steps,final) =>
    unless program.extraRegisters==32 do throw (IO.userError "matching validation layout changed")
    unless (List.finRange 34).all (fun r =>
        if inside : r.val<program.extraRegisters+2 then final.store ⟨r.val,inside⟩ == expected r else false) do
      throw (IO.userError s!"matching validation full store differs: {name}")
    return steps

def tests : IO Unit := do
  let program := (routine 2 workspace).program
  let encode := CNFEncoding.rawCodec.encode
  let cases : List (String × List Bool × Bool) :=
    [("empty formula",encode ([],[]),true),
     ("three literals",encode ([true],[[(0,true),(0,false),(0,true)]]),true),
     ("two variables",encode ([true,true],[[(0,false),(1,true),(1,false)]]),true),
     ("false universe marker",encode ([false],[[(0,true),(0,false),(0,true)]]),false),
     ("out of range",encode ([true],[[(1,true),(0,false),(0,true)]]),false),
     ("empty universe with clause",encode ([],[[(0,true),(0,false),(0,true)]]),false),
     ("empty clause",encode ([true],[[]]),false),
     ("two literals",encode ([true],[[(0,true),(0,false)]]),false),
     ("four literals",encode ([true],[[(0,true),(0,false),(0,true),(0,false)]]),false),
     ("large binary index",encode ([true],[[(2^129,true),(0,false),(0,true)]]),false),
     ("missing header",[],false),
     ("trailing bit",encode ([],[])++[true],false)]
  let mut maximum := 0
  for (name,input,accepted) in cases do
    maximum := max maximum (←requireCase program name input accepted)
  IO.println s!"Matching input validation: {cases.length} full-store cases passed, including malformed encodings, exact clause widths, index bounds, binary large indices and outside-register preservation; maximum {maximum} stack transitions."

#eval tests
end Counting.External.MatchingValidation.Tests
