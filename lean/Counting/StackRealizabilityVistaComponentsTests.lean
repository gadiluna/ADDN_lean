import Counting.StackRealizabilityVistaEntry
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.VistaComplement.ComponentTests
open Routine RealizabilityCall

private def requireRun (label : String) (routine : Routine 128) (start expected : Store 128) : IO Nat := do
  let program := routine.program
  match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,start⟩ with
  | none => throw (IO.userError s!"Complement component exhausted fuel: {label}")
  | some (time,result) =>
    unless (List.finRange 130).all (fun r=>result.store r==expected r) do
      throw (IO.userError s!"Complement component violated full-store contract: {label}")
    return time

def tests : IO Unit := do
  let root : Executable.Node := ⟨0,none,true,0,[]⟩
  let next : Executable.Node := ⟨1,some 0,true,0,[]⟩
  let vista : Executable.Vista := ⟨#[root,next],1⟩
  let mut count := 0
  let mut maximum := 0
  for (ell,first,second,a,b) in [(1,1,2,[1,1],[1,2]),(2^90,2^100,2^100+1,[2^110,1],[2^115,1])] do
    let input := Encoding.vistaInput.encode (vista,ell)
    let witness := Encoding.twoOrderWitness.encode ((first,a),(second,b))
    let data := initialData input witness true
    let parsed := allFieldsData data vista ell first second a b
    let t ← requireRun "six canonical fields" allFields (file data) (file parsed)
    maximum := max maximum t
    count := count+1
    let t ← requireRun "second certificate replacement" secondFields (file parsed) (file (secondFieldsData parsed))
    maximum := max maximum t
    count := count+1
    let t ← requireRun "different canonical orders" ordersDifferent (file parsed)
      (file (Function.update parsed 4 [true]))
    maximum := max maximum t
    count := count+1
  let input := Encoding.vistaInput.encode (vista,1)
  let sameWitness := Encoding.twoOrderWitness.encode ((1,[1,1]),(1,[1,1]))
  let same := allFieldsData (initialData input sameWitness true) vista 1 1 1 [1,1] [1,1]
  let t ← requireRun "equal orders rejected" ordersDifferent (file same) (file (Function.update same 4 [false]))
  maximum := max maximum t
  count := count+1
  for word in [[],[true],Encoding.pairWords input sameWitness,Encoding.pairWords [] []] do
    let t ← requireRun "framed input and raw witness" prepare (inputStore 128 word)
      (file (initialData (EncodingPrograms.unframePayload word) (EncodingPrograms.unframeSuffix word)
        (Encoding.unframe word).isSome))
    maximum := max maximum t
    count := count+1
  IO.println s!"Vista complement components passed {count} full-store cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.VistaComplement.ComponentTests
