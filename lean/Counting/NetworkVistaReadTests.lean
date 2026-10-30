import Counting.NetworkVistaReadBounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkVista.Reader.Tests
open Routine EncodingPrograms

private def test {α:Type} {codec:Encoding.Codec α}
    (parser:VerifiedParser 15 0 1 2 α codec) (input:List Bool) (index:Nat) : IO Nat := do
  let store:Store 19:=fun r=>if r=17 then input else if r=18 then List.replicate index true
    else if r=1 then [true,false,true] else []
  let effect:=readEffect parser.effect index input
  let expected:=preservingStore store true [false,true] effect
  let program:=(preservingRead parser).program
  match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "Preserving structured reader exhausted fuel")
  | some (time,result)=>
    unless (List.finRange 21).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Preserving structured reader violated its full-store contract")
    return time

def tests : IO Unit := do
  let vistas:List Executable.Vista:=[Executable.initialVista false,Executable.initialVista true,
    ⟨#[⟨0,none,true,2^129,[]⟩],0⟩]
  let vistaInput:=Encoding.sequence Encoding.vista vistas++[false,true]
  let rows:List (Array Nat):=[#[],#[0],#[2^129,0,3]]
  let rowInput:=Encoding.sequence (Encoding.array Encoding.natural) rows++[true,false]
  let mut maximum:=0
  let mut count:=0
  for index in [0,1,2,3] do
    let time ← test DagParser.vista vistaInput index
    maximum:=max maximum time
    count:=count+1
  for index in [0,1,2,3] do
    let time ← test NetworkRecognition.row rowInput index
    maximum:=max maximum time
    count:=count+1
  for input in [[],[true],[false,true,true]] do
    let time ← test DagParser.vista input 0
    maximum:=max maximum time
    count:=count+1
  IO.println s!"Structured preserving reader passed {count} full-store cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.NetworkVista.Reader.Tests
