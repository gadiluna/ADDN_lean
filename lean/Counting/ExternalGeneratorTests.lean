import Counting.ExternalCookLevinCounterCost
import Counting.StackEmitClause
import Counting.StackCompilerComplete

namespace Counting.External.CookLevin.StackGenerator.Tests
open StackMachine StackMachine.Routine

def testStore (input : List Bool) : Fin 8 → List Bool := fun register => if register=0 then input else []

def counterTests : IO Unit := do
  let w : Workspace 0 := Function.Embedding.refl _
  let samples : List (List Bool) := [[],[false],[true,false],[true,false,true]]
  let parameters : List (Nat × Nat × Nat × Nat) := [(0,0,0,0),(1,0,2,1),(1,1,1,1),(2,1,1,0)]
  for input in samples do
    for (coefficient,exponent,witnessCoefficient,witnessExponent) in parameters do
      let routine := boundsRoutine 0 w coefficient exponent witnessCoefficient witnessExponent
      let cost := boundsCost input.length coefficient exponent witnessCoefficient witnessExponent
      let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
      let time := timeBound coefficient exponent input witness
      let expected : Fin 8 → List Bool := ![input,List.replicate (input.length+1) true,
        List.replicate witness true,List.replicate (2*(input.length+1)+witness) true,List.replicate time true,[],[],[]]
      match Machine.run (step routine.program) cost ⟨0,testStore input⟩ with
      | none => throw (IO.userError "Cook-Levin bound preparation stopped too early")
      | some finish =>
          unless (step routine.program finish).isNone do
            throw (IO.userError "Cook-Levin bound preparation exceeded its exact cost")
          unless (List.finRange 8).all (fun register => finish.store register == expected register) do
            throw (IO.userError "Cook-Levin bound preparation changed the wrong register or returned an incorrect count")
          unless cost ≤ Complexity.polynomial (boundsCoefficient coefficient exponent witnessCoefficient witnessExponent)
              (boundsExponent exponent witnessExponent) input.length do
            throw (IO.userError "Cook-Levin bound preparation exceeded its polynomial bound")
  IO.println "Cook-Levin counters: 16 exact-cost runs passed, including zero coefficients, zero exponents and empty inputs."

def finishWithin (program : Machine.Program) : Nat → Nat → Machine.Config program → Option (Nat × Machine.Config program)
  | 0, _, _ => none
  | fuel+1, elapsed, config => match Machine.step program config with
    | none => some (elapsed,config)
    | some next => finishWithin program fuel (elapsed+1) next

def emitterTests : IO Unit := do
  let w : PowerWorkspace 0 := Function.Embedding.refl _
  let samples : List (List Bool) := [[],[false],[true,false],[true,true,true]]
  let templates : List (List (Nat × Bool)) := [[],[(0,true)],[(0,false),(2,true)],[(3,true),(1,false),(0,false)]]
  for input in samples do
    for template in templates do
      let routine := emitClause 0 w template
      let program := Compiler.compile routine.program
      let expected := (Encoding.list literalCodec).encode (shiftedLiterals input.length template)
      match finishWithin program 500000 0 (Machine.initial program input) with
      | none => throw (IO.userError "Clause emitter exhausted physical transition fuel")
      | some (elapsed,finish) =>
          let right := finish.tape.head::finish.tape.right
          unless finish.tape.left.all (· == .blank) &&
              right.take expected.length == expected.map Machine.bitSymbol &&
              (right.drop expected.length).all (· == .blank) do
            throw (IO.userError "Clause emitter produced the wrong codec word or left a dirty tape")
          let stackBound := clauseCoefficient template*(input.length+1)^2
          unless elapsed ≤ 20*(input.length+3+stackBound+4)^2 do
            throw (IO.userError "Clause emitter exceeded the proved compiler bound")
  IO.println "Clause emitter: 16 physical-machine runs passed, including empty clauses, signs, offsets and clean output tapes."

#eval counterTests
#eval emitterTests
end Counting.External.CookLevin.StackGenerator.Tests
