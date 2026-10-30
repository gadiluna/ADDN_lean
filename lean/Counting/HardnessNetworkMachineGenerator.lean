import Counting.HardnessNetworkMachineBuild

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

def initialNetworkScratch : List (Fin 96) :=
  (List.finRange 96).filter (fun i=>i≠0 ∧ i≠1 ∧ i≠17 ∧ i≠25 ∧ i≠31 ∧ i≠51)

@[simp] theorem mem_initialNetworkScratch (i : Fin 96) : i∈initialNetworkScratch ↔
    i≠0 ∧ i≠1 ∧ i≠17 ∧ i≠25 ∧ i≠31 ∧ i≠51 := by simp [initialNetworkScratch]

def networkValue (input : X3CEncoding.Input) : List Bool :=
  networkWord (X3C.base input.1) (External.CoefficientMachine.inputCoefficients input)

def networkGenerator : Routine 94 :=
  sequence (External.CoefficientMachine.coefficientGenerator 32 coefficientRoles)
    (sequence (move 93 1 0 20) (sequence (pushBit 1 true) buildNetwork))

def networkGeneratorCost (input : X3CEncoding.Input) :=
  let code:=(Encoding.list Encoding.natural).encode (External.CoefficientMachine.inputCoefficients input)
  External.CoefficientMachine.generatorCost (X3CEncoding.codec.encode input).length input.1 input.2.1 code.length+
    6*code.length+buildNetworkCost input.1 (External.CoefficientMachine.inputCoefficients input)+8

theorem networkGenerator_executes (store : Store 94) (input : X3CEncoding.Input)
    (source : store 0=X3CEncoding.codec.encode input) (status : store 1=[true])
    (universeCount : store 17=List.replicate (3*input.1) true)
    (rowCount : store 25=List.replicate input.2.1 true)
    (empty : ∀ i∈initialNetworkScratch,store i=[]) :
    ∃ time ≤ networkGeneratorCost input,∃ result,
      Executes networkGenerator store time result ∧ result 1=networkValue input := by
  let values:=External.CoefficientMachine.inputCoefficients input
  let code:=(Encoding.list Encoding.natural).encode values
  have coefficientEmpty (i : Fin 64) (member : i∈External.MatchingMachine.generatorScratch) : store (coefficientRoles i)=[] := by
    have excluded : i≠0 ∧ i≠1 ∧ i≠17 ∧ i≠25 ∧ i≠31 ∧ i≠51 := by
      simpa [External.MatchingMachine.generatorScratch] using member
    apply empty
    simp only [mem_initialNetworkScratch,coefficientRoles,Function.Embedding.coeFn_mk]
    constructor
    · intro same;exact excluded.1 (Fin.ext (congrArg (fun j : Fin 96=>j.val) same))
    constructor
    · intro same;exact excluded.2.1 (Fin.ext (congrArg (fun j : Fin 96=>j.val) same))
    constructor
    · intro same;exact excluded.2.2.1 (Fin.ext (congrArg (fun j : Fin 96=>j.val) same))
    constructor
    · intro same;exact excluded.2.2.2.1 (Fin.ext (congrArg (fun j : Fin 96=>j.val) same))
    constructor
    · intro same;exact excluded.2.2.2.2.1 (Fin.ext (congrArg (fun j : Fin 96=>j.val) same))
    · intro same;exact excluded.2.2.2.2.2 (Fin.ext (congrArg (fun j : Fin 96=>j.val) same))
  obtain ⟨coefficientTime,coefficientBound,coefficientRun⟩:=External.CoefficientMachine.coefficientGenerator_state 32 coefficientRoles store input
    source status universeCount rowCount coefficientEmpty
  let computed:=External.CoefficientMachine.generatorState coefficientRoles store input
  have moving:=move_executes 93 (1:Fin 96) 0 20 (by decide) (by decide) (by decide) computed
    (by simp [computed,External.CoefficientMachine.generatorState,coefficientRoles,empty])
  have codeAt : computed 1=code := by simp [computed,External.CoefficientMachine.generatorState,coefficientRoles,code,values]
  have sourceEmpty : computed 0=[] := by simp [computed,External.CoefficientMachine.generatorState,coefficientRoles]
  rw [codeAt,sourceEmpty,List.append_nil] at moving
  let moved:=Function.update (Function.update computed 0 code) 1 []
  have pushing:=pushBit_executes (1:Fin 96) true moved
  let ready:=Function.update (Function.update computed 0 code) 1 [true]
  have pushAs : Executes (pushBit 1 true) moved 1 ready := by simpa [moved,ready] using pushing
  have readyEmpty (i : Fin 96) (member : i∈networkScratch) : ready i=[] := by
    simp only [mem_networkScratch] at member
    have original : i∈initialNetworkScratch := by
      exact (mem_initialNetworkScratch i).mpr ⟨member.1,member.2.1,member.2.2.1,member.2.2.2.1,
        member.2.2.2.2.2.1,member.2.2.2.2.2.2.1⟩
    simp [ready,computed,External.CoefficientMachine.generatorState,coefficientRoles,member,empty i original]
  have first : X3C.target input.1::values.tail=values := rfl
  have restLength : values.tail.length=input.2.1 := by
    rw [List.length_tail,External.CoefficientMachine.inputCoefficients_length]
    omega
  obtain ⟨buildTime,buildBound,result,building,output⟩:=buildNetwork_executes ready input.1 (X3C.target input.1) values.tail
    (by simp [ready,code,first]) (by simp [ready])
    (by simp [ready,computed,External.CoefficientMachine.generatorState,coefficientRoles])
    (by simp [ready,computed,External.CoefficientMachine.generatorState,coefficientRoles,rowCount,restLength]) readyEmpty
  rw [first] at buildBound output
  have combined:=coefficientRun.sequence (moving.sequence (pushAs.sequence building))
  refine ⟨_,?_,result,combined,?_⟩
  · change coefficientTime ≤ External.CoefficientMachine.generatorCost (store 0).length input.1 input.2.1 code.length at coefficientBound
    rw [source] at coefficientBound
    change _ ≤ External.CoefficientMachine.generatorCost (X3CEncoding.codec.encode input).length input.1 input.2.1 code.length+
      6*code.length+buildNetworkCost input.1 values+8
    omega
  · simpa only [networkValue,X3C.base,values] using output

end Counting.HardnessNetworkMachine
