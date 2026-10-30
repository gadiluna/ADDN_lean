import Counting.HardnessNetworkMachineContinuation
import Counting.StackEncodingBranch

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 32768

def validationRoles : External.SATVerification.SATWorkspace 64 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 96=>i.val) h)⟩

def networkEntry : Routine 94 :=
  sequence (ofProgram (ListPrograms.copyProgram 93 0 51 63))
    (sequence (pushBit 1 true)
      (sequence (External.CoverInputValidation.routine 64 validationRoles)
        (branchRoutine 1 acceptedNetworkContinuation rejectedNetworkContinuation)))

def networkEntryCost (input : List Bool) :=
  External.CoverInputValidation.coefficient*(input.length+1)^5+10*input.length+100+
    if External.CoverInputValidation.validInput input then
      match X3CEncoding.codec.decodeExact input with
      | none=>0
      | some value=>networkGeneratorCost value
    else 0

theorem networkTransform_rejected (input : List Bool) (invalid : External.CoverInputValidation.validInput input=false) :
    networkTransform input=[] := by
  cases decoded : X3CEncoding.codec.decodeExact input with
  | none=>simp [networkTransform,decoded]
  | some value=>
    have encoded := (X3CEncoding.codec.decodeExact_iff input value).mp decoded
    have valid := (External.CoverInputValidation.validInput_iff input).mpr ⟨value,encoded⟩
    rw [invalid] at valid
    contradiction

/-- Total network transducer entry. All binary inputs terminate; invalid
X3C encodings return the empty word. Normalization is composed separately
and guarantees a valid input whenever the hardness reduction invokes it. -/
theorem networkEntry_executes (store : Store 94) (empty : ∀ i : Fin 96,i≠0→store i=[]) :
    ∃ time ≤ networkEntryCost (store 0),∃ result,
      Executes networkEntry store time result ∧ result 1=networkTransform (store 0) := by
  let input:=store 0
  have inputLength : (store 0).length=input.length := rfl
  have saving:=copy_executes 93 (0:Fin 96) 51 63 (by decide) (by decide) (by decide) store (empty 63 (by decide))
  rw [empty 51 (by decide),List.append_nil] at saving
  let saved:=Function.update store 51 input
  have pushing:=pushBit_executes (1:Fin 96) true saved
  have nilFlag : saved 1=[] := by simp [saved,empty]
  rw [nilFlag] at pushing
  let ready:=Function.update saved 1 [true]
  have readySource : ready 0=input := by simp [ready,saved,input]
  have readyEmpty (i : Fin 32) (a : i≠0) (b : i≠1) : ready (validationRoles i)=[] := by
    fin_cases i <;> simp_all [validationRoles,ready,saved]
  obtain ⟨validateTime,validateBound,validation⟩:=External.CoverInputValidation.routine_executes 64 validationRoles ready
    (by simp [validationRoles,ready]) readyEmpty
  have validateLimit : validateTime ≤ External.CoverInputValidation.coefficient*(input.length+1)^5 := by
    simpa [validationRoles,readySource] using validateBound
  by_cases valid : External.CoverInputValidation.validInput input=true
  · obtain ⟨value,encoded⟩:=(External.CoverInputValidation.validInput_iff input).mp valid
    have decoded := (X3CEncoding.codec.decodeExact_iff input value).mpr encoded
    have canonicalSource : ready (validationRoles 0)=X3CEncoding.codec.encode value := by
      change ready 0=_;rw [readySource,encoded]
    rw [External.CoverInputValidation.result_canonical 64 validationRoles ready value canonicalSource] at validation
    let checked:=Function.update (Function.update (Function.update (Function.update ready
      17 (List.replicate (3*value.1) true)) 25 (List.replicate value.2.1 true)) 0 []) 1 [true]
    have validationAs : Executes (External.CoverInputValidation.routine 64 validationRoles) ready validateTime checked := by
      simpa [validationRoles,checked] using validation
    let consumed:=Function.update checked 1 []
    have continuationEmpty (i : Fin 96) (member : i∈initialNetworkScratch) : consumed i=[] := by
      obtain ⟨a,b,c,d,e,f⟩:=(mem_initialNetworkScratch i).mp member
      simp [consumed,checked,ready,saved,a,b,c,d,f,empty i a]
    obtain ⟨acceptTime,acceptBound,result,accepting,output⟩:=acceptedNetworkContinuation_executes consumed value
      (by simp [consumed,checked,ready,saved,encoded]) (by simp [consumed,checked]) (by simp [consumed])
      (by simp [consumed,checked]) (by simp [consumed,checked]) continuationEmpty
    have branch:=branch_executes_true (1:Fin 96) acceptedNetworkContinuation rejectedNetworkContinuation
      checked result [] acceptTime (by simp [checked]) accepting
    have combined:=saving.sequence (pushing.sequence (validationAs.sequence branch))
    refine ⟨_,?_,result,combined,?_⟩
    · rw [encoded] at acceptBound
      change _ ≤ networkEntryCost input
      simp only [networkEntryCost,valid,if_true,decoded]
      omega
    · rw [output]
      change _=networkTransform input
      rw [←encoded,networkTransform_encoded]
  · have invalid : External.CoverInputValidation.validInput input=false := Bool.eq_false_iff.mpr valid
    let checked:=External.CoverInputValidation.result 64 validationRoles ready
    have flagFalse : checked 1=[false] := by
      have flag:=External.CoverInputValidation.result_flag 64 validationRoles ready
      change checked 1=[External.CoverInputValidation.validInput (ready 0)] at flag
      simpa only [readySource,invalid] using flag
    let consumed:=Function.update checked 1 []
    have rejecting:=prepend_executes (1:Fin 96) [] consumed
    have outputEmpty : consumed 1=[] := by simp [consumed]
    rw [outputEmpty,List.append_nil] at rejecting
    have branch:=branch_executes_false (1:Fin 96) acceptedNetworkContinuation rejectedNetworkContinuation
      checked _ [] _ flagFalse rejecting
    have combined:=saving.sequence (pushing.sequence (validation.sequence branch))
    refine ⟨_,?_,_,combined,?_⟩
    · change _ ≤ networkEntryCost input
      simp only [networkEntryCost,invalid,Bool.false_eq_true,if_false,Nat.add_zero]
      simp only [List.length_nil,Nat.mul_zero]
      omega
    · simp only [Function.update_self]
      exact (networkTransform_rejected input invalid).symm

end Counting.HardnessNetworkMachine
