import Counting.StackDagSyntaxGate

/-! Complete DAG semantic validation on every binary word. Syntax recognition
is a real charged prefix-parser machine; only its positive branch invokes
the three semantic scans. All malformed encodings therefore halt and reject. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def validWord (input : List Bool) : Bool:=
  ((Encoding.vista.decodeExact input).map Executable.Vista.valid).getD false

def validationRoutine : Routine 35:=sequence (ofProgram (ListPrograms.copyProgram 34 0 35 36))
  (sequence syntaxGate (sequence (branchRoutine 1 semanticOnValid (pushBit 1 false)) (clear 35)))

def validationProgram : Program:=validationRoutine.program

theorem validatorStore_update_flags (input before after : List Bool) :
    Function.update (validatorStore input before) 1 after=validatorStore input after:=by
  funext r
  by_cases same : r=1 <;> simp [validatorStore,same]

theorem validationBranch_executes (input : List Bool) :
    ∃ time ≤ 224000020*(input.length+1)^6,
      Executes (branchRoutine 1 semanticOnValid (pushBit 1 false))
        (validatorStore input [(Encoding.vista.decodeExact input).isSome]) time (validatorStore input [validWord input]):=by
  cases decoded:Encoding.vista.decodeExact input with
  | none=>
    have pushing:=pushBit_executes (1:Fin 37) false (validatorStore input [])
    have empty : validatorStore input [] 1=[]:=by simp [validatorStore]
    rw [empty,validatorStore_update_flags] at pushing
    have branch:=branch_executes_false (1:Fin 37) semanticOnValid (pushBit 1 false)
      (validatorStore input [false]) (validatorStore input [false]) [] 1 (by simp [validatorStore])
      (by simpa only [validatorStore_update_flags] using pushing)
    refine ⟨2,by have:=Nat.one_le_pow 6 (input.length+1) (by omega);omega,?_⟩
    simpa only [decoded,Option.isSome_none,validWord,Option.map_none,Option.getD_none] using branch
  | some vista=>
    have encoded : Encoding.vista.encode vista=input:=(Encoding.Codec.decodeExact_iff _ input vista).mp decoded
    obtain ⟨time,bound,ran⟩:=semanticOnValid_executes vista
    rw [encoded] at bound ran
    have branch:=branch_executes_true (1:Fin 37) semanticOnValid (pushBit 1 false)
      (validatorStore input [true]) (validatorStore input [vista.valid]) [] time (by simp [validatorStore])
      (by simpa only [validatorStore_update_flags] using ran)
    refine ⟨1+time,by have:=Nat.one_le_pow 6 (input.length+1) (by omega);omega,?_⟩
    simpa only [decoded,Option.isSome_some,validWord,Option.map_some,Option.getD_some] using branch

theorem validation_executes (input : List Bool) :
    ∃ time ≤ 225000000*(input.length+1)^6,
      Executes validationRoutine (inputStore 35 input) time (outputStore 35 [validWord input]):=by
  have copying:=copy_executes 34 0 35 36 (by decide) (by decide) (by decide) (inputStore 35 input)
    (by simp [inputStore])
  have initialSource : inputStore 35 input 0=input:=by simp [inputStore]
  have initialTarget : inputStore 35 input 35=[]:=by simp [inputStore]
  rw [initialSource,initialTarget,List.append_nil] at copying
  have start : Function.update (inputStore 35 input) 35 input=validatorStart input:=by
    funext r
    by_cases r0 : r=0 <;> by_cases r35 : r=35 <;> simp [validatorStart,validatorStore,inputStore,r0,r35]
  rw [start] at copying
  obtain ⟨syntaxTime,syntaxBound,syntaxRun⟩:=syntaxGate_executes input
  obtain ⟨branchTime,branchBound,branchRun⟩:=validationBranch_executes input
  have clearing:=clear_executes (35:Fin 37) (validatorStore input [validWord input])
  have backup : validatorStore input [validWord input] 35=input:=by simp [validatorStore]
  rw [backup] at clearing
  have final : Function.update (validatorStore input [validWord input]) 35 []=outputStore 35 [validWord input]:=by
    funext r
    by_cases r1 : r=1 <;> by_cases r35 : r=35 <;> simp [validatorStore,outputStore,r1,r35]
  rw [final] at clearing
  have fourth : (input.length+1)^4≤(input.length+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have linear:=Nat.le_self_pow (by decide : 6≠0) (input.length+1)
  exact ⟨5*input.length+2+1+(syntaxTime+1+(branchTime+1+(input.length+1))),by omega,
    copying.sequence (syntaxRun.sequence (branchRun.sequence clearing))⟩

theorem validation_computes : ComputesIn validationProgram (fun input=>[validWord input])
    (Complexity.polynomial 225000000 6):=by
  intro input
  obtain ⟨time,bound,finish,ran,halted,result⟩:=validation_executes input
  refine ⟨time,finish,bound,⟨ran,halted⟩,?_⟩
  rw [result]
  simp [outputStore]

/-- A finite-control, finite-alphabet Turing machine with clean output and a
polynomial number of actual transitions on every input bit string. -/
theorem validation_computesCleanIn : Complexity.ComputesCleanIn (Compiler.compile validationProgram)
    (fun input=>[validWord input]) (Complexity.polynomial (20*(225000040)^2) 14):=by
  exact Compiler.computesCleanIn_polynomial 225000000 6 validation_computes

@[simp] theorem validWord_encoded (vista : Executable.Vista) : validWord (Encoding.vista.encode vista)=vista.valid:=by
  have decoded : Encoding.vista.decodeExact (Encoding.vista.encode vista)=some vista:=
    (Encoding.Codec.decodeExact_iff _ _ vista).mpr rfl
  simp only [validWord,decoded,Option.map_some,Option.getD_some]

theorem validWord_true_iff (input : List Bool) : validWord input=true ↔
    ∃ vista,Encoding.vista.encode vista=input ∧ vista.valid=true:=by
  cases decoded:Encoding.vista.decodeExact input with
  | none=>
    simp only [validWord,decoded,Option.map_none,Option.getD_none,Bool.false_eq_true,false_iff,not_exists,not_and]
    intro vista encoded
    have someDecode:=(Encoding.Codec.decodeExact_iff _ _ vista).mpr encoded
    rw [decoded] at someDecode
    contradiction
  | some vista=>
    have encoded:=(Encoding.Codec.decodeExact_iff _ _ vista).mp decoded
    simp only [validWord,decoded,Option.map_some,Option.getD_some]
    constructor
    · intro valid;exact ⟨vista,encoded,valid⟩
    · rintro ⟨other,otherEncoded,valid⟩
      have same : other=vista:=Encoding.vista.injective (otherEncoded.trans encoded.symm)
      simpa only [same] using valid

end Counting.StackMachine.DagValidation
