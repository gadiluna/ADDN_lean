import Counting.StackRealizabilityCallInputs
import Counting.StackRealizabilityVistaParser
import Counting.StackRegisterFrames
import Counting.StackEncodingPair

namespace Counting.StackMachine.VistaComplement
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def syntaxRoles : Fin 17 ↪ Fin 130 := ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun r:Fin 130=>r.val) h)⟩
def runSyntax (parser : Routine 15) : Routine 128 := mapRegisters syntaxRoles (isolate parser)

theorem runSyntax_executes (parser : Routine 15) (predicate : List Bool→Bool) (c k : Nat)
    (computes : ComputesIn parser.program (fun input=>[predicate input]) (Complexity.polynomial c k))
    (data : Fin 30→List Bool) (input : List Bool) :
    ∃time≤18*(Complexity.polynomial c k input.length+input.length+3),
      Executes (runSyntax parser) (Function.update (file data) 0 input) time
        (Function.update (file data) 1 [predicate input]) := by
  obtain ⟨time,bound,run⟩ := isolate_executes parser _ _ computes input
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame (isolate parser) syntaxRoles
    (Function.update (file data) 0 input) (Function.update (file data) 1 [predicate input])
    (inputStore 15 input) (outputStore 15 [predicate input]) time _ _ _ run
  · funext i
    by_cases same:i=0
    · subst i;simp [syntaxRoles,inputStore]
    · have different : syntaxRoles i≠0 := by
        intro equal;apply same;exact Fin.ext (congrArg (fun r:Fin 130=>r.val) equal)
      have empty : file data (syntaxRoles i)=[] := by simp [file,syntaxRoles];omega
      simp [different,inputStore,same,empty]
  · intro i
    by_cases same:i=1
    · subst i;simp [syntaxRoles,outputStore]
    · have different : syntaxRoles i≠1 := by
        intro equal;apply same;exact Fin.ext (congrArg (fun r:Fin 130=>r.val) equal)
      have empty : file data (syntaxRoles i)=[] := by simp [file,syntaxRoles];omega
      simp [different,outputStore,same,empty]
  · intro i outside
    have a:i≠0 := by intro same;subst i;exact outside 0 rfl
    have b:i≠1 := by intro same;subst i;exact outside 1 rfl
    simp [a,b]

def syntaxCall (parser : Routine 15) (field : Fin 30) : Routine 128 :=
  sequence (copyField field) (sequence (runSyntax parser)
    (sequence (ofProgram (ListPrograms.reverseProgram 128 1 104)) (ofProgram (combineFlagsProgram 128 104))))

theorem syntaxCall_executes (parser : Routine 15) (predicate : List Bool→Bool) (c k : Nat)
    (computes : ComputesIn parser.program (fun input=>[predicate input]) (Complexity.polynomial c k))
    (data : Fin 30→List Bool) (field : Fin 30) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail) :
    ∃time≤18*Complexity.polynomial c k (data field).length+23*(data field).length+65,
      Executes (syntaxCall parser field) (file data) time
        (file (Function.update data 4 ((accepted && predicate (data field))::tail))) := by
  have copying := copyField_executes data field []
  simp only [List.append_nil] at copying
  have empty : Function.update (file data) 0 []=file data := by
    have atZero : file data 0=[] := by simp [file]
    rw [←atZero,Function.update_eq_self]
  rw [empty] at copying
  obtain ⟨time,bound,verification⟩ := runSyntax_executes parser predicate c k computes data (data field)
  let answer := predicate (data field)
  let verified := Function.update (file data) 1 [answer]
  have moving := reverse_executes 128 (1:Fin 130) 104 (by decide) verified
  have sourceAt : verified 1=[answer] := by simp [verified]
  have targetAt : verified 104=accepted::tail := by simpa [verified,file] using status
  rw [sourceAt,targetAt,List.length_singleton,List.reverse_singleton,List.singleton_append] at moving
  let appended := Function.update (file data) 104 (answer::accepted::tail)
  have moved : Function.update (Function.update verified 1 []) 104 (answer::accepted::tail)=appended := by
    funext i
    by_cases a:i=1 <;> by_cases b:i=104 <;> simp_all [verified,appended,file]
  rw [moved] at moving
  have joining := combineFlags_executes 128 (104:Fin 130) appended accepted answer tail (by simp [appended])
  have final : Function.update appended 104 ((accepted && answer)::tail)=
      file (Function.update data 4 ((accepted && answer)::tail)) := by
    simp only [appended,Function.update_idem]
    exact file_update data 4 _
  rw [final] at joining
  refine ⟨_,?_,copying.sequence (verification.sequence (moving.sequence joining))⟩
  change 5*(data field).length+2+1+(time+1+(3+1+3))≤_
  simp only [Nat.mul_add] at bound
  omega

end Counting.StackMachine.VistaComplement
