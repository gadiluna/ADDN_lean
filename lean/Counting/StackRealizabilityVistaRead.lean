import Counting.StackRealizabilityCallFile
import Counting.StackRealizabilityVistaParser
import Counting.StackEncodingParserRelabel
import Counting.StackRoutineLists

namespace Counting.StackMachine.VistaComplement
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def readerRoles : Fin 17 ↪ Fin 130 :=
  ⟨![105,104,71,0,1,2,3,4,5,6,7,8,9,10,11,12,13],by decide⟩

def readField {α : Type} {codec : Encoding.Codec α}
    (parser : VerifiedParser 15 0 1 2 α codec) (target : Fin 30) : Routine 128 :=
  sequence (mapRegisters readerRoles parser.routine)
    (ofProgram (ListPrograms.reverseProgram 128 71 (context target)))

/-- An actual canonical-component reader populates an external field of
our reusable verifier frame. The unread suffix remains in external cell5;
all parser workspace is restored and the acceptance tail is preserved. -/
theorem readField_executes {α : Type} {codec : Encoding.Codec α}
    (parser : VerifiedParser 15 0 1 2 α codec) (data : Fin 30→List Bool)
    (target : Fin 30) (targetSource : target≠5) (_targetStatus : target≠4)
    (value : α) (suffix : List Bool) (accepted : Bool) (tail : List Bool)
    (source : data 5=codec.encode value++suffix) (status : data 4=accepted::tail)
    (empty : data target=[]) :
    ∃ time ≤ Complexity.polynomial parser.coefficient parser.exponent (data 5).length+
        2*(codec.encode value).length+2,
      Executes (readField parser target) (file data) time
        (file (Function.update (Function.update data 5 suffix) target (codec.encode value))) := by
  let relocated := parser.relabel readerRoles
  have work (r : Fin 130) (member : r∈relocated.work) : file data r=[] := by
    change r∈parser.work.map readerRoles at member
    obtain ⟨i,inWork,rfl⟩ := Finset.mem_map.mp member
    obtain ⟨a,b,c⟩ := parser.separate i inWork
    fin_cases i <;> simp_all [readerRoles,file]
  obtain ⟨time,bound,parsing⟩ := relocated.executes (file data) accepted tail
    (by simpa [readerRoles,file] using status) work
  change time ≤ Complexity.polynomial parser.coefficient parser.exponent (file data 105).length at bound
  have inputAt : file data 105=codec.encode value++suffix := by simpa [file] using source
  have originalAt : file data 105=data 5 := by simp [file]
  rw [originalAt] at bound
  change Executes (mapRegisters readerRoles parser.routine) (file data) time
    (parseStore (105:Fin 130) 104 71 (file data) accepted tail (parser.effect (file data 105))) at parsing
  rw [inputAt,parser.roundtrip] at parsing
  let parsed := Function.update (Function.update (file data) 105 suffix) 71 (codec.encode value).reverse
  have parsedEq : parseStore (105:Fin 130) 104 71 (file data) accepted tail
      ⟨suffix,codec.encode value,true⟩=parsed := by
    funext r
    by_cases a:r=105 <;> by_cases b:r=104 <;> by_cases c:r=71 <;>
      simp_all [parseStore,parsed,file]
  rw [parsedEq] at parsing
  have temporary : context target≠71 := by
    intro equal;have:=congrArg (fun r:Fin 130=>r.val) equal;change 100+target.val=71 at this;omega
  have outputSource : context target≠105 := by
    intro equal;apply targetSource;apply Fin.ext
    have:=congrArg (fun r:Fin 130=>r.val) equal;change 100+target.val=105 at this;omega
  have reversing := reverse_executes 128 (71:Fin 130) (context target) temporary.symm parsed
  have fromAt : parsed 71=(codec.encode value).reverse := by simp [parsed]
  have toAt : parsed (context target)=[] := by simp [parsed,temporary,outputSource,empty]
  rw [fromAt,toAt,List.reverse_reverse,List.append_nil,List.length_reverse] at reversing
  have final : Function.update (Function.update parsed 71 []) (context target) (codec.encode value)=
      file (Function.update (Function.update data 5 suffix) target (codec.encode value)) := by
    have clearTemporary : Function.update parsed 71 []=Function.update (file data) 105 suffix := by
      funext r
      by_cases same:r=71 <;> simp_all [parsed,file]
    rw [clearTemporary]
    change Function.update (Function.update (file data) (context 5) suffix) (context target) (codec.encode value)=_
    rw [file_update,file_update]
  rw [final] at reversing
  exact ⟨_,by omega,parsing.sequence reversing⟩

end Counting.StackMachine.VistaComplement
