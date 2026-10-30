import Counting.StackDagReferenceLookup
import Counting.EncodingNetwork
import Counting.StackRealizabilityCallFile
import Counting.StackRoutineClean
import Counting.StackEncodingRoutineInterfaces

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def outputLookupRoles : ReferenceWorkspace 116 :=
  ⟨![101,125,0,2,3,4,5,6,7,8,9,10,11,12],by decide⟩

def outputLookup : Routine 128 := referenceLookup 116 outputLookupRoles

def output : Routine 128 := sequence outputLookup
  (sequence (frameRoutine 127 0 1 2)
    (sequence (ofProgram (ListPrograms.copyProgram 127 (context 2) 1 0))
      (clearRegisters (workRegisters 128))))

theorem mappedBottom_bits_length (mapping : Array Nat) (bottom : Nat) :
    (mapping[bottom]?.getD 0).bits.length≤((Encoding.array Encoding.natural).encode mapping).length := by
  cases selected : mapping[bottom]? with
  | none => simp
  | some value =>
    have member : value∈mapping.toList := by
      have inside := (Array.getElem?_eq_some_iff.mp selected).1
      have same := (Array.getElem?_eq_some_iff.mp selected).2
      rw [←same]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem inside)
    have bounded := Encoding.array_member_length_le Encoding.natural mapping value member
    simp only [Option.getD_some,Encoding.natural_length,Encoding.bits_length] at bounded ⊢
    omega

/-- Map the saved root reference with the specified out-of-range default,
serialize the final pool and reference, then erase every working cell. -/
theorem output_executes (data : Fin 30→List Bool) (pool : Array Executable.Node)
    (mapping : Array Nat) (bottom : Nat)
    (mapAt : data 1=(Encoding.array Encoding.natural).encode mapping)
    (poolAt : data 2=(Encoding.array Encoding.node).encode pool)
    (bottomAt : data 25=Encoding.natural.encode bottom)
    (B : Nat) (bounded : ∀r,(data r).length≤B) :
    ∃time≤2200*(B+1)^3,
      Executes output (file data) time
        (outputStore 128 (Encoding.vista.encode ⟨pool,mapping[bottom]?.getD 0⟩)) := by
  obtain ⟨t0,b0,r0⟩ := referenceLookup_executes 116 outputLookupRoles (file data) mapping.toList bottom
    (by simpa [outputLookupRoles,file,Encoding.array,Encoding.transport] using mapAt)
    (by simpa [outputLookupRoles,file] using bottomAt) (by
      intro r n0 n1 n2
      fin_cases r <;> simp_all [outputLookupRoles,file])
  have nil : file data (outputLookupRoles 2)=[] := by simp [outputLookupRoles,file]
  rw [nil,List.append_nil] at r0
  let mapped := mapping[bottom]?.getD 0
  have lookupSame : (mapping.toList[bottom]?.getD 0)=mapped := by simp [mapped]
  rw [lookupSame] at r0
  change Executes outputLookup (file data) t0 (Function.update (file data) 0 mapped.bits) at r0
  let read := Function.update (file data) 0 mapped.bits
  have framing := frame_executes_updates 127 (0:Fin 130) 1 2
    (by decide) (by decide) (by decide) read (by simp [read,file])
  rw [show read 0=mapped.bits by simp [read],show read 1=[] by simp [read,file],List.append_nil] at framing
  let framed := Function.update (Function.update read 0 []) 1 (Encoding.natural.encode mapped)
  have copying := copy_executes 127 (context 2) 1 0 (by decide) (by decide) (by decide)
    framed (by simp [framed])
  have source : framed (context 2)=(Encoding.array Encoding.node).encode pool := by simp [framed,read,context,file,poolAt]
  have target : framed 1=Encoding.natural.encode mapped := by simp [framed]
  rw [source,target] at copying
  let word := Encoding.vista.encode (⟨pool,mapped⟩:Executable.Vista)
  have assembled : (Encoding.array Encoding.node).encode pool++Encoding.natural.encode mapped=word := rfl
  rw [assembled] at copying
  let written := Function.update framed 1 word
  have mappedBound : mapped.bits.length≤B := by
    exact (mappedBottom_bits_length mapping bottom).trans (by rw [←mapAt];exact bounded 1)
  have poolBound : ((Encoding.array Encoding.node).encode pool).length≤B := by
    rw [←poolAt];exact bounded 2
  have wordBound : word.length≤3*B+1 := by
    rw [←assembled,List.length_append,Encoding.natural_length,←Encoding.bits_length]
    omega
  have stateBound : ∀r,(written r).length≤3*B+1 := by
    intro r
    by_cases r0:r=0
    · subst r;simp [written,framed]
    by_cases r1:r=1
    · subst r;simpa [written] using wordBound
    simp only [written,framed,read,Function.update_of_ne r0,Function.update_of_ne r1]
    unfold file
    split
    · have h := bounded ⟨r.val-100,by omega⟩;omega
    · simp
  obtain ⟨t3,b3,r3⟩ := clearRegisters_executes (workRegisters 128) written (3*B+1) stateBound
  have final : clearedStore (workRegisters 128) written=outputStore 128 word := by
    funext r
    by_cases one:r=1
    · subst r;simp [clearedStore,workRegisters,written,outputStore]
    · simp [clearedStore,workRegisters,outputStore,one]
  rw [final] at r3
  have count : (workRegisters 128).length≤130 :=
    (List.length_filter_le _ _).trans_eq (by simp)
  have cleanBound := b3.trans (Nat.mul_le_mul_right (3*B+3) count)
  have dataBound : (file data (outputLookupRoles 0)).length+(file data (outputLookupRoles 1)).length+1≤2*(B+1) := by
    have first := bounded 1
    have last := bounded 25
    change (data 1).length+(data 25).length+1≤2*(B+1)
    omega
  have cube := Nat.pow_le_pow_left dataBound 3
  rw [Nat.mul_pow] at cube
  have lookupBound := b0.trans (Nat.mul_le_mul_left 200 cube)
  have linear : B+1≤(B+1)^3 := Nat.le_self_pow (by decide) _
  have one : 1≤(B+1)^3 := Nat.one_le_pow' _ _
  refine ⟨t0+1+(5*mapped.bits.length+4+1+(5*((Encoding.array Encoding.node).encode pool).length+2+1+t3)),?_,
    r0.sequence (framing.sequence (copying.sequence r3))⟩
  omega

end Counting.StackMachine.DagUpdate.Canonical
