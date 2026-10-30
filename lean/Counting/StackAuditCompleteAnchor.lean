import Counting.StackAuditCompleteInput

namespace Counting.StackMachine.AuditComplete
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev readAnchor : Routine 62 := sequence moveOutput (readField 4)

theorem readAnchor_executes (vista : Executable.Vista) (leaders candidate last : Nat) (anchor : Option Nat) :
    ∃ time≤ 20*((AuditPrefix.anchorCode anchor).size+1),
      Executes readAnchor
        (file [] (Encoding.optionalNatural.encode anchor) (metadata vista leaders candidate last [] [])) time
        (file [] [] (metadata vista leaders candidate last (AuditPrefix.anchorCode anchor).bits [])) := by
  let saved:=metadata vista leaders candidate last [] []
  have a:=moveOutput_executes (Encoding.optionalNatural.encode anchor) saved rfl
  have b:=readField_executes 4 (by decide) (AuditPrefix.anchorCode anchor).bits [] [] saved rfl rfl
  have word : Encoding.optionalNatural.encode anchor=Encoding.frame (AuditPrefix.anchorCode anchor).bits++[] := by
    simp [Encoding.optionalNatural,Encoding.transport,Encoding.natural,AuditPrefix.anchorCode]
  rw [word] at a
  have final : Function.update saved 4 (AuditPrefix.anchorCode anchor).bits=
      metadata vista leaders candidate last (AuditPrefix.anchorCode anchor).bits [] := by
    funext r;fin_cases r <;> simp [saved,metadata]
  rw [final] at b
  rw [word]
  refine ⟨_,?_,a.sequence b⟩
  simp only [List.length_append,List.length_nil,Nat.add_zero,Encoding.frame_length,Encoding.bits_length]
  omega

def predecessorRoles : Binary.PredWorkspace 56 := ⟨![60,62,0,2,3,4,5,6],by decide⟩

abbrev decrementAnchor : Routine 62 := sequence (Binary.predecessor 56 predecessorRoles)
  (sequence (clear 60) (move 61 62 60 63))

/-- Decode the successful optional-natural tag by a real binary predecessor;
the finite machine never expands the anchor into unary. -/
theorem decrementAnchor_executes (vista : Executable.Vista) (leaders candidate last anchor : Nat) :
    ∃ time≤ 100*((anchor+1).size+anchor.size+1),
      Executes decrementAnchor
        (file [] [] (metadata vista leaders candidate last (anchor+1).bits [])) time
        (file [] [] (metadata vista leaders candidate last anchor.bits [])) := by
  let saved:=metadata vista leaders candidate last (anchor+1).bits []
  let start:=file [] [] saved
  obtain ⟨predTime,predBound,a⟩:=Binary.predecessor_executes 56 predecessorRoles start (anchor+1)
    (by simp [start,file,saved,metadata,predecessorRoles])
    (by intro i member;fin_cases i <;> simp_all [start,file,saved,metadata,predecessorRoles])
  simp only [Nat.add_sub_cancel] at a
  let copied:=Function.update start 62 anchor.bits
  change Executes _ start predTime copied at a
  have b:=clear_executes (60:Fin 64) copied
  have source:copied 60=(anchor+1).bits := by simp [copied,start,file,saved,metadata]
  rw [source,Encoding.bits_length] at b
  let erased:=Function.update copied 60 []
  have c:=move_executes 61 (62:Fin 64) 60 63 (by decide) (by decide) (by decide) erased
    (by simp [erased,copied,start,file,saved,metadata])
  have next:erased 62=anchor.bits := by simp [erased,copied]
  have empty:erased 60=[] := by simp [erased]
  rw [next,empty,List.append_nil,Encoding.bits_length] at c
  have final : Function.update (Function.update erased 60 anchor.bits) 62 []=
      file [] [] (metadata vista leaders candidate last anchor.bits []) := by
    funext r;fin_cases r <;> simp [erased,copied,start,file,saved,metadata]
  rw [final] at c
  exact ⟨_,by omega,a.sequence (b.sequence c)⟩

end Counting.StackMachine.AuditComplete
