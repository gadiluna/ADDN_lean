import Counting.StackRoutineClean
import Counting.StackRegisterFrames
import Counting.StackRoutineLists

namespace Counting.StackMachine.NetworkComplement
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The first 130 cells are a clean reusable work area. The outer thirty
cells retain the encoded network, its certificate, and pipeline results. -/
def file (data : Fin 30 → List Bool) : Store 158 :=
  fun r => if inside : 130 ≤ r.val then data ⟨r.val-130,by omega⟩ else []

def context : Fin 30 ↪ Fin 160 where
  toFun r := ⟨130+r.val,by omega⟩
  inj' := by intro a b h;apply Fin.ext;have := congrArg Fin.val h;dsimp at this;omega

def localRoles (registers : Nat) (small : registers ≤ 128) : Fin (registers+2) ↪ Fin 160 where
  toFun r := ⟨r.val,by omega⟩
  inj' := by intro a b h;exact Fin.ext (congrArg (fun r : Fin 160 => r.val) h)

@[simp] theorem file_context (data : Fin 30 → List Bool) (r : Fin 30) :
    file data (context r)=data r := by simp [file,context]

@[simp] theorem file_local (data : Fin 30 → List Bool) (r : Fin 160) (low : r.val<130) :
    file data r=[] := by simp [file,show ¬130≤r.val by omega]

theorem context_ne_local (r : Fin 30) (i : Fin 160) (low : i.val<130) : context r≠i := by
  intro h
  have := congrArg Fin.val h
  change 130+r.val=i.val at this
  omega

theorem file_update (data : Fin 30 → List Bool) (r : Fin 30) (word : List Bool) :
    Function.update (file data) (context r) word=file (Function.update data r word) := by
  funext i
  by_cases inside : 130 ≤ i.val
  · by_cases same : i=context r
    · subst i;simp
    · have ne : (⟨i.val-130,by omega⟩:Fin 30)≠r := by
        intro h;apply same;apply Fin.ext
        have := congrArg Fin.val h
        change i.val-130=r.val at this
        change i.val=130+r.val
        omega
      simp [file,inside,same,ne]
  · have ne : i≠context r := (context_ne_local r i (by omega)).symm
    simp [file,inside,ne]

/-- A reusable clean routine reads an external input. Only the selected
external output is replaced, and the local work area is restored completely. -/
def call {registers : Nat} (routine : Routine registers) (small : registers≤128)
    (source target : Fin 30) : Routine 158 :=
  sequence (ofProgram (ListPrograms.copyProgram 157 (context source) 0 1))
    (sequence (relocate routine (localRoles registers small))
      (sequence (ofProgram (ListPrograms.copyProgram 157 1 (context target) 0)) (clear 1)))

theorem call_executes {registers : Nat} (routine : Routine registers) (small : registers≤128)
    (data : Fin 30→List Bool) (source target : Fin 30) (empty : data target=[])
    (output : List Bool) (time : Nat)
    (run : Executes routine (inputStore registers (data source)) time (outputStore registers output)) :
    Executes (call routine small source target) (file data)
      (5*(data source).length+6*output.length+time+8)
      (file (Function.update data target output)) := by
  have copy := copy_executes 157 (context source) 0 1
    (context_ne_local source 0 (by decide)) (context_ne_local source 1 (by decide)) (by decide)
    (file data) (by simp)
  rw [file_context,show file data 0=[] by simp,List.append_nil] at copy
  let ready := Function.update (file data) 0 (data source)
  let finished := Function.update (file data) 1 output
  have invoked : Executes (relocate routine (localRoles registers small)) ready time finished := by
    apply relocate_executes_frame routine (localRoles registers small) ready finished
      (inputStore registers (data source)) (outputStore registers output) time
    · funext r
      have low : (localRoles registers small r).val<130 := by change r.val<130;omega
      have zero : localRoles registers small r=0 ↔ r=0 := by
        simp only [Fin.ext_iff]; rfl
      simp [ready,inputStore,Function.update,zero,file_local _ _ low]
    · intro r
      have low : (localRoles registers small r).val<130 := by change r.val<130;omega
      have one : localRoles registers small r=1 ↔ r=1 := by
        simp only [Fin.ext_iff]; rfl
      simp [finished,outputStore,Function.update,one,file_local _ _ low]
    · intro r outside
      have n0 := (outside 0).symm
      have n1 := (outside 1).symm
      change r≠0 at n0
      change r≠1 at n1
      simp [finished,ready,n0,n1]
    · exact run
  have exporting := copy_executes 157 (1:Fin 160) (context target) 0
    (context_ne_local target 1 (by decide)).symm (by decide) (context_ne_local target 0 (by decide))
    finished (by simp [finished])
  rw [show finished 1=output by simp [finished],
    show finished (context target)=[] by simp [finished,(context_ne_local target 1 (by decide)),empty],
    List.append_nil] at exporting
  let exported := Function.update finished (context target) output
  have erased := clear_executes (1:Fin 160) exported
  rw [show exported 1=output by simp [exported,finished,(context_ne_local target 1 (by decide)).symm]] at erased
  have final : Function.update exported 1 []=file (Function.update data target output) := by
    rw [← file_update]
    funext r
    by_cases one : r=1
    · subst r;simp [exported,finished,(context_ne_local target 1 (by decide)).symm]
    · simp [exported,finished,Function.update,one]
  rw [final] at erased
  have composed := copy.sequence (invoked.sequence (exporting.sequence erased))
  simpa only [call,show 5*(data source).length+2+1+(time+1+(5*output.length+2+1+(output.length+1)))=5*(data source).length+6*output.length+time+8 by omega] using composed

end Counting.StackMachine.NetworkComplement
