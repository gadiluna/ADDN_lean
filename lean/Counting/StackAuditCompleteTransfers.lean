import Counting.StackAuditCompleteBank
import Counting.StackEncodingFrameStore

namespace Counting.StackMachine.AuditComplete
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

def slot (i : Fin 8) : Fin 64 := ⟨56+i.val,by omega⟩

@[simp] theorem file_slot (input output : List Bool) (saved : Fin 8 → List Bool) (i : Fin 8) :
    file input output saved (slot i)=saved i := by
  have nonzero:slot i≠0 := by intro eq;have h:=congrArg Fin.val eq;change 56+i.val=0 at h;omega
  have nonone:slot i≠1 := by intro eq;have h:=congrArg Fin.val eq;change 56+i.val=1 at h;omega
  simp only [file,if_neg nonzero,if_neg nonone]
  simp [slot]

theorem file_update_slot (input output word : List Bool) (saved : Fin 8 → List Bool) (i : Fin 8) :
    Function.update (file input output saved) (slot i) word=
      file input output (Function.update saved i word) := by
  funext r
  by_cases inside:r.val<56
  · have unequal:r≠slot i := by intro eq;have:=congrArg Fin.val eq;simp only [slot] at this;omega
    simp [file,inside,unequal]
  · have nonzero:r≠0 := by intro eq;subst r;simp at inside
    have nonone:r≠1 := by intro eq;subst r;simp at inside
    have equivalent : r=slot i ↔ (⟨r.val-56,by omega⟩:Fin 8)=i := by
      constructor <;> intro eq <;> apply Fin.ext
      · have h:=congrArg Fin.val eq;change r.val=56+i.val at h;change r.val-56=i.val;omega
      · have h:=congrArg Fin.val eq;change r.val-56=i.val at h;change r.val=56+i.val;omega
    simp [file,inside,nonzero,nonone,Function.update_apply,equivalent]

abbrev readField (i : Fin 8) : Routine 62 := ofProgram (unframeProgram 61 0 (slot i) 63)

theorem readField_executes (i : Fin 8) (notScratch:i≠7) (word rest output : List Bool)
    (saved : Fin 8 → List Bool) (vacant:saved i=[]) (scratch:saved 7=[]) :
    Executes (readField i) (file (Encoding.frame word++rest) output saved) (5*word.length+2)
      (file rest output (Function.update saved i word)) := by
  have sourceDifferent : (0:Fin 64)≠slot i := by intro eq;have h:=congrArg Fin.val eq;change 0=56+i.val at h;omega
  have targetDifferent : slot i≠63 := by
    intro eq;apply notScratch;apply Fin.ext;have:=congrArg Fin.val eq;dsimp [slot] at this;omega
  have run:=unframe_canonical_executes 61 (0:Fin 64) (slot i) 63 sourceDifferent
    (by decide) targetDifferent (file (Encoding.frame word++rest) output saved) word rest
    (by simp [file]) (by simpa [file,slot] using scratch)
  rw [file_slot,vacant,List.append_nil] at run
  have consumed : Function.update (file (Encoding.frame word++rest) output saved) 0 rest=
      file rest output saved := by
    funext r;by_cases zero:r=0 <;> simp [file,zero]
  rw [consumed,file_update_slot] at run
  exact run

abbrev prependSaved (i : Fin 8) : Routine 62 :=
  sequence (ofProgram (ListPrograms.copyProgram 61 (slot i) 62 63)) (frameRoutine 61 62 0 63)

theorem prependSaved_executes (i : Fin 8) (fits:i.val<6) (input output : List Bool)
    (saved : Fin 8 → List Bool) (temporary:saved 6=[]) (scratch:saved 7=[]) :
    Executes (prependSaved i) (file input output saved) (10*(saved i).length+7)
      (file (Encoding.frame (saved i)++input) output saved) := by
  have different62:slot i≠62 := by intro eq;have:=congrArg Fin.val eq;dsimp [slot] at this;omega
  have different63:slot i≠63 := by intro eq;have:=congrArg Fin.val eq;dsimp [slot] at this;omega
  have a:=copy_executes 61 (slot i) 62 63 different62 different63 (by decide)
    (file input output saved) (by simpa [file] using scratch)
  rw [file_slot] at a
  have t:(file input output saved) 62=[] := by simpa [file] using temporary
  rw [t,List.append_nil] at a
  let copied:=Function.update (file input output saved) 62 (saved i)
  have b:=frame_executes_updates 61 (62:Fin 64) 0 63 (by decide) (by decide) (by decide)
    copied (by simp [copied,file,scratch])
  have target : Function.update (Function.update copied 62 []) 0
      (Encoding.frame (copied 62)++copied 0)=file (Encoding.frame (saved i)++input) output saved := by
    funext r
    by_cases zero:r=0 <;> by_cases temp:r=62 <;> simp [copied,file,zero,temp,temporary]
  rw [target] at b
  change Executes _ copied (5*(saved i).length+4) _ at b
  have combined:=a.sequence b
  convert combined using 1 <;> first | rfl | omega

abbrev copySaved (i : Fin 8) : Routine 62 := ofProgram (ListPrograms.copyProgram 61 (slot i) 0 63)

theorem copySaved_executes (i : Fin 8) (notScratch:i≠7) (input output : List Bool)
    (saved : Fin 8 → List Bool) (scratch:saved 7=[]) :
    Executes (copySaved i) (file input output saved) (5*(saved i).length+2)
      (file (saved i++input) output saved) := by
  have different0:slot i≠0 := by intro eq;have h:=congrArg Fin.val eq;change 56+i.val=0 at h;omega
  have different63:slot i≠63 := by
    intro eq;apply notScratch;apply Fin.ext;have:=congrArg Fin.val eq;dsimp [slot] at this;omega
  have run:=copy_executes 61 (slot i) 0 63 different0 different63 (by decide)
    (file input output saved) (by simpa [file] using scratch)
  rw [file_slot] at run
  have inputAt:file input output saved 0=input := by simp [file]
  rw [inputAt] at run
  have target : Function.update (file input output saved) 0 (saved i++input)=
      file (saved i++input) output saved := by
    funext r;by_cases zero:r=0 <;> simp [file,zero]
  rwa [target] at run

abbrev moveOutput : Routine 62 := move 61 1 0 63

theorem moveOutput_executes (word : List Bool) (saved : Fin 8 → List Bool) (scratch:saved 7=[]) :
    Executes moveOutput (file [] word saved) (6*word.length+4) (file word [] saved) := by
  have run:=move_executes 61 (1:Fin 64) 0 63 (by decide) (by decide) (by decide)
    (file [] word saved) (by simpa [file] using scratch)
  have source:file [] word saved 1=word := by simp [file]
  have target:file [] word saved 0=[] := by simp [file]
  rw [source,target,List.append_nil] at run
  have final : Function.update (Function.update (file [] word saved) 0 word) 1 []=file word [] saved := by
    funext r;by_cases zero:r=0 <;> by_cases one:r=1 <;> simp [file,zero,one]
  rwa [final] at run

abbrev moveInputSaved (i : Fin 8) : Routine 62 := move 61 0 (slot i) 63

theorem moveInputSaved_executes (i : Fin 8) (notScratch:i≠7) (word output : List Bool)
    (saved : Fin 8 → List Bool) (vacant:saved i=[]) (scratch:saved 7=[]) :
    Executes (moveInputSaved i) (file word output saved) (6*word.length+4)
      (file [] output (Function.update saved i word)) := by
  have different0:(0:Fin 64)≠slot i := by
    intro eq;have h:=congrArg Fin.val eq;change 0=56+i.val at h;omega
  have different63:slot i≠63 := by
    intro eq;apply notScratch;apply Fin.ext;have h:=congrArg Fin.val eq;change 56+i.val=63 at h;omega
  have run:=move_executes 61 (0:Fin 64) (slot i) 63 different0 (by decide) different63
    (file word output saved) (by simpa [file] using scratch)
  have source:file word output saved 0=word := by simp [file]
  rw [source,file_slot,vacant,List.append_nil,file_update_slot] at run
  have target : Function.update (file word output (Function.update saved i word)) 0 []=
      file [] output (Function.update saved i word) := by
    funext r;by_cases zero:r=0 <;> simp [file,zero]
  rwa [target] at run

abbrev saveOutput (i : Fin 8) : Routine 62 := ofProgram (ListPrograms.copyProgram 61 1 (slot i) 63)

theorem saveOutput_executes (i : Fin 8) (notScratch:i≠7) (word input : List Bool)
    (saved : Fin 8 → List Bool) (vacant:saved i=[]) (scratch:saved 7=[]) :
    Executes (saveOutput i) (file input word saved) (5*word.length+2)
      (file input word (Function.update saved i word)) := by
  have different1:(1:Fin 64)≠slot i := by
    intro eq;have h:=congrArg Fin.val eq;change 1=56+i.val at h;omega
  have different63:slot i≠63 := by
    intro eq;apply notScratch;apply Fin.ext;have h:=congrArg Fin.val eq;change 56+i.val=63 at h;omega
  have run:=copy_executes 61 (1:Fin 64) (slot i) 63 different1 (by decide) different63
    (file input word saved) (by simpa [file] using scratch)
  have source:file input word saved 1=word := by simp [file]
  rwa [source,file_slot,vacant,List.append_nil,file_update_slot] at run

end Counting.StackMachine.AuditComplete
