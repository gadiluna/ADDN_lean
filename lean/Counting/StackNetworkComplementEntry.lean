import Counting.StackNetworkComplementFile
import Counting.StackEncodingFlaggedCorrectness
import Counting.StackEncodingRoutineInterfaces
import Counting.StackEncodingListSemantics

namespace Counting.StackMachine.NetworkComplement
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def initialData (input witness : List Bool) (accepted : Bool) : Fin 30→List Bool :=
  fun r=>if r=0 then input else if r=1 then witness else if r=2 then [accepted] else []

def prepare : Routine 158 := sequence (ofProgram (flaggedProgram 156 0 130 1 132))
  (sequence (ofProgram (ListPrograms.copyProgram 157 0 131 1)) (clear 0))

theorem prepare_executes (input : List Bool) :
    ∃time≤9*input.length+9,
      Executes prepare (inputStore 158 input) time
        (file (initialData (unframePayload input) (unframeSuffix input) (Encoding.unframe input).isSome)) := by
  obtain ⟨t0,b0,r0⟩ := flagged_executes 156 (0:Fin 160) 130 1 132
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (inputStore 158 input) (by simp [inputStore])
  rw [flagged_result_updates 156 (0:Fin 160) 130 1 132
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (inputStore 158 input) (by simp [inputStore])] at r0
  simp only [inputStore,show (130:Fin 160)≠0 by decide,show (132:Fin 160)≠0 by decide,
    ↓reduceIte,List.append_nil] at r0
  let parsed := Function.update (Function.update (Function.update (inputStore 158 input)
    0 (unframeSuffix input)) 130 (unframePayload input)) 132 [(Encoding.unframe input).isSome]
  have copying := copy_executes 157 (0:Fin 160) 131 1 (by decide) (by decide) (by decide)
    parsed (by simp [parsed,inputStore])
  have p0 : parsed 0=unframeSuffix input := by simp [parsed]
  have p1 : parsed 131=[] := by simp [parsed,inputStore]
  rw [p0,p1,List.append_nil] at copying
  let copied := Function.update parsed 131 (unframeSuffix input)
  have clearing := clear_executes (0:Fin 160) copied
  rw [show copied 0=unframeSuffix input by simp [copied,p0]] at clearing
  have final : Function.update copied 0 []=
      file (initialData (unframePayload input) (unframeSuffix input) (Encoding.unframe input).isSome) := by
    funext r
    fin_cases r <;> simp [copied,parsed,file,initialData,inputStore]
  rw [final] at clearing
  have suffixBound := unframe_suffix_length input
  refine ⟨t0+1+(5*(unframeSuffix input).length+2+1+((unframeSuffix input).length+1)),?_,
    r0.sequence (copying.sequence clearing)⟩
  change t0≤3*input.length+4 at b0
  omega

def copyExternal (source target : Fin 30) : Routine 158 :=
  ofProgram (ListPrograms.copyProgram 157 (context source) (context target) 0)

theorem copyExternal_executes (data : Fin 30→List Bool) (source target : Fin 30) (different : source≠target) :
    Executes (copyExternal source target) (file data) (5*(data source).length+2)
      (file (Function.update data target (data source++data target))) := by
  have run := copy_executes 157 (context source) (context target) 0
    (fun h=>different (context.injective h)) (context_ne_local source 0 (by decide))
    (context_ne_local target 0 (by decide)) (file data) (by simp)
  simpa only [copyExternal,file_context,file_update] using run

def assemble : Routine 158 := sequence (copyExternal 1 6)
  (sequence (copyExternal 5 6) (copyExternal 4 6))

theorem assemble_executes (data : Fin 30→List Bool) (empty : data 6=[]) :
    Executes assemble (file data) (5*((data 1).length+(data 5).length+(data 4).length)+8)
      (file (Function.update data 6 (data 4++data 5++data 1))) := by
  have r0 := copyExternal_executes data 1 6 (by decide)
  rw [empty,List.append_nil] at r0
  let d1 := Function.update data 6 (data 1)
  have r1 := copyExternal_executes d1 5 6 (by decide)
  have d15 : d1 5=data 5 := by simp [d1]
  have d16 : d1 6=data 1 := by simp [d1]
  rw [d15,d16] at r1
  let d2 := Function.update d1 6 (data 5++data 1)
  have r2 := copyExternal_executes d2 4 6 (by decide)
  have d24 : d2 4=data 4 := by simp [d2,d1]
  have d26 : d2 6=data 5++data 1 := by simp [d2]
  rw [d24,d26] at r2
  have final : Function.update d2 6 (data 4++(data 5++data 1))=
      Function.update data 6 (data 4++data 5++data 1) := by
    simp only [d2,d1,Function.update_idem,List.append_assoc]
  rw [final] at r2
  have composed := r0.sequence (r1.sequence r2)
  simpa only [assemble,show 5*(data 1).length+2+1+(5*(data 5).length+2+1+(5*(data 4).length+2))=
    5*((data 1).length+(data 5).length+(data 4).length)+8 by omega] using composed

end Counting.StackMachine.NetworkComplement
