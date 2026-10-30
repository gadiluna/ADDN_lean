import Counting.StackProtocolAdvanceInput

namespace Counting.StackMachine.ProtocolAdvance
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

abbrev emitState (view : Fin 8) : Routine 254 := sequence (prependSaved view)
  (sequence (prependSaved 1) (sequence (prependSaved 0)
    (sequence (move 253 0 1 255) (pushBit 1 true))))

/-- State serialization performs real copies, framing, output transfer and
the option tag. The saved fields remain available until final cleanup. -/
theorem emitState_executes (view : Fin 8) (fits:view.val<6) (saved : Fin 8 → List Bool)
    (temporary:saved 6=[]) (scratch:saved 7=[]) :
    ∃ time≤ 50*((saved view).length+(saved 1).length+(saved 0).length+1),
      Executes (emitState view) (file [] [] saved) time
        (file [] (true::(Encoding.frame (saved 0)++Encoding.frame (saved 1)++Encoding.frame (saved view))) saved) := by
  have a:=prependSaved_executes view fits [] [] saved temporary scratch
  have b:=prependSaved_executes 1 (by decide) (Encoding.frame (saved view)) [] saved temporary scratch
  have c:=prependSaved_executes 0 (by decide) (Encoding.frame (saved 1)++Encoding.frame (saved view)) [] saved temporary scratch
  simp only [List.append_nil] at a
  let payload:=Encoding.frame (saved 0)++(Encoding.frame (saved 1)++Encoding.frame (saved view))
  have d:=move_executes 253 (0:Fin 256) 1 255 (by decide) (by decide) (by decide)
    (file payload [] saved) (by simpa [file] using scratch)
  have source:file payload [] saved 0=payload := by simp [file]
  have vacant:file payload [] saved 1=[] := by simp [file]
  rw [source,vacant,List.append_nil] at d
  have moved:Function.update (Function.update (file payload [] saved) 1 payload) 0 []=file [] payload saved := by
    funext r;by_cases zero:r=0 <;> by_cases one:r=1 <;> simp [file,zero,one]
  rw [moved] at d
  have e:=pushBit_executes (1:Fin 256) true (file [] payload saved)
  have result:Function.update (file [] payload saved) 1 (true::file [] payload saved 1)=
      file [] (true::(Encoding.frame (saved 0)++Encoding.frame (saved 1)++Encoding.frame (saved view))) saved := by
    funext r;by_cases one:r=1 <;> simp [file,one,payload,List.append_assoc]
  rw [result] at e
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  dsimp only [payload]
  simp only [List.length_append,Encoding.frame_length]
  omega

abbrev restoreHalted : Routine 254 := sequence (pushBit 248 true) (emitState 2)

theorem restoreHalted_executes (state : Executable.LocalState) (messages : List (Executable.Vista×Nat))
    (degree value : Nat) (halted : state.output=some value) :
    ∃ time≤ 60*((stateWord state).length+1),
      Executes restoreHalted
        (file [] [] (metadata (Encoding.natural.encode value) state.leaders state.vista messages degree [])) time
        (file [] (outputWord (some state))
          (metadata ((Encoding.optional Encoding.natural).encode state.output) state.leaders state.vista messages degree [])) := by
  let saved:=metadata (Encoding.natural.encode value) state.leaders state.vista messages degree []
  have a:=pushBit_executes (248:Fin 256) true (file [] [] saved)
  have source:file [] [] saved 248=Encoding.natural.encode value := by simp [file,saved,metadata]
  rw [source] at a
  have target:Function.update (file [] [] saved) 248 (true::Encoding.natural.encode value)=
      file [] [] (metadata ((Encoding.optional Encoding.natural).encode state.output)
        state.leaders state.vista messages degree []) := by
    change Function.update _ (slot 0) _=_
    rw [file_update_slot]
    congr 1
    funext r;fin_cases r <;> simp [saved,metadata,halted,Encoding.optional]
  rw [target] at a
  let restored:=metadata ((Encoding.optional Encoding.natural).encode state.output) state.leaders state.vista messages degree []
  obtain ⟨b,bbound,brun⟩:=emitState_executes 2 (by decide) restored rfl rfl
  have word:true::(Encoding.frame (restored 0)++Encoding.frame (restored 1)++Encoding.frame (restored 2))=
      outputWord (some state) := by
    simp only [outputWord,answerCodec,Encoding.optional]
    change true::_=true::stateWord state
    rw [stateWord_fields]
    rfl
  rw [word] at brun
  refine ⟨_,?_,a.sequence brun⟩
  have length:=congrArg List.length (stateWord_fields state)
  simp only [List.length_append,Encoding.frame_length,Encoding.natural_length] at length
  change b≤ 50*((Encoding.vista.encode state.vista).length+state.leaders.bits.length+
    ((Encoding.optional Encoding.natural).encode state.output).length+1) at bbound
  rw [Encoding.bits_length] at bbound
  omega

end Counting.StackMachine.ProtocolAdvance
