import Counting.StackAnchorRowLoop
import Counting.StackRoutineUnary

namespace Counting.StackMachine.AnchorRow
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev finish : Routine 38 := sequence (ofProgram (Unary.toBinaryProgram 37 36 38 39))
  (sequence (frameRoutine 37 38 39 22)
    (sequence (ofProgram (ListPrograms.reverseProgram 38 35 22)) (move 37 39 22 38)))

/-- Materialize the real list header from its unary counter, then reverse
and attach the emitted fields. No serialization step is treated as free. -/
theorem finish_executes (store : Store 38) (stream : List Bool)
    (outputEmpty : store 22=[]) (binaryEmpty : store 38=[]) (scratchEmpty : store 39=[])
    (reversed : store 35=stream.reverse) :
    ∃ time ≤ 4*(store 36).length*((store 36).length+1)+
        17*(store 36).length+2*stream.length+20,
      Executes finish store time
        (Function.update (Function.update (Function.update store 36 []) 35 []) 22
          (Encoding.natural.encode (store 36).length++stream)) := by
  obtain ⟨time,bounded,a⟩ := toBinary_executes 37 (36:Fin 40) 38 39 (by decide) (by decide) (by decide)
    store 0 binaryEmpty scratchEmpty
  simp only [Nat.zero_add] at a bounded
  let binary := Function.update (Function.update store 36 []) 38 (store 36).length.bits
  change Executes _ store time binary at a
  have b := frame_executes_updates 37 (38:Fin 40) 39 22 (by decide) (by decide) (by decide) binary
    (by simp [binary,outputEmpty])
  let framed := Function.update (Function.update store 36 []) 39 (Encoding.natural.encode (store 36).length)
  have bs : Function.update (Function.update binary 38 []) 39 (Encoding.frame (binary 38)++binary 39)=framed := by
    funext r
    by_cases r36 : r=36
    · subst r;simp [binary,framed]
    · by_cases r38 : r=38
      · subst r;simp [binary,framed,binaryEmpty]
      · by_cases r39 : r=39
        · subst r;simp [binary,framed,scratchEmpty,Encoding.natural]
        · simp [binary,framed,r36,r38,r39]
  rw [bs] at b
  change Executes _ binary (5*(store 36).length.bits.length+4) framed at b
  have c := reverse_executes 38 (35:Fin 40) 22 (by decide) framed
  let forward := Function.update (Function.update framed 35 []) 22 stream
  have cs : Function.update (Function.update framed 35 []) 22 ((framed 35).reverse++framed 22)=forward := by
    simp [forward,framed,reversed,outputEmpty]
  rw [cs] at c
  have readStream : framed 35=stream.reverse := by simp [framed,reversed]
  rw [readStream] at c
  have d := move_executes 37 (39:Fin 40) 22 38 (by decide) (by decide) (by decide) forward
    (by simp [forward,framed,binaryEmpty])
  have ds : Function.update (Function.update forward 22 (forward 39++forward 22)) 39 []=
      Function.update (Function.update (Function.update store 36 []) 35 []) 22
        (Encoding.natural.encode (store 36).length++stream) := by
    funext r
    by_cases r22 : r=22
    · subst r;simp [forward,framed]
    · by_cases r35 : r=35
      · subst r;simp [forward,framed]
      · by_cases r36 : r=36
        · subst r;simp [forward,framed]
        · by_cases r39 : r=39
          · subst r;simp [forward,framed,scratchEmpty]
          · simp [forward,framed,r22,r35,r36,r39]
  rw [ds] at d
  change Executes _ forward (6*(Encoding.natural.encode (store 36).length).length+4) _ at d
  have composed := a.sequence (b.sequence (c.sequence d))
  refine ⟨_,?_,composed⟩
  have size : (store 36).length.size ≤ (store 36).length := Nat.size_le.mpr (store 36).length.lt_two_pow_self
  simp only [Encoding.bits_length,Encoding.natural_length,List.length_reverse]
  omega

end Counting.StackMachine.AnchorRow
