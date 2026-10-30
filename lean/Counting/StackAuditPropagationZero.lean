import Counting.StackRepeatBit
import Counting.StackRoutineUnary
import Counting.StackRoutineMove
import Counting.StackEncodingFrameStore
import Counting.StackFrameReplaceArray

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

private theorem zero_sequence (n : Nat) :
    Encoding.sequence Encoding.natural (List.replicate n 0)=List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,Encoding.sequence,ih]
    rfl

theorem zero_array_word (n : Nat) :
    (Encoding.array Encoding.natural).encode (Array.replicate n 0)=
      Encoding.natural.encode n++List.replicate n false := by
  simp only [Encoding.array,Encoding.transport,Array.toList_replicate,Encoding.list,List.length_replicate,zero_sequence]

abbrev zeroArray : Routine 4 := sequence (ofProgram (ListPrograms.copyProgram 3 0 2 4))
  (sequence (repeatBit 2 5 false)
    (sequence (ofProgram (ListPrograms.copyProgram 3 0 2 4))
      (sequence (ofProgram (Unary.toBinaryProgram 3 2 3 4))
        (sequence (frameRoutine 3 3 5 4) (move 3 5 1 4)))))

/-- Allocate the actual zero-weight array from the explicit node-count
counter. The counter is preserved, the length header is generated in binary,
and every output cell and temporary movement is charged. -/
theorem zeroArray_executes (store : Store 4) (n : Nat)
    (source : store 0=List.replicate n true)
    (empty : ∀ i : Fin 6,i≠0 → store i=[]) :
    ∃ time ≤ 80*(n+1)^2,
      Executes zeroArray store time
        (Function.update store 1 ((Encoding.array Encoding.natural).encode (Array.replicate n 0))) := by
  have a := copy_executes 3 (0:Fin 6) 2 4 (by decide) (by decide) (by decide) store (empty _ (by decide))
  rw [source,empty 2 (by decide),List.append_nil,List.length_replicate] at a
  let copied := Function.update store 2 (List.replicate n true)
  have b := repeatBit_executes (2:Fin 6) 5 false (by decide) copied
  have input : copied 2=List.replicate n true := by simp [copied]
  rw [input,List.length_replicate] at b
  let zeros := Function.update store 5 (List.replicate n false)
  have bs : Function.update (Function.update copied 2 []) 5
      (List.replicate n false++copied 5)=zeros := by
    have restored : Function.update copied 2 []=store := by
      simp only [copied,Function.update_idem]
      rw [←empty 2 (by decide),Function.update_eq_self]
    rw [restored]
    simp [copied,zeros,empty]
  rw [bs] at b
  have c := copy_executes 3 (0:Fin 6) 2 4 (by decide) (by decide) (by decide) zeros (by simp [zeros,empty])
  have zerosSource : zeros 0=List.replicate n true := by simp [zeros,source]
  have zerosTarget : zeros 2=[] := by simp [zeros,empty]
  rw [zerosSource,zerosTarget,List.append_nil,List.length_replicate] at c
  let counted := Function.update zeros 2 (List.replicate n true)
  obtain ⟨binaryTime,binaryBound,d⟩ := toBinary_executes 3 (2:Fin 6) 3 4
    (by decide) (by decide) (by decide) counted 0 (by simp [counted,zeros,empty]) (by simp [counted,zeros,empty])
  have countAt : counted 2=List.replicate n true := by simp [counted]
  rw [countAt,List.length_replicate,Nat.zero_add] at d binaryBound
  let binary := Function.update zeros 3 n.bits
  have ds : Function.update (Function.update counted 2 []) 3 n.bits=binary := by
    have restored : Function.update counted 2 []=zeros := by
      simp only [counted,Function.update_idem]
      rw [←zerosTarget,Function.update_eq_self]
    rw [restored]
  rw [ds] at d
  have e := frame_executes_updates 3 (3:Fin 6) 5 4 (by decide) (by decide) (by decide) binary (by simp [binary,zeros,empty])
  let word := (Encoding.array Encoding.natural).encode (Array.replicate n 0)
  let framed := Function.update store 5 word
  have es : Function.update (Function.update binary 3 []) 5 (Encoding.frame (binary 3)++binary 5)=framed := by
    have restored : Function.update binary 3 []=zeros := by
      simp only [binary,Function.update_idem]
      have z3 : zeros 3=[] := by simp [zeros,empty]
      rw [←z3,Function.update_eq_self]
    rw [restored]
    simp [binary,zeros,framed,word,zero_array_word,Encoding.natural]
  rw [es] at e
  change Executes _ _ (5*n.bits.length+4) _ at e
  have f := move_executes 3 (5:Fin 6) 1 4 (by decide) (by decide) (by decide) framed (by simp [framed,empty])
  have fs : Function.update (Function.update framed 1 (framed 5++framed 1)) 5 []=
      Function.update store 1 word := by
    funext r
    by_cases r1 : r=1 <;> by_cases r5 : r=5 <;> simp [framed,r1,r5,empty]
  rw [fs] at f
  change Executes _ _ (6*word.length+4) _ at f
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence (e.sequence f))))⟩
  have outputLength : word.length=2*n.size+1+n := by
    simp only [word,zero_array_word,List.length_append,Encoding.natural_length,List.length_replicate]
  have bitsBound : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [Encoding.bits_length]
  rw [outputLength]
  nlinarith

end Counting.StackMachine.AuditPropagation
