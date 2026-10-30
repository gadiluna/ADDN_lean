import Counting.StackBinarySubtractRoutine
import Counting.StackBinaryNormalize
import Counting.StackRoutineBasic

namespace Counting.StackMachine.Binary
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Source, result, copied source, constant one, reversed difference,
normalization frame, scratch, branch flag. -/
abbrev PredWorkspace (extra : Nat) := Fin 8 ↪ Fin (extra+8)

def positivePredecessor (extra : Nat) (w : PredWorkspace extra) : Routine (extra+6) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+5) (w 0) (w 2) (w 6)))
    (sequence (pushBit (w 3) true)
      (sequence (ofProgram (subtractProgram (extra+5) (w 2) (w 3) (w 4)))
        (sequence (ofProgram (ListPrograms.reverseProgram (extra+6) (w 4) (w 1)))
          (normalizePayload (extra+5) (w 1) (w 5) (w 6)))))

theorem positivePredecessor_executes (extra : Nat) (w : PredWorkspace extra)
    (store : Fin (extra+8)→List Bool) (n : Nat) (positive : 0<n)
    (source : store (w 0)=n.bits)
    (empty : ∀ i∈([1,2,3,4,5,6] : List (Fin 8)),store (w i)=[]) :
    ∃ time ≤ 50*(n.size+1),
      Executes (positivePredecessor extra w) store time (Function.update store (w 1) (n-1).bits) := by
  have copying := copy_executes (extra+5) (w 0) (w 2) (w 6)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) store (empty 6 (by simp))
  let copied := Function.update store (w 2) n.bits
  have copyAs : Executes (ofProgram (ListPrograms.copyProgram (extra+5) (w 0) (w 2) (w 6)))
      store (5*n.bits.length+2) copied := by
    simpa +instances [copied,source,empty] using copying
  have pushing := pushBit_executes (w 3) true copied
  let ready := Function.update copied (w 3) [true]
  have pushAs : Executes (pushBit (w 3) true) copied 1 ready := by
    simpa [ready,copied,w.injective.eq_iff,empty] using pushing
  have subtracting := binary_subtract_executes (extra+5) (w 2) (w 3) (w 4)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) ready
  let digits := (subtractBits false n.bits [true]).1
  let reversed := Function.update store (w 4) digits.reverse
  have subAs : Executes (ofProgram (subtractProgram (extra+5) (w 2) (w 3) (w 4)))
      ready (3*max n.bits.length 1+2) reversed := by
    have s2 : ready (w 2)=n.bits := by simp [ready,copied,w.injective.eq_iff]
    have s3 : ready (w 3)=[true] := by simp [ready]
    rw [s2,s3] at subtracting
    simp only [List.length_cons,List.length_nil] at subtracting
    convert subtracting using 1
    funext r
    by_cases e2 : r=w 2
    · subst r;simp [reversed,w.injective.eq_iff,empty]
    · by_cases e3 : r=w 3
      · subst r;simp [reversed,w.injective.eq_iff,empty]
      · simp [reversed,ready,copied,digits,e2,e3,Function.update_apply,w.injective.eq_iff,empty]
  have reversing := reverse_executes (extra+6) (w 4) (w 1)
    (by simp [w.injective.eq_iff]) reversed
  let forward := Function.update store (w 1) digits
  have revAs : Executes (ofProgram (ListPrograms.reverseProgram (extra+6) (w 4) (w 1)))
      reversed (2*digits.length+1) forward := by
    have contents : reversed (w 4)=digits.reverse := by simp [reversed]
    rw [contents,List.length_reverse,List.reverse_reverse] at reversing
    convert reversing using 1
    funext r
    by_cases e4 : r=w 4
    · subst r;simp [forward,w.injective.eq_iff,empty]
    · simp [forward,reversed,e4,Function.update_apply,w.injective.eq_iff,empty]
  have normalizing := normalizePayload_executes (extra+5) (w 1) (w 5) (w 6)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) forward
    (by simp [forward,w.injective.eq_iff,empty]) (by simp [forward,w.injective.eq_iff,empty])
  have value : Encoding.value digits=n-1 := by
    have one : Encoding.value [true]=1 := by decide
    have result := subtractBits_of_le false n.bits [true] (by simp [one,Encoding.value_bits];omega)
    simpa only [one,Encoding.value_bits,Bool.false_eq_true,ite_false,Nat.add_zero] using result
  have normAs : Executes (normalizePayload (extra+5) (w 1) (w 5) (w 6)) forward
      (normalizePayloadCost digits) (Function.update store (w 1) (n-1).bits) := by
    simpa only [forward,Function.update_self,Function.update_idem,value] using normalizing
  have execution := copyAs.sequence (pushAs.sequence (subAs.sequence (revAs.sequence normAs)))
  refine ⟨_,?_,execution⟩
  have length : digits.length=max n.bits.length 1 := subtractBits_length false n.bits [true]
  have normBound := normalizePayloadCost_le digits
  rw [length,Encoding.bits_length] at normBound
  rw [length,Encoding.bits_length]
  omega

end Counting.StackMachine.Binary
