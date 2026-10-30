import Counting.StackBinaryComparePreserving
import Counting.StackEncodingRoutineInterfaces
import Counting.StackEncodingBranch
import Counting.StackRoutineBasic
import Counting.StackEncodingPair

namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false

/-- Negate one status bit, leaving its tail unchanged. -/
def negateFlag (extra : Nat) (flag : Fin (extra+2)) : Routine extra :=
  branchRoutine flag (pushBit flag false) (pushBit flag true)

theorem negateFlag_executes (extra : Nat) (flag : Fin (extra+2)) (store : Store extra)
    (bit : Bool) (tail : List Bool) (status : store flag=bit::tail) :
    Executes (negateFlag extra flag) store 2 (Function.update store flag ((!bit)::tail)) := by
  have pushed:=pushBit_executes flag (!bit) (Function.update store flag tail)
  simp only [Function.update_self,Function.update_idem] at pushed
  cases bit with
  | false => exact branch_executes_false flag _ _ store _ tail 1 status pushed
  | true => exact branch_executes_true flag _ _ store _ tail 1 status pushed

/-- Positive, canonical natural payload. The leading zero ensures that the
empty payload is rejected as well; every original payload bit is still read. -/
def positiveGuard (extra : Nat) (source status : Fin (extra+2)) : Routine extra :=
  sequence (pushBit source false)
    (sequence (ofProgram (canonicalProgram extra source status))
      (ofProgram (combineFlagsProgram extra status)))

theorem positiveGuard_executes (extra : Nat) (source status : Fin (extra+2))
    (distinct : source≠status) (store : Store extra) (accepted : Bool) (tail : List Bool)
    (flag : store status=accepted::tail) :
    Executes (positiveGuard extra source status) store ((store source).length+9)
      (Function.update (Function.update store source []) status
        ((accepted && lastPayloadBit false (store source))::tail)) := by
  let pushed:=Function.update store source (false::store source)
  have first:=pushBit_executes source false store
  have second:=canonical_executes extra source status distinct pushed
  simp only [pushed,Function.update_self,Function.update_of_ne (Ne.symm distinct),
    Function.update_idem,canonicalPayload,lastPayloadBit,List.length_cons] at second
  let checked:=Function.update (Function.update store source []) status
    (lastPayloadBit false (store source)::store status)
  have third:=combineFlags_executes extra status checked accepted
    (lastPayloadBit false (store source)) tail (by simp [checked,flag])
  simp only [checked,Function.update_idem] at third
  have composed:=first.sequence (second.sequence third)
  convert composed using 1 <;> first | rfl | omega

/-- Preserve a payload while accumulating its canonicality in status. -/
def canonicalGuard (extra : Nat) (w : Fin 4 ↪ Fin (extra+4)) : Routine (extra+2) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+1) (w 0) (w 2) (w 3)))
    (sequence (ofProgram (canonicalProgram (extra+2) (w 2) (w 1)))
      (ofProgram (combineFlagsProgram (extra+2) (w 1))))

theorem canonicalGuard_executes (extra : Nat) (w : Fin 4 ↪ Fin (extra+4))
    (store : Store (extra+2)) (accepted : Bool) (tail : List Bool)
    (flag : store (w 1)=accepted::tail) (copyEmpty : store (w 2)=[]) (scratchEmpty : store (w 3)=[]) :
    Executes (canonicalGuard extra w) store (6*(store (w 0)).length+9)
      (Function.update store (w 1) ((accepted && canonicalPayload (store (w 0)))::tail)) := by
  have ne (i j : Fin 4) (h : i≠j) : w i≠w j := fun eq=>h (w.injective eq)
  let copied:=Function.update store (w 2) (store (w 0))
  have first : Executes (ofProgram (ListPrograms.copyProgram (extra+1) (w 0) (w 2) (w 3)))
      store (5*(store (w 0)).length+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,copyEmpty,List.append_nil,copied] using
      copy_executes (extra+1) (w 0) (w 2) (w 3) (ne 0 2 (by decide))
        (ne 0 3 (by decide)) (ne 2 3 (by decide)) store scratchEmpty
  have restored : Function.update copied (w 2) []=store := by
    simp only [copied,Function.update_idem]
    rw [←copyEmpty,Function.update_eq_self]
  have second:=canonical_executes (extra+2) (w 2) (w 1) (ne 2 1 (by decide)) copied
  simp only [copied,Function.update_self] at second
  rw [restored] at second
  simp only [Function.update_of_ne (ne 1 2 (by decide))] at second
  let checked:=Function.update store (w 1) (canonicalPayload (store (w 0))::store (w 1))
  have third:=combineFlags_executes (extra+2) (w 1) checked accepted
    (canonicalPayload (store (w 0))) tail (by simp [checked,flag])
  simp only [checked,Function.update_idem] at third
  have composed:=first.sequence (second.sequence third)
  convert composed using 1 <;> first | rfl | omega

/-- Preserve both numeric operands and accumulate their strict comparison.
No canonicality of either payload is assumed by this arithmetic routine. -/
def strictGuard (extra : Nat) (w : Fin 6 ↪ Fin (extra+6)) : Routine (extra+4) :=
  sequence (Binary.preservingComparison extra w)
    (sequence (negateFlag (extra+4) (w 2)) (ofProgram (combineFlagsProgram (extra+4) (w 2))))

theorem strictGuard_executes (extra : Nat) (w : Fin 6 ↪ Fin (extra+6))
    (store : Store (extra+4)) (accepted : Bool) (tail : List Bool)
    (flag : store (w 2)=accepted::tail) (a : store (w 3)=[]) (b : store (w 4)=[]) (c : store (w 5)=[]) :
    Executes (strictGuard extra w) store
      (Binary.preservingCompareCost (store (w 0)) (store (w 1))+7)
      (Function.update store (w 2)
        ((accepted && !Binary.compareBits true (store (w 0)) (store (w 1)))::tail)) := by
  have first:=Binary.preservingComparison_executes extra w store a b c
  let checked:=Function.update store (w 2) (Binary.compareBits true (store (w 0)) (store (w 1))::store (w 2))
  have second:=negateFlag_executes (extra+4) (w 2) checked
    (Binary.compareBits true (store (w 0)) (store (w 1))) (store (w 2)) (by simp [checked])
  simp only [checked,Function.update_idem] at second
  let negated:=Function.update store (w 2) ((!Binary.compareBits true (store (w 0)) (store (w 1)))::store (w 2))
  have third:=combineFlags_executes (extra+4) (w 2) negated accepted
    (!Binary.compareBits true (store (w 0)) (store (w 1))) tail (by simp [negated,flag])
  simp only [negated,Function.update_idem] at third
  have composed:=first.sequence (second.sequence third)
  exact composed

end Counting.StackMachine.EncodingPrograms
