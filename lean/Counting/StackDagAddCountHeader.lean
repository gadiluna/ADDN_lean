import Counting.StackDagAddCountSelect
import Counting.StackEncodingListReadHeader
import Counting.StackDagEmptyGuard

namespace Counting.StackMachine.DagUpdate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def AddWorkspace.header (w : AddWorkspace extra) : FullListWorkspace (extra+3) :=
  (⟨![0,4,6,18,17,7,1,2,8,3,5,9,10,11,12,13,19],by decide⟩ : Fin 17 ↪ Fin 20).trans w

def headerScratch : List (Fin 20) := [6,7,8,9,10,11,12,13,17,18,19]

theorem readHeader_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (edges : List (Nat×Nat)) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list edgeCodec).encode edges++suffix)
    (flag : store (w 4)=true::tail) (empty : ∀ j∈headerScratch,store (w j)=[]) :
    ∃ time ≤ 1820*((store (w 0)).length+1)^3,
      Executes (readListHeader (extra+3) w.header) store time
        (Function.update (Function.update store (w 0) (Encoding.sequence edgeCodec edges++suffix))
          (w 17) (List.replicate edges.length true)) := by
  apply readListHeader_canonical (extra+3) w.header store true tail flag
  · intro j member
    fin_cases j <;> simp_all [AddWorkspace.header,headerScratch]
  · intro edge
    simp [edgeCodec,Encoding.product,Encoding.natural_length]
  · exact source

def initializePending (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (discardBit (w 4))
    (sequence (DagValidation.emptyFlag (w 2) (w 4))
      (branchRoutine (w 4) (pushBit (w 4) false) (pushBit (w 4) true)))

theorem initializePending_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (count : Nat) (tail : List Bool) (increment : store (w 2)=count.bits) (flag : store (w 4)=true::tail) :
    ∃ time ≤ 8, Executes (initializePending extra w) store time
      (Function.update store (w 4) (decide (count≠0)::tail)) := by
  have discarding:=discardBit_executes (w 4) store
  rw [flag,List.tail_cons] at discarding
  let clean:=Function.update store (w 4) tail
  have testing:=DagValidation.emptyFlag_executes (w 2) (w 4) clean
  have sourceAt : clean (w 2)=count.bits := by simp [clean,w.injective.eq_iff,increment]
  have flagAt : clean (w 4)=tail := by simp [clean]
  rw [sourceAt,flagAt] at testing
  have bitsEmpty : count.bits=[] ↔ count=0 := by simpa only [Nat.zero_bits] using bits_eq_iff count 0
  simp only [bitsEmpty] at testing
  by_cases zero : count=0
  · subst count
    simp only [Nat.zero_bits,DagValidation.emptyFlagCost,if_true,decide_true] at testing
    have pushing:=pushBit_executes (w 4) false clean
    simp only [clean,Function.update_self,Function.update_idem] at pushing
    have restoring : Function.update (Function.update clean (w 4) (true::tail)) (w 4) tail=clean := by
      simp [clean]
    have branch:=branch_executes_true (w 4) (pushBit (w 4) false) (pushBit (w 4) true)
      (Function.update clean (w 4) (true::tail)) _ tail 1 (by simp) (by rw [restoring];exact pushing)
    have combined:=discarding.sequence (testing.sequence branch)
    exact ⟨7,by decide,combined⟩
  · have nonempty : count.bits≠[] := fun same=>zero (bitsEmpty.mp same)
    simp only [zero,decide_false,DagValidation.emptyFlagCost,nonempty,if_false] at testing
    have pushing:=pushBit_executes (w 4) true clean
    simp only [clean,Function.update_self,Function.update_idem] at pushing
    have restoring : Function.update (Function.update clean (w 4) (false::tail)) (w 4) tail=clean := by
      simp [clean]
    have branch:=branch_executes_false (w 4) (pushBit (w 4) false) (pushBit (w 4) true)
      (Function.update clean (w 4) (false::tail)) _ tail 1 (by simp) (by rw [restoring];exact pushing)
    have combined:=discarding.sequence (testing.sequence branch)
    exact ⟨8,by decide,by simpa only [initializePending,zero,ne_eq,not_false_eq_true,decide_true] using combined⟩

end Counting.StackMachine.DagUpdate
