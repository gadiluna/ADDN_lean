import Counting.ExternalMatchingLiteral
import Counting.ExternalMatchingLiteralBounds
import Counting.ExternalMatchingCompletionLoop

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def literalRows (first width shift occurrence : Nat) : List (Nat×Bool) → List (List Nat)
  | [] => []
  | literal::rest => literalEdge first literal.1 width occurrence shift literal.2::literalRows first width shift (occurrence+1) rest

def generateLiteralLoop (extra : Nat) (w : LiteralWorkspace extra) : Routine (extra+46) :=
  forEach (w 24) (generateLiteral extra w)

def literalLoopResult (extra : Nat) (w : LiteralWorkspace extra) (store : Fin (extra+48) → List Bool)
    (first width shift occurrence : Nat) (literals : List (Nat×Bool)) (suffix : List Bool) :=
  Function.update (Function.update (Function.update (Function.update store (w 0) suffix) (w 24) [])
    (w 34) (List.replicate (occurrence+literals.length) true)) (w 36)
    ((Encoding.sequence (Encoding.list Encoding.natural) (literalRows first width shift occurrence literals)).reverse++store (w 36))

theorem generateLiteralLoop_executes (extra : Nat) (w : LiteralWorkspace extra)
    (literals : List (Nat×Bool)) (n width shift first bound occurrence : Nat)
    (store : Fin (extra+48) → List Bool) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence (Encoding.product Encoding.natural Encoding.boolean) literals++suffix)
    (counter : store (w 24)=List.replicate literals.length true)
    (status : store (w 1)=accepted::tail) (nValue : (store (w 17)).length=n)
    (widthValue : store (w 32)=List.replicate width true) (shiftValue : store (w 33)=List.replicate shift true)
    (occurrenceValue : store (w 34)=List.replicate occurrence true) (firstValue : (store (w 35)).length=first)
    (sourceBound : (store (w 0)).length ≤ bound) (hn : n ≤ bound) (hw : width ≤ bound)
    (hs : shift ≤ bound) (hf : first ≤ bound) (ho : occurrence+literals.length ≤ bound)
    (fits : ∀ literal∈literals,literal.1 ≤ n)
    (empty : ∀ i∈generateLiteralScratch,store (w i)=[]) :
    ∃ time ≤ literals.length*(8000*(bound+1)^4+2)+1,
      Executes (generateLiteralLoop extra w) store time
        (literalLoopResult extra w store first width shift occurrence literals suffix) := by
  induction literals generalizing store occurrence with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 24) (generateLiteral extra w) store counter
    have unchanged : literalLoopResult extra w store first width shift occurrence [] suffix=store := by
      simp only [literalLoopResult,literalRows,Encoding.sequence,List.length_nil,Nat.add_zero,List.reverse_nil,List.nil_append]
      have counterEmpty : store (w 24)=[] := counter
      have sourceEq : store (w 0)=suffix := source
      rw [←sourceEq,Function.update_eq_self,←counterEmpty,Function.update_eq_self,←occurrenceValue,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | cons literal rest ih =>
    let consumed := Function.update store (w 24) (List.replicate rest.length true)
    let remaining := Encoding.sequence (Encoding.product Encoding.natural Encoding.boolean) rest++suffix
    have consumedSource : consumed (w 0)=(Encoding.product Encoding.natural Encoding.boolean).encode literal++remaining := by
      simpa [consumed,remaining,w.injective.eq_iff,Encoding.sequence,List.append_assoc] using source
    have consumedEmpty (i : Fin 48) (member : i∈generateLiteralScratch) : consumed (w i)=[] := by
      have different : i≠24 := by intro same;subst i;simp [generateLiteralScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := generateLiteral_executes extra w consumed
      literal.1 width occurrence shift literal.2 accepted remaining tail consumedSource
      (by simp [consumed,w.injective.eq_iff,status])
      (by simpa [consumed,w.injective.eq_iff,nValue] using fits literal (by simp))
      (by simp [consumed,w.injective.eq_iff,widthValue])
      (by simp [consumed,w.injective.eq_iff,occurrenceValue])
      (by simp [consumed,w.injective.eq_iff,shiftValue]) consumedEmpty
    let next := generateLiteralResult extra w consumed literal.1 literal.2 remaining
    have nextSource : next (w 0)=Encoding.sequence (Encoding.product Encoding.natural Encoding.boolean) rest++suffix := by
      simp [next,generateLiteralResult,w.injective.eq_iff,remaining]
    have nextCounter : next (w 24)=List.replicate rest.length true := by simp [next,generateLiteralResult,consumed,w.injective.eq_iff]
    have nextStatus : next (w 1)=accepted::tail := by simp [next,generateLiteralResult,consumed,w.injective.eq_iff,status]
    have nextN : (next (w 17)).length=n := by simpa [next,generateLiteralResult,consumed,w.injective.eq_iff] using nValue
    have nextWidth : next (w 32)=List.replicate width true := by simp [next,generateLiteralResult,consumed,w.injective.eq_iff,widthValue]
    have nextShift : next (w 33)=List.replicate shift true := by simp [next,generateLiteralResult,consumed,w.injective.eq_iff,shiftValue]
    have nextOccurrence : next (w 34)=List.replicate (occurrence+1) true := by simp [next,generateLiteralResult,consumed,w.injective.eq_iff,occurrenceValue,List.replicate_succ]
    have nextFirst : (next (w 35)).length=first := by simpa [next,generateLiteralResult,consumed,w.injective.eq_iff] using firstValue
    have nextBound : (next (w 0)).length ≤ bound := by
      rw [nextSource]
      rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound ⊢
      omega
    have nextEmpty (i : Fin 48) (member : i∈generateLiteralScratch) : next (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [generateLiteralScratch] at member
      have b : i≠34 := by intro same;subst i;simp [generateLiteralScratch] at member
      have c : i≠36 := by intro same;subst i;simp [generateLiteralScratch] at member
      simpa [next,generateLiteralResult,w.injective.eq_iff,a,b,c] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih (occurrence+1) next nextSource nextCounter nextStatus nextN nextWidth nextShift
      nextOccurrence nextFirst nextBound (by simp only [List.length_cons] at ho;omega)
      (fun lit member=>fits lit (by simp [member])) nextEmpty
    have firstRun := repeat_iteration (w 24) (generateLiteral extra w) store true (List.replicate rest.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (generateLiteralLoop extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ 8000*(bound+1)^4 := by
      apply bodyBound.trans
      apply generateLiteralCost_polynomial
      · simpa [consumed,w.injective.eq_iff] using sourceBound
      · simpa [consumed,w.injective.eq_iff,nValue] using hn
      · exact hw
      · simp only [List.length_cons] at ho;omega
      · exact hs
      · simpa [consumed,w.injective.eq_iff,firstValue] using hf
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · simp only [List.length_cons];nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases a : r=w 0
      · subst r;simp [literalLoopResult,w.injective.eq_iff]
      · by_cases c : r=w 24
        · subst r;simp [literalLoopResult,w.injective.eq_iff]
        · by_cases b : r=w 34
          · subst r;simp [literalLoopResult,w.injective.eq_iff,Nat.add_comm,Nat.add_left_comm]
          · by_cases o : r=w 36
            · subst r
              simp [literalLoopResult,literalRows,next,generateLiteralResult,consumed,w.injective.eq_iff,
                firstValue,widthValue,shiftValue,occurrenceValue,Encoding.sequence,List.reverse_append,List.append_assoc]
            · simp [literalLoopResult,next,generateLiteralResult,consumed,a,c,b,o]

end Counting.External.MatchingMachine
