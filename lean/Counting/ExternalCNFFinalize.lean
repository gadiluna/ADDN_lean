import Counting.ExternalCNFClauseLayout
import Counting.ExternalCNFCount
import Counting.ExternalCNFHeaders

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def finalCountPositions : Fin 6 ↪ Fin 52 := ⟨![25,47,51,49,45,50],by decide⟩
def finalCountRoles (extra : Nat) (w : ClauseWorkspace extra) : CountWorkspace (extra+46) := finalCountPositions.trans w
def finalHeaderPositions : Fin 6 ↪ Fin 52 := ⟨![34,51,1,18,19,50],by decide⟩
def finalHeaderRoles (extra : Nat) (w : ClauseWorkspace extra) : HeaderWorkspace (extra+46) := finalHeaderPositions.trans w

def formulaFinalize (extra : Nat) (w : ClauseWorkspace extra) : Routine (extra+50) :=
  sequence (clauseCount (extra+46) (finalCountRoles extra w))
    (sequence (clear (w 1)) (sequence (ofProgram (ListPrograms.reverseProgram (extra+50) (w 42) (w 1)))
      (formulaHeaders (extra+46) (finalHeaderRoles extra w))))

def formulaFinalizeCost (m width index streamLength : Nat) :=
  15*width*m+19*m+18*width+22+2*streamLength+20*(m*(3*width+2)+1)^2+28*(index+1)^2+10

theorem formulaFinalize_executes (extra : Nat) (w : ClauseWorkspace extra) (store : Fin (extra+52) → List Bool)
    (m width index : Nat) (stream : List Bool) (status : Bool)
    (count : store (w 25)=List.replicate m true) (widthEq : (store (w 47)).length=width)
    (indexEq : store (w 34)=List.replicate index true) (output : store (w 42)=stream.reverse)
    (flag : store (w 1)=[status]) (empty : ∀ i∈([18,19,45,49,50,51] : List (Fin 52)),store (w i)=[]) :
    ∃ time ≤ formulaFinalizeCost m width index stream.length,
      Executes (formulaFinalize extra w) store time
        (Function.update (Function.update (Function.update store (w 51) (List.replicate (m*(3*width+2)) true))
          (w 42) []) (w 1) ((Encoding.list Encoding.boolean).encode (List.replicate index true)++
            Encoding.natural.encode (m*(3*width+2))++stream)) := by
  have counting := clauseCount_executes (extra+46) (finalCountRoles extra w) m width store count widthEq
    (empty 51 (by decide)) (empty 49 (by decide)) (empty 45 (by decide)) (empty 50 (by decide))
  let s1 := Function.update store (w 51) (List.replicate (m*(3*width+2)) true)
  change Executes _ store _ s1 at counting
  have clearing := clear_executes (w 1) s1
  have flagLen : (s1 (w 1)).length+1=2 := by simp [s1,w.injective.eq_iff,flag]
  rw [flagLen] at clearing
  let s2 := Function.update s1 (w 1) []
  have reversing := reverse_executes (extra+50) (w 42) (w 1) (by simp [w.injective.eq_iff]) s2
  have data : s2 (w 42)=stream.reverse := by simp [s2,s1,w.injective.eq_iff,output]
  rw [data,List.length_reverse,List.reverse_reverse] at reversing
  let s3 := Function.update (Function.update s1 (w 42) []) (w 1) stream
  have reverseResult : Function.update (Function.update s2 (w 42) []) (w 1) (stream++s2 (w 1))=s3 := by
    funext r
    by_cases a : r=w 1
    · subst r;simp [s2,s3]
    · simp [s2,s3,Function.update_apply,a]
  rw [reverseResult] at reversing
  obtain ⟨ht,hb,headers⟩ := formulaHeaders_executes (extra+46) (finalHeaderRoles extra w) index (m*(3*width+2)) s3
    (by simp [finalHeaderRoles,finalHeaderPositions,s3,s1,w.injective.eq_iff,indexEq])
    (by simp [finalHeaderRoles,finalHeaderPositions,s3,s1,w.injective.eq_iff])
    (by simp [finalHeaderRoles,finalHeaderPositions,s3,s1,w.injective.eq_iff,empty 18 (by decide)])
    (by simp [finalHeaderRoles,finalHeaderPositions,s3,s1,w.injective.eq_iff,empty 19 (by decide)])
    (by simp [finalHeaderRoles,finalHeaderPositions,s3,s1,w.injective.eq_iff,empty 50 (by decide)])
  have combined := counting.sequence (clearing.sequence (reversing.sequence headers))
  refine ⟨15*width*m+19*m+18*width+22+1+(2+1+(2*stream.length+1+1+ht)),?_,?_⟩
  · dsimp only [formulaFinalizeCost];omega
  · simpa [formulaFinalize,finalHeaderRoles,finalHeaderPositions,s3,s1,List.append_assoc] using combined

end Counting.External.CNFMachine
