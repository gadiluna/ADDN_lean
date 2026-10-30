import Counting.ExternalMatchingGeneratorLayout

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def clausePart (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 33) (w 35) (w 59)))
    (generateClauseLoop (extra+16) w.literal)

def clausePartScratch : List (Fin 64) :=
  [2,3,4,5,6,9,10,11,12,13,14,18,19,21,24,26,27,28,34,35,37,38,39,40,41,42,43,44,45,46,47,59]
def clausePartCost (input n m width shift : Nat) :=
  5*shift+3+(m*(26000*(input+n+width+shift+4*m+2)^4+2)+1)
def clausePartResult (w : GeneratorWorkspace extra) (store : Fin (extra+64) → List Bool)
    (width shift : Nat) (clauses : List (List (Nat×Bool))) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 0) []) (w 23) []) (w 34) (List.replicate (3*clauses.length) true))
    (w 35) (List.replicate (shift+clauses.length) true))
    (w 36) ((Encoding.sequence (Encoding.list Encoding.natural) (clauseRows shift width shift 0 clauses)).reverse++store (w 36))

theorem clausePart_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (n width shift : Nat) (clauses : List (List (Nat×Bool))) (store : Fin (extra+64) → List Bool)
    (source : store (w 0)=Encoding.sequence (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) clauses)
    (status : store (w 1)=[true]) (count : store (w 23)=List.replicate clauses.length true)
    (nValue : (store (w 17)).length=n) (widthValue : store (w 32)=List.replicate width true)
    (shiftValue : store (w 33)=List.replicate shift true)
    (three : ∀ clause∈clauses,clause.length=3)
    (fits : ∀ clause∈clauses,∀ literal∈clause,literal.1≤n)
    (empty : ∀ i∈clausePartScratch,store (w i)=[]) :
    ∃ time ≤ clausePartCost (store (w 0)).length n clauses.length width shift,
      Executes (clausePart extra w) store time (clausePartResult w store width shift clauses) := by
  have copying := copy_executes (extra+61) (w 33) (w 35) (w 59)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 59 (by decide))
  rw [shiftValue,empty 35 (by decide),List.append_nil,List.length_replicate] at copying
  let ready := Function.update store (w 35) (List.replicate shift true)
  let bound := (store (w 0)).length+n+width+shift+4*clauses.length+1
  have readyEmpty (i : Fin 48) (member : i∈generateClauseScratch) : ready (w.literal i)=[] := by
    have mem : (⟨i.val,by omega⟩ : Fin 64)∈clausePartScratch := by
      fin_cases i <;> simp [generateClauseScratch,generateLiteralScratch,clausePartScratch] at member ⊢
    have different : (⟨i.val,by omega⟩ : Fin 64)≠35 := by
      intro same
      have val := congrArg Fin.val same
      have is35 : i=35 := Fin.ext val
      subst i
      simp [generateClauseScratch,generateLiteralScratch] at member
    simpa [ready,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,different] using empty _ mem
  obtain ⟨loopTime,loopBound,looping⟩ := generateClauseLoop_executes (extra+16) w.literal clauses n width shift bound shift 0 ready true [] []
    (by simp [ready,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,source])
    (by simp [ready,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,count])
    (by simp [ready,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,status])
    (by simpa [ready,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff] using nValue)
    (by simp [ready,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,widthValue])
    (by simp [ready,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,shiftValue])
    (by simp [ready,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,empty 34 (by decide)])
    (by simp [ready,GeneratorWorkspace.literal,literalPositions])
    (by simp [ready,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff];dsimp [bound];omega)
    (by dsimp [bound];omega) (by dsimp [bound];omega) (by dsimp [bound];omega)
    (by dsimp [bound];omega) (by dsimp [bound];omega) three fits readyEmpty
  have combined := copying.sequence looping
  refine ⟨5*shift+2+1+loopTime,?_,?_⟩
  · dsimp only [clausePartCost]
    dsimp only [bound] at loopBound
    simpa only [Nat.add_assoc,Nat.reduceAdd] using Nat.add_le_add_left loopBound (5*shift+3)
  · have final : clauseLoopResult (extra+16) w.literal ready shift width shift 0 clauses []=clausePartResult w store width shift clauses := by
      funext r
      by_cases is35 : r=w 35
      · subst r
        simp [clauseLoopResult,clausePartResult,ready,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,Nat.add_comm]
      · simp [clauseLoopResult,clausePartResult,ready,GeneratorWorkspace.literal,literalPositions,Function.update_apply,is35]
    simpa only [clausePart,final] using combined

end Counting.External.MatchingMachine
