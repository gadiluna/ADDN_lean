import Counting.ExternalCoverNaturalRead

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def readCoverIndex (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (readNatural extra w)
    (sequence (readIndex (extra+19) (literalIndexRoles extra w)) (clear (w 18)))

def coverIndexScratch : List (Fin 32) := [2,3,4,5,6,9,10,11,12,18,19,26,28]

theorem readCoverIndex_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (index : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.natural.encode index++suffix)
    (status : store (w 1)=accepted::tail) (fits : index ≤ (store (w 17)).length)
    (empty : ∀ i∈coverIndexScratch,store (w i)=[]) :
    ∃ time ≤ 200*((store (w 0)).length+(store (w 17)).length+1)^3,
      Executes (readCoverIndex extra w) store time
        (Function.update (Function.update store (w 0) suffix)
          (w 26) (List.replicate index true)) := by
  obtain ⟨readTime,readBound,reading⟩ := readNatural_executes extra w store index accepted suffix tail source status
    (fun i mem=>empty i (by simp only [coverIndexScratch,List.mem_cons,List.not_mem_nil] at mem ⊢;tauto))
  let code := Encoding.natural.encode index
  let read := Function.update (Function.update store (w 0) suffix) (w 18) code
  have indexEmpty (i : Fin 13) (member : i∈([2,3,4,5,6,7,8,9,10,11] : List (Fin 13))) :
      read (literalIndexRoles extra w i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h
    all_goals first | contradiction | simp [literalIndexRoles,literalIndexPositions,read,w.injective.eq_iff,empty,coverIndexScratch]
  obtain ⟨indexTime,indexBound,indexRun⟩ := readIndex_executes (extra+19) (literalIndexRoles extra w) read index
    (by simp [literalIndexRoles,literalIndexPositions,read,code])
    (by simpa [literalIndexRoles,literalIndexPositions,read,w.injective.eq_iff] using fits) indexEmpty
  let counted := Function.update read (w 26) (List.replicate index true)
  have countRun : Executes (readIndex (extra+19) (literalIndexRoles extra w)) read indexTime counted := indexRun
  have clearing := clear_executes (w 18) counted
  have codeEq : counted (w 18)=code := by simp [counted,read,w.injective.eq_iff]
  rw [codeEq] at clearing
  have final : Function.update counted (w 18) []=
      Function.update (Function.update store (w 0) suffix) (w 26) (List.replicate index true) := by
    funext r
    by_cases e18 : r=w 18
    · subst r;simp [w.injective.eq_iff,empty,coverIndexScratch]
    · by_cases e26 : r=w 26
      · subst r;simp [counted,w.injective.eq_iff]
      · simp [counted,read,e18,e26,Function.update_apply]
  rw [final] at clearing
  have composed := reading.sequence (countRun.sequence clearing)
  refine ⟨readTime+1+(indexTime+1+(code.length+1)),?_,composed⟩
  have codeBound : code.length ≤ (store (w 0)).length := by
    rw [source]
    simp only [List.length_append]
    dsimp [code]
    omega
  have countedBound : indexTime ≤ 100*((store (w 0)).length+(store (w 17)).length+1)^3 := by
    apply indexBound.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simpa [literalIndexRoles,literalIndexPositions,read,w.injective.eq_iff] using Nat.add_le_add_right
      (Nat.add_le_add_right codeBound (store (w 17)).length) 1
  have linear : (store (w 0)).length+(store (w 17)).length+1 ≤
      ((store (w 0)).length+(store (w 17)).length+1)^3 := Nat.le_self_pow (by decide) _
  omega

end Counting.External.CoverMachine
