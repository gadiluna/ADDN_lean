import Counting.ExternalCNFMeasureHeader

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false

def measureClause (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (measureHeader extra w) (clauseRoutine extra w)

theorem measureClause_executes (extra : Nat) (w : SATWorkspace extra)
    (literals : List (Nat×Bool)) (bits suffix tail valueTail : List Bool)
    (store : Fin (extra+32) → List Bool) (accepted value : Bool)
    (source : store (w 0)=(Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode literals++suffix)
    (witness : store (w 17)=bits) (status : store (w 1)=accepted::tail)
    (formula : store (w 27)=value::valueTail)
    (empty : ∀ i∈clauseScratch++[30],store (w i)=[]) :
    ∃ time ≤ 4100*((store (w 0)).length+bits.length+1)^4,
      Executes (measureClause extra w) store time
        (Function.update (Function.update (Function.update (Function.update store (w 31)
          (List.replicate literals.length true++store (w 31))) (w 0) suffix)
          (w 1) ((accepted && clauseRange bits literals)::tail))
          (w 27) ((value && clauseValue bits literals)::valueTail)) := by
  have positive (literal : Nat×Bool) : 0<((Encoding.product Encoding.natural Encoding.boolean).encode literal).length := by
    simp [Encoding.product,Encoding.boolean]
  obtain ⟨measureTime,measureBound,measureRun⟩ := measureHeader_executes extra w
    (Encoding.product Encoding.natural Encoding.boolean) positive literals suffix store accepted tail source status empty
  let measured := Function.update store (w 31) (List.replicate literals.length true++store (w 31))
  have scratch (i : Fin 32) (member : i∈clauseScratch) : measured (w i)=[] := by
    have different : i≠31 := by intro same;subst i;simp [clauseScratch] at member
    simpa [measured,w.injective.eq_iff,different] using empty i (by simp [member])
  obtain ⟨clauseTime,clauseBound,clauseRun⟩ := clauseRoutine_executes extra w literals bits suffix tail valueTail measured accepted value
    (by simp [measured,w.injective.eq_iff,source]) (by simp [measured,w.injective.eq_iff,witness])
    (by simp [measured,w.injective.eq_iff,status]) (by simp [measured,w.injective.eq_iff,formula]) scratch
  have combined := measureRun.sequence clauseRun
  refine ⟨measureTime+1+clauseTime,?_,combined⟩
  have measuredInput : measured (w 0)=store (w 0) := by simp [measured,w.injective.eq_iff]
  rw [measuredInput] at clauseBound
  let S := (store (w 0)).length+bits.length+1
  have positiveS : 1≤S := by dsimp [S];omega
  have powers : ((store (w 0)).length+1)^3≤S^4 :=
    (Nat.pow_le_pow_left (by dsimp [S];omega) 3).trans (Nat.pow_le_pow_right positiveS (by decide))
  have measuredBound := measureBound.trans (Nat.mul_le_mul_left 1900 powers)
  change clauseTime≤2100*S^4 at clauseBound
  change _≤4100*S^4
  nlinarith only [measuredBound,clauseBound,show 1≤S^4 from Nat.one_le_pow _ _ positiveS]

end Counting.External.CNFMachine
