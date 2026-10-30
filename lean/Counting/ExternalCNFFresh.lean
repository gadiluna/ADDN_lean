import Counting.StackEmitSyntax

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

abbrev FreshWorkspace (extra : Nat) := Fin 8 ↪ Fin (extra+8)

def freshPositions (target : Fin 4) : Fin 5 ↪ Fin 8 :=
  ⟨![![0,1,5,6,7],![0,2,5,6,7],![0,3,5,6,7],![0,4,5,6,7]] target,by
    intro i j same
    fin_cases target <;> fin_cases i <;> fin_cases j <;> simp_all⟩

def freshRoles (extra : Nat) (w : FreshWorkspace extra) (target : Fin 4) : PowerWorkspace (extra+3) :=
  (freshPositions target).trans w

/-- Emit the positive and negative current/next fresh literals, then retain
next as the current unary identifier. All four encoded output registers are
preserved as suffixes. -/
def freshPair (extra : Nat) (w : FreshWorkspace extra) : Routine (extra+6) :=
  sequence (emitLiteral (extra+3) (freshRoles extra w 0) true)
    (sequence (emitLiteral (extra+3) (freshRoles extra w 1) false)
      (sequence (pushBit (w 0) true)
        (sequence (emitLiteral (extra+3) (freshRoles extra w 2) true)
          (emitLiteral (extra+3) (freshRoles extra w 3) false))))

def freshResult (extra : Nat) (w : FreshWorkspace extra) (store : Fin (extra+8) → List Bool) :=
  let literal := Encoding.product Encoding.natural Encoding.boolean
  let index := (store (w 0)).length
  Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 1) (literal.encode (index,true)++store (w 1)))
    (w 2) (literal.encode (index,false)++store (w 2)))
    (w 0) (true::store (w 0)))
    (w 3) (literal.encode (index+1,true)++store (w 3)))
    (w 4) (literal.encode (index+1,false)++store (w 4))

theorem freshPair_executes (extra : Nat) (w : FreshWorkspace extra) (store : Fin (extra+8) → List Bool)
    (e5 : store (w 5)=[]) (e6 : store (w 6)=[]) (e7 : store (w 7)=[]) :
    ∃ time ≤ 100*((store (w 0)).length+2)^2,
      Executes (freshPair extra w) store time (freshResult extra w store) := by
  let codec := Encoding.product Encoding.natural Encoding.boolean
  let index := (store (w 0)).length
  obtain ⟨t0,b0,r0⟩ := emitLiteral_executes (extra+3) (freshRoles extra w 0) true store e5 e6 e7
  let s1 := Function.update store (w 1) (codec.encode (index,true)++store (w 1))
  change Executes (emitLiteral (extra+3) (freshRoles extra w 0) true) store t0 s1 at r0
  obtain ⟨t1,b1,r1⟩ := emitLiteral_executes (extra+3) (freshRoles extra w 1) false s1
    (by simp [freshRoles,freshPositions,s1,w.injective.eq_iff,e5])
    (by simp [freshRoles,freshPositions,s1,w.injective.eq_iff,e6])
    (by simp [freshRoles,freshPositions,s1,w.injective.eq_iff,e7])
  let s2 := Function.update s1 (w 2) (codec.encode (index,false)++store (w 2))
  have r1as : Executes (emitLiteral (extra+3) (freshRoles extra w 1) false) s1 t1 s2 := by
    simpa [freshRoles,freshPositions,s1,s2,w.injective.eq_iff,index,codec] using r1
  have advancing := pushBit_executes (w 0) true s2
  let s3 := Function.update s2 (w 0) (true::store (w 0))
  have advancingAs : Executes (pushBit (w 0) true) s2 1 s3 := by
    simpa [s3,s2,s1,w.injective.eq_iff] using advancing
  obtain ⟨t2,b2,r2⟩ := emitLiteral_executes (extra+3) (freshRoles extra w 2) true s3
    (by simp [freshRoles,freshPositions,s3,s2,s1,w.injective.eq_iff,e5])
    (by simp [freshRoles,freshPositions,s3,s2,s1,w.injective.eq_iff,e6])
    (by simp [freshRoles,freshPositions,s3,s2,s1,w.injective.eq_iff,e7])
  let s4 := Function.update s3 (w 3) (codec.encode (index+1,true)++store (w 3))
  have r2as : Executes (emitLiteral (extra+3) (freshRoles extra w 2) true) s3 t2 s4 := by
    simpa [freshRoles,freshPositions,s4,s3,s2,s1,w.injective.eq_iff,index,codec] using r2
  obtain ⟨t3,b3,r3⟩ := emitLiteral_executes (extra+3) (freshRoles extra w 3) false s4
    (by simp [freshRoles,freshPositions,s4,s3,s2,s1,w.injective.eq_iff,e5])
    (by simp [freshRoles,freshPositions,s4,s3,s2,s1,w.injective.eq_iff,e6])
    (by simp [freshRoles,freshPositions,s4,s3,s2,s1,w.injective.eq_iff,e7])
  have r3as : Executes (emitLiteral (extra+3) (freshRoles extra w 3) false) s4 t3 (freshResult extra w store) := by
    simpa [freshRoles,freshPositions,freshResult,s4,s3,s2,s1,w.injective.eq_iff,index,codec] using r3
  have combined := r0.sequence (r1as.sequence (advancingAs.sequence (r2as.sequence r3as)))
  refine ⟨t0+1+(t1+1+(1+1+(t2+1+t3))),?_,combined⟩
  change t0≤22*(index+1)^2 at b0
  have b1as : t1≤22*(index+1)^2 := by simpa [freshRoles,freshPositions,s1,w.injective.eq_iff,index] using b1
  have b2as : t2≤22*(index+2)^2 := by simpa [freshRoles,freshPositions,s3,s2,s1,w.injective.eq_iff,index,Nat.add_assoc] using b2
  have b3as : t3≤22*(index+2)^2 := by simpa [freshRoles,freshPositions,s4,s3,s2,s1,w.injective.eq_iff,index,Nat.add_assoc] using b3
  change _≤100*(index+2)^2
  have squares := Nat.pow_le_pow_left (by omega : index+1 ≤ index+2) 2
  have pos : 1≤(index+2)^2 := Nat.one_le_pow 2 _ (by omega)
  nlinarith only [b0,b1as,b2as,b3as,squares,pos]

end Counting.External.CNFMachine
