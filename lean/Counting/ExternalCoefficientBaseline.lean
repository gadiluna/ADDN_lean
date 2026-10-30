import Counting.ExternalCoefficientGeometricLoop
import Counting.ExternalCoefficientProduct
import Counting.X3CSize

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def baselineScratch : List (Fin 64) := productScratch++geometricScratch++[37,42]

def prepareBaseline (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (prepareProduct extra w)
    (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 17) (w 42) (w 20)))
      (sequence (geometricLoop extra w) (clear (w 37))))

def baselineCost (q universeLength baseLength highLength sumLimit : Nat) :=
  100000*(q+highLength+1)^3+1+(5*universeLength+2+1+
    (universeLength*(geometricStepCost baseLength sumLimit universeLength+2)+1+1+(universeLength+1)))

theorem prepareBaseline_executes (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+64) → List Bool) (q universeLength base high sumLimit : Nat)
    (qCounter : store (w 27)=List.replicate q true)
    (universeCounter : store (w 17)=List.replicate universeLength true)
    (baseInput : store (w 52)=base.bits) (highInput : store (w 54)=high.bits)
    (sumSize : (q*high+geometric base 0 universeLength).bits.length ≤ sumLimit)
    (empty : ∀ i∈baselineScratch,store (w i)=[]) :
    ∃ time ≤ baselineCost q universeLength base.bits.length high.bits.length sumLimit,
      Executes (prepareBaseline extra w) store time
        (Function.update store (w 55) (q*high+geometric base 0 universeLength).bits) := by
  obtain ⟨productTime,productBound,productRun⟩:=prepareProduct_executes extra w store q qCounter
    (fun i member=>empty i (by simp only [baselineScratch,List.mem_append];exact Or.inl (Or.inl member)))
  rw [highInput,Encoding.value_bits] at productRun
  rw [highInput] at productBound
  let productStore:=Function.update store (w 55) (q*high).bits
  have copyRun:=copy_executes (extra+61) (w 17) (w 42) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) productStore
    (by simp [productStore,w.injective.eq_iff,empty,baselineScratch,productScratch])
  have universeAt : productStore (w 17)=List.replicate universeLength true := by
    simpa [productStore,w.injective.eq_iff] using universeCounter
  have counterAt : productStore (w 42)=[] := by simp [productStore,w.injective.eq_iff,empty,baselineScratch]
  rw [universeAt,counterAt,List.append_nil,List.length_replicate] at copyRun
  let copied:=Function.update productStore (w 42) (List.replicate universeLength true)
  have copiedEmpty (i : Fin 64) (member : i∈geometricScratch) : copied (w i)=[] := by
    have n42 : i≠42 := by intro same;subst i;simp [geometricScratch] at member
    have n55 : i≠55 := by intro same;subst i;simp [geometricScratch] at member
    simpa [copied,productStore,w.injective.eq_iff,n42,n55] using
      empty i (by simp only [baselineScratch,List.mem_append];exact Or.inl (Or.inr member))
  obtain ⟨loopTime,loopBound,loopRun⟩:=geometricLoop_executes extra w universeLength universeLength base sumLimit copied 0 (q*high)
    (by simp [copied,productStore,w.injective.eq_iff,baseInput])
    (by simp [copied,productStore,w.injective.eq_iff])
    (by simp [copied,productStore,w.injective.eq_iff,empty,baselineScratch])
    (by simp [copied]) (by omega) sumSize copiedEmpty
  let loopStore:=Function.update (Function.update store (w 37) (List.replicate universeLength true))
    (w 55) (q*high+geometric base 0 universeLength).bits
  have loopFinal : Function.update (Function.update (Function.update copied (w 42) []) (w 37)
      (List.replicate universeLength true++copied (w 37))) (w 55)
      (q*high+geometric base 0 universeLength).bits=loopStore := by
    funext r
    by_cases e42 : r=w 42
    · subst r;simp [loopStore,w.injective.eq_iff,empty,baselineScratch]
    · by_cases e37 : r=w 37
      · subst r;simp [loopStore,copied,productStore,w.injective.eq_iff,empty,baselineScratch]
      · by_cases e55 : r=w 55
        · subst r;simp [loopStore]
        · simp [loopStore,copied,productStore,e42,e37,e55]
  rw [loopFinal] at loopRun
  have clearing:=clear_executes (w 37) loopStore
  have indexAt : loopStore (w 37)=List.replicate universeLength true := by simp [loopStore,w.injective.eq_iff]
  rw [indexAt,List.length_replicate] at clearing
  have final : Function.update loopStore (w 37) []=
      Function.update store (w 55) (q*high+geometric base 0 universeLength).bits := by
    funext r
    by_cases e37 : r=w 37
    · subst r;simp [w.injective.eq_iff,empty,baselineScratch]
    · simp [loopStore,Function.update_apply,e37]
  rw [final] at clearing
  refine ⟨productTime+1+(5*universeLength+2+1+(loopTime+1+(universeLength+1))),?_,
    productRun.sequence (copyRun.sequence (loopRun.sequence clearing))⟩
  unfold baselineCost
  omega

theorem prepareBaseline_target_executes (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+64) → List Bool) (q : Nat)
    (qCounter : store (w 27)=List.replicate q true)
    (universeCounter : store (w 17)=List.replicate (3*q) true)
    (baseInput : store (w 52)=(X3C.base q).bits) (highInput : store (w 54)=(X3C.high q).bits)
    (empty : ∀ i∈baselineScratch,store (w i)=[]) :
    ∃ time ≤ baselineCost q (3*q) (X3C.base q).bits.length (X3C.high q).bits.length ((3*q+1)*(X3C.base q).size),
      Executes (prepareBaseline extra w) store time (Function.update store (w 55) (X3C.target q).bits) := by
  have target : q*X3C.high q+geometric (X3C.base q) 0 (3*q)=X3C.target q := by
    rw [geometric_ones];rfl
  have bound : (q*X3C.high q+geometric (X3C.base q) 0 (3*q)).bits.length ≤ (3*q+1)*(X3C.base q).size := by
    rw [target,Encoding.bits_length]
    exact X3C.size_le_power_width _ _ _ (X3C.target_lt_base_power q)
  simpa only [target] using prepareBaseline_executes extra w store q (3*q) (X3C.base q) (X3C.high q)
    ((3*q+1)*(X3C.base q).size) qCounter universeCounter baseInput highInput bound empty

end Counting.External.CoefficientMachine
