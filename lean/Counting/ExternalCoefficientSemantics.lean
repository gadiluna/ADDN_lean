import Counting.ExternalCoefficientTriple
import Counting.X3CSize
import Counting.X3CEncoding

namespace Counting.External.CoefficientMachine

theorem powers_tripleRaw {q : Nat} (triple : X3CEncoding.Triple q) :
    powers (X3C.base q) (X3CEncoding.tripleRaw triple)=∑ e∈triple.val,X3C.base q^e.val := by
  unfold powers X3CEncoding.tripleRaw
  rw [List.map_map]
  change (Multiset.map (fun e : Fin (3*q)=>X3C.base q^e.val) (↑(triple.val.sort (· ≤ ·)) : Multiset (Fin (3*q)))).sum=_
  rw [Finset.sort_eq]
  rfl

theorem powers_instance_triple {q m : Nat} (instanceData : X3C.Instance q m) (j : Fin m) :
    powers (X3C.base q) (X3CEncoding.tripleRaw ⟨instanceData.triples j,instanceData.triple_card j⟩)=instanceData.tripleValue j :=
  powers_tripleRaw _

open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

theorem coefficientTriple_instance_executes {q m : Nat} (instanceData : X3C.Instance q m)
    (large : 2 ≤ q) (j : Fin m) (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+64) → List Bool) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode
      (X3CEncoding.tripleRaw ⟨instanceData.triples j,instanceData.triple_card j⟩)++suffix)
    (status : store (w 1)=accepted::tail) (universeSize : (store (w 17)).length=3*q)
    (baseInput : store (w 52)=(X3C.base q).bits) (highInput : store (w 54)=(X3C.high q).bits)
    (empty : ∀ i∈tripleScratch,store (w i)=[]) :
    ∃ time ≤ tripleCost (store (w 0)).length (3*q) (X3C.base q).bits.length (X3C.high q).bits.length
        ((3*q+1)*(X3C.base q).size),
      Executes (coefficientTriple extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 55) (instanceData.coefficient (some j)).bits) := by
  let triple : X3CEncoding.Triple q := ⟨instanceData.triples j,instanceData.triple_card j⟩
  have length : (X3CEncoding.tripleRaw triple).length=3 := by simp [X3CEncoding.tripleRaw,triple,instanceData.triple_card]
  obtain ⟨a,b,c,row⟩:=List.length_eq_three.mp length
  have value : X3C.high q+powers (X3C.base q) [a,b,c]=instanceData.coefficient (some j) := by
    rw [←row,powers_instance_triple]
    rfl
  have fits : ∀ e∈[a,b,c],e ≤ (store (w 17)).length := by
    intro e member
    rw [←row] at member
    obtain ⟨element,_membership,rfl⟩:=List.mem_map.mp member
    rw [universeSize]
    exact element.isLt.le
  obtain ⟨time,bound,ran⟩:=coefficientTriple_executes extra w store (X3C.base q) (X3C.high q) a b c
    ((3*q+1)*(X3C.base q).size) accepted suffix tail (by
      change store (w 0)=(Encoding.list Encoding.natural).encode (X3CEncoding.tripleRaw triple)++suffix at source
      rwa [row] at source) status baseInput highInput
    (by rw [value,Encoding.bits_length];exact instanceData.coefficient_size large (some j)) fits empty
  rw [value] at ran
  rw [universeSize] at bound
  exact ⟨time,bound,ran⟩

end Counting.External.CoefficientMachine
