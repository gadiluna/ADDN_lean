import Counting.StackEncodingParser

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def productEffect (first second : List Bool → ParseEffect) (input : List Bool) : ParseEffect :=
  let a:=first input
  let b:=second a.suffix
  ⟨b.suffix,a.code++b.code,a.accepted && b.accepted⟩

theorem parseStore_product {registers : Nat} (source status output : Fin (registers+2))
    (ss : source≠status) (so : source≠output) (statusOutput : status≠output)
    (store : Routine.Store registers) (accepted : Bool) (tail : List Bool) (first second : ParseEffect) :
    parseStore source status output (parseStore source status output store accepted tail first)
      (accepted && first.accepted) tail second =
    parseStore source status output store accepted tail
      ⟨second.suffix,first.code++second.code,first.accepted && second.accepted⟩ := by
  funext r
  by_cases a : r=source
  · subst r; simp [parseStore]
  · by_cases b : r=status
    · subst r; simp [parseStore,Ne.symm ss,Bool.and_assoc]
    · by_cases c : r=output
      · subst r; simp [parseStore,Ne.symm so,Ne.symm statusOutput,List.reverse_append,List.append_assoc]
      · simp [parseStore,a,b,c]

theorem polynomial_pair_bound (a b p q n m : Nat) (bounded : m≤n) :
    Complexity.polynomial a p n+1+Complexity.polynomial b q m ≤
      Complexity.polynomial (a+b+1) (max p q) n := by
  have first : (n+1)^p ≤ (n+1)^(max p q) := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have second : (m+1)^q ≤ (n+1)^(max p q) := by
    calc
      _≤(n+1)^q := by gcongr
      _≤_ := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have positive : 1≤(n+1)^(max p q) := Nat.one_le_pow _ _ (by omega)
  unfold Complexity.polynomial
  nlinarith [Nat.mul_le_mul_left a first,Nat.mul_le_mul_left b second]

namespace VerifiedParser

/-- Sequential composition is a concrete jump between the two routines.
Scratch may overlap because both routines restore it before returning. -/
def product {registers : Nat} {source status output : Fin (registers+2)}
    (ss : source≠status) (so : source≠output) (statusOutput : status≠output)
    {α β : Type} {a : Encoding.Codec α} {b : Encoding.Codec β}
    (first : VerifiedParser registers source status output α a)
    (second : VerifiedParser registers source status output β b) :
    VerifiedParser registers source status output (α×β) (Encoding.product a b) where
  work := first.work ∪ second.work
  separate r member := by
    rcases Finset.mem_union.mp member with member | member
    · exact first.separate r member
    · exact second.separate r member
  routine := Routine.sequence first.routine second.routine
  effect := productEffect first.effect second.effect
  coefficient := first.coefficient+second.coefficient+1
  exponent := max first.exponent second.exponent
  suffix_le input := (second.suffix_le _).trans (first.suffix_le input)
  code_le input := by
    have firstBound:=first.code_le input
    have secondBound:=second.code_le (first.effect input).suffix
    have total:=polynomial_pair_bound first.coefficient second.coefficient first.exponent second.exponent
      input.length (first.effect input).suffix.length (first.suffix_le input)
    simp only [productEffect,List.length_append]
    omega
  sound input accepted := by
    have both : (first.effect input).accepted=true ∧ (second.effect (first.effect input).suffix).accepted=true := by
      simpa only [productEffect,Bool.and_eq_true] using accepted
    obtain ⟨va,splitA,codeA⟩:=first.sound input both.1
    obtain ⟨vb,splitB,codeB⟩:=second.sound (first.effect input).suffix both.2
    refine ⟨(va,vb),?_,?_⟩
    · change (a.encode va++b.encode vb)++_=input
      rw [List.append_assoc,productEffect,splitB,splitA]
    · change (first.effect input).code++(second.effect (first.effect input).suffix).code=_
      rw [codeA,codeB]
      rfl
  roundtrip value suffix := by
    obtain ⟨va,vb⟩:=value
    change productEffect first.effect second.effect ((a.encode va++b.encode vb)++suffix)=_
    rw [List.append_assoc]
    simp only [productEffect,first.roundtrip,second.roundtrip,Bool.true_and]
    rfl
  executes store accepted tail statusEq workEmpty := by
    have firstEmpty r member : store r=[] := workEmpty r (Finset.mem_union_left _ member)
    obtain ⟨firstTime,firstBound,firstRun⟩:=first.executes store accepted tail statusEq firstEmpty
    let middle := parseStore source status output store accepted tail (first.effect (store source))
    have nextStatus : middle status=(accepted && (first.effect (store source)).accepted)::tail := by
      simp [middle,parseStore,Ne.symm ss]
    have nextSource : middle source=(first.effect (store source)).suffix := by simp [middle,parseStore]
    have secondEmpty (r : Fin (registers+2)) (member : r∈second.work) : middle r=[] := by
      obtain ⟨r0,r1,r2⟩:=second.separate r member
      simp only [middle,parseStore,if_neg r0,if_neg r1,if_neg r2]
      exact workEmpty r (Finset.mem_union_right _ member)
    obtain ⟨secondTime,secondBound,secondRun⟩:=second.executes middle
      (accepted && (first.effect (store source)).accepted) tail nextStatus secondEmpty
    rw [nextSource] at secondRun secondBound
    have composed:=firstRun.sequence secondRun
    change Routine.Executes _ _ _ (parseStore source status output
      (parseStore source status output store accepted tail (first.effect (store source)))
      (accepted && (first.effect (store source)).accepted) tail (second.effect (first.effect (store source)).suffix)) at composed
    rw [parseStore_product source status output ss so statusOutput] at composed
    refine ⟨firstTime+1+secondTime,?_,composed⟩
    have total:=polynomial_pair_bound first.coefficient second.coefficient first.exponent second.exponent
      (store source).length (first.effect (store source)).suffix.length (first.suffix_le _)
    omega

end VerifiedParser
end Counting.StackMachine.EncodingPrograms
