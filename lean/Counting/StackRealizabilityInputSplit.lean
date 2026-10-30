import Counting.StackRealizabilityInputComponents

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def inputSplit : Routine 98 := sequence (readComponent DagParser.vista 99)
  (sequence (readComponent DagParser.naturals 81)
    (sequence (readNaturalPayload 96 70 98 0 85) (readNaturalPayload 96 70 82 0 85)))

def inputSplitStore (input status : List Bool) : Store 98 := fun r =>
  if r=70 then input else if r=85 then status else []

def inputFieldsStore (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (status : List Bool) : Store 98 := fun r =>
  if r=99 then Encoding.vista.encode vista else
  if r=81 then (Encoding.list Encoding.natural).encode values else
  if r=98 then ell.bits else if r=82 then order.bits else if r=85 then status else []

/-- Four actual serialized fields are extracted, with all scratch empty.
The caller's prior full-codec check supplies canonicality; this pass does
not convert population counts or indices to unary. -/
theorem inputSplit_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 6000*((Encoding.verifierInput.encode (vista,values,ell,order)).length+1)^4,
      Executes inputSplit (inputSplitStore (Encoding.verifierInput.encode (vista,values,ell,order)) (accepted::tail))
        time (inputFieldsStore vista values ell order (accepted::tail)) := by
  let whole := Encoding.verifierInput.encode (vista,values,ell,order)
  let rest := (Encoding.list Encoding.natural).encode values++
    (Encoding.natural.encode ell++Encoding.natural.encode order)
  let numbers := Encoding.natural.encode ell++Encoding.natural.encode order
  let start := inputSplitStore whole (accepted::tail)
  have input : start 70=Encoding.vista.encode vista++rest := rfl
  obtain ⟨t0,b0,r0⟩ := readComponent_executes DagParser.vista (99:Fin 100)
    (by decide) (by decide) start vista rest accepted tail input
    (by simp [start,inputSplitStore]) (by simp [start,inputSplitStore])
    (by simp [start,inputSplitStore]) (by
      intro i a b c;fin_cases i <;> simp_all [start,inputSplitStore,componentRoles])
  let s1 := Function.update (Function.update start 70 rest) 99 (Encoding.vista.encode vista)
  obtain ⟨t1,b1,r1⟩ := readComponent_executes DagParser.naturals (81:Fin 100)
    (by decide) (by decide) s1 values numbers accepted tail (by simp [s1,rest,numbers])
    (by simp [s1,start,inputSplitStore]) (by simp [s1,start,inputSplitStore])
    (by simp [s1,start,inputSplitStore]) (by
      intro i a b c;fin_cases i <;> simp_all [s1,start,inputSplitStore,componentRoles])
  let s2 := Function.update (Function.update s1 70 numbers) 81 ((Encoding.list Encoding.natural).encode values)
  obtain ⟨t2,b2,r2⟩ := readNaturalPayload_executes 96 (70:Fin 100) 98 0 85
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    s2 ell (Encoding.natural.encode order) accepted tail
    (by simp [s2,numbers]) (by simp [s2,s1,start,inputSplitStore])
    (by simp [s2,s1,start,inputSplitStore]) (by simp [s2,s1,start,inputSplitStore])
  let s3 := Function.update (Function.update s2 70 (Encoding.natural.encode order)) 98 ell.bits
  obtain ⟨t3,b3,r3⟩ := readNaturalPayload_executes 96 (70:Fin 100) 82 0 85
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    s3 order [] accepted tail (by simp [s3]) (by simp [s3,s2,s1,start,inputSplitStore])
    (by simp [s3,s2,s1,start,inputSplitStore]) (by simp [s3,s2,s1,start,inputSplitStore])
  have final : Function.update (Function.update s3 70 []) 82 order.bits=
      inputFieldsStore vista values ell order (accepted::tail) := by
    funext r
    by_cases a:r=70 <;> by_cases b:r=99 <;> by_cases c:r=81 <;>
      by_cases d:r=98 <;> by_cases e:r=82 <;> by_cases f:r=85 <;>
      simp_all [s3,s2,s1,start,inputSplitStore,inputFieldsStore]
  rw [final] at r3
  change t0 ≤ 3890*(whole.length+1)^4+2*(Encoding.vista.encode vista).length+2 at b0
  change t1 ≤ 1860*(rest.length+1)^3+2*((Encoding.list Encoding.natural).encode values).length+2 at b1
  change t2 ≤ 3*numbers.length+8 at b2
  change t3 ≤ 3*(Encoding.natural.encode order).length+8 at b3
  have split : whole.length=(Encoding.vista.encode vista).length+
      ((Encoding.list Encoding.natural).encode values).length+
      (Encoding.natural.encode ell).length+(Encoding.natural.encode order).length := by
    simp [whole,Encoding.verifierInput,Encoding.product,List.length_append,Nat.add_assoc]
  have restLength : rest.length ≤ whole.length := by
    simp only [rest,List.length_append];omega
  have numbersLength : numbers.length ≤ whole.length := by
    simp only [numbers,List.length_append];omega
  have cube : (rest.length+1)^3 ≤ (whole.length+1)^4 :=
    (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have second := b1.trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 1860 cube) _) _)
  have linear : whole.length+1 ≤ (whole.length+1)^4 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ (whole.length+1)^4 := Nat.one_le_pow _ _ (by omega)
  exact ⟨_,by change t0+1+(t1+1+(t2+1+t3)) ≤ 6000*(whole.length+1)^4;omega,
    r0.sequence (r1.sequence (r2.sequence r3))⟩

end Counting.StackMachine.RealizabilityCheck
