import Counting.StackEncodingListAppend

namespace Counting.StackMachine.EncodingPrograms
open Routine

theorem appendCanonicalBudget_polynomial {α : Type} (codec : Encoding.Codec α)
    (values : List α) (value : α) :
    appendCanonicalBudget codec values value ≤
      200*(values.length+((Encoding.list codec).encode values).length+(codec.encode value).length+1)^2 := by
  let N := values.length
  let L := ((Encoding.list codec).encode values).length
  let I := (codec.encode value).length
  let K := N+L+I+1
  have positive : 1 ≤ K := by omega
  have n : N ≤ K := by omega
  have l : L ≤ K := by omega
  have i : I ≤ K := by omega
  have n1 : N+1 ≤ K := by omega
  have n2 : N+2 ≤ 2*K := by omega
  have bits : N.bits.length ≤ K := by
    rw [Encoding.bits_length]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans n
  have nextBits : (N+1).bits.length ≤ K := by
    rw [Encoding.bits_length]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans n1
  have stream : (Encoding.sequence codec values).length ≤ L := by
    dsimp only [L]
    simp only [Encoding.list,List.length_append]
    omega
  have appended : Encoding.sequence codec (values++[value])=
      Encoding.sequence codec values++codec.encode value := sequence_append_one codec values value
  have output : ((Encoding.list codec).encode (values++[value])).length ≤ 4*K := by
    simp only [Encoding.list,List.length_append,List.length_cons,List.length_nil,Encoding.natural_length]
    rw [appended,List.length_append]
    rw [←Encoding.bits_length]
    change 2*(N+1).bits.length+1+((Encoding.sequence codec values).length+I) ≤ 4*K
    omega
  have multiplication := Nat.mul_le_mul n1 n2
  have square : K ≤ K^2 := Nat.le_self_pow (by decide) _
  change appendCanonicalBudget codec values value ≤ 200*K^2
  dsimp only [appendCanonicalBudget]
  change 4*(N+1)*(N+2)+5*N+5*L+6*N.bits.length+9*(N+1).bits.length+
    2*(Encoding.sequence codec values).length+7*I+
    2*((Encoding.list codec).encode (values++[value])).length+32 ≤ _
  nlinarith only [multiplication,n,l,i,bits,nextBits,stream,output,positive,square]

theorem appendCanonical_executes_polynomial {α : Type} (codec : Encoding.Codec α)
    (values : List α) (value : α) (store : Store 8)
    (source : store 0=(Encoding.list codec).encode values) (item : store 1=codec.encode value)
    (count : store 2=List.replicate values.length true)
    (empty : ∀ r : Fin 10,3 ≤ r.val → store r=[]) :
    ∃ time ≤ 200*((store 2).length+(store 0).length+(store 1).length+1)^2,
      Executes appendCanonical store time
        (Function.update store 3 ((Encoding.list codec).encode (values++[value]))) := by
  obtain ⟨time,bound,ran⟩ := appendCanonical_executes codec values value store source item count empty
  refine ⟨time,?_,ran⟩
  rw [source,item,count,List.length_replicate]
  exact bound.trans (appendCanonicalBudget_polynomial codec values value)

end Counting.StackMachine.EncodingPrograms
