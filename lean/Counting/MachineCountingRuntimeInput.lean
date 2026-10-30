import Counting.CountingSizeEncoding
import Counting.ProtocolStateEncoding
import Counting.ExecutableRefinementPhysical

namespace Counting.StackMachine.ProtocolAdvance
open Executable
open scoped BigOperators
set_option maxHeartbeats 2400000

/-- A uniform population-and-label bound at every live counting round. -/
theorem vistaBudget_horizon (n depth bits : Nat) (horizon : depth ≤ 2*n) :
    ((depth+1)*n)*(8*(depth+(depth+1)*n+bits+n+1)+9+
      n*(4*(depth+(depth+1)*n+bits+n+1)+2))+2 ≤ 400*(n+bits+1)^5 := by
  let N := n+bits+1
  have positive : 1 ≤ N := by dsimp [N];omega
  have pop : n ≤ N := by dsimp [N];omega
  have labels : bits ≤ N := by dsimp [N];omega
  have time : depth ≤ 2*N := by omega
  have linear2 : N ≤ N^2 := Nat.le_self_pow (by decide) _
  have one2 : 1 ≤ N^2 := one_le_pow₀ positive
  have count : (depth+1)*n ≤ 3*N^2 := by
    have a : depth+1 ≤ 3*N := by omega
    have product := Nat.mul_le_mul a pop
    nlinarith only [product]
  have fields : depth+(depth+1)*n+bits+n+1 ≤ 8*N^2 := by omega
  have factor : 4*(depth+(depth+1)*n+bits+n+1)+2 ≤ 34*N^2 := by omega
  have scale := Nat.mul_le_mul pop factor
  have scale' : n*(4*(depth+(depth+1)*n+bits+n+1)+2) ≤ 34*N^3 := by
    convert scale using 1; ring
  have two3 : N^2 ≤ N^3 := Nat.pow_le_pow_right positive (by decide)
  have one3 : 1 ≤ N^3 := one_le_pow₀ positive
  have inner : 8*(depth+(depth+1)*n+bits+n+1)+9+
      n*(4*(depth+(depth+1)*n+bits+n+1)+2) ≤ 107*N^3 := by omega
  have total := Nat.mul_le_mul count inner
  have total' : ((depth+1)*n)*(8*(depth+(depth+1)*n+bits+n+1)+9+
      n*(4*(depth+(depth+1)*n+bits+n+1)+2)) ≤ 321*N^5 := by
    convert total using 1; ring
  have one5 : 1 ≤ N^5 := one_le_pow₀ positive
  change _ ≤ 400*N^5
  omega

theorem physical_vista_horizon {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth M : Nat)
    (states : V → LocalState)
    (represented : ∀ x,StateRep ell depth (Counting.history G leader depth x) (states x))
    (horizon : depth ≤ 2*Fintype.card V)
    (mass : ∀ r,0 < r → r ≤ depth → arcMass G r ≤ M) (observer : V) :
    (Encoding.vista.encode (states observer).vista).length ≤ 400*(Fintype.card V+M.size+1)^5 := by
  have size := Encoding.physical_vista_encoding_length G leader depth observer (states observer).vista
    (represented observer).valid (represented observer).level (represented observer).history M mass
  exact size.trans (vistaBudget_horizon _ _ _ horizon)

theorem physicalBundles_length_le {V : Type} [Fintype V] (edge : V → V → Nat)
    (views : V → Vista) (receiver : V) :
    (physicalBundles edge views receiver).length ≤ Fintype.card V := by
  unfold physicalBundles senderBundles
  exact (List.length_filterMap_le _ _).trans_eq (by simp)

theorem bundle_count_le_arcMass {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (round : Nat) (sender receiver : V) :
    G round sender receiver ≤ arcMass G round := by
  have one : G round sender receiver ≤ ∑ other,G round sender other :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ receiver)
  exact one.trans (outgoing_le_arcMass G round sender)

/-- One encoded message per physical sender, with multiplicity kept binary. -/
theorem physical_messages_horizon {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth M : Nat)
    (states : V → LocalState)
    (represented : ∀ x,StateRep ell depth (Counting.history G leader depth x) (states x))
    (horizon : depth ≤ 2*Fintype.card V)
    (mass : ∀ r,0 < r → r ≤ depth+1 → arcMass G r ≤ M) (receiver : V) :
    (messagesCodec.encode (physicalBundles (G (depth+1)) (fun x=>(states x).vista) receiver)).length ≤
      406*(Fintype.card V+M.size+1)^6 := by
  let N := Fintype.card V+M.size+1
  let messages := physicalBundles (G (depth+1)) (fun x=>(states x).vista) receiver
  have positive : 1 ≤ N := by dsimp [N];omega
  have nBound : Fintype.card V ≤ N := by dsimp [N];omega
  have bitsBound : M.size ≤ N := by dsimp [N];omega
  have count : messages.length ≤ N := (physicalBundles_length_le _ _ _).trans nBound
  have countBits : messages.length.size ≤ N := (Nat.size_le.mpr Nat.lt_two_pow_self).trans count
  have linear : N ≤ N^5 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ N^5 := one_le_pow₀ positive
  have each (message : Vista×Nat) (member : message∈messages) :
      ((Encoding.product Encoding.vista Encoding.natural).encode message).length ≤ 403*N^5 := by
    obtain ⟨sender,_,_,same⟩ := mem_senderBundles _ _ _ _ message member
    subst message
    have view := physical_vista_horizon G leader ell depth M states represented horizon
      (fun r pos within=>mass r pos (by omega)) sender
    have countBound := (bundle_count_le_arcMass G (depth+1) sender receiver).trans
      (mass (depth+1) (by omega) le_rfl)
    have size := Nat.size_le_size countBound
    simp only [Encoding.product,List.length_append,Encoding.natural_length]
    change (Encoding.vista.encode (states sender).vista).length ≤ 400*N^5 at view
    omega
  have payload := List.sum_le_sum (l:=messages)
    (f:=fun message=>((Encoding.product Encoding.vista Encoding.natural).encode message).length)
    (g:=fun _=>403*N^5) each
  simp only [List.map_const',List.sum_replicate,smul_eq_mul] at payload
  have scaled := Nat.mul_le_mul_right (403*N^5) count
  have power : N*(403*N^5)=403*N^6 := by ring
  rw [power] at scaled
  have linear6 : N ≤ N^6 := Nat.le_self_pow (by decide) _
  have one6 : 1 ≤ N^6 := one_le_pow₀ positive
  change ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode messages).length ≤ 406*N^6
  rw [Encoding.list_length]
  omega

/-- The real local input, including framing, leader count, own vista,
compact incoming bundles and learned outdegree, has polynomial bit length. -/
theorem physical_inputWord_horizon {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth M : Nat)
    (states : V → LocalState)
    (represented : ∀ x,StateRep ell depth (Counting.history G leader depth x) (states x))
    (receiver : V) (active : (states receiver).output=none)
    (leaderBound : ell ≤ Fintype.card V) (horizon : depth ≤ 2*Fintype.card V)
    (mass : ∀ r,0 < r → r ≤ depth+1 → arcMass G r ≤ M) :
    (inputWord (states receiver)
      (physicalBundles (G (depth+1)) (fun x=>(states x).vista) receiver)
      (∑ sender,G (depth+1) receiver sender)).length+1 ≤
      4000*(Fintype.card V+M.size+1)^6 := by
  let N := Fintype.card V+M.size+1
  have positive : 1 ≤ N := by dsimp [N];omega
  have nBound : Fintype.card V ≤ N := by dsimp [N];omega
  have bitsBound : M.size ≤ N := by dsimp [N];omega
  have view := physical_vista_horizon G leader ell depth M states represented horizon
    (fun r pos within=>mass r pos (by omega)) receiver
  have messages := physical_messages_horizon G leader ell depth M states represented horizon mass receiver
  have degree := Nat.size_le_size ((outgoing_le_arcMass G (depth+1) receiver).trans (mass (depth+1) (by omega) le_rfl))
  have leaders : (states receiver).leaders.size ≤ N := by
    rw [(represented receiver).leaderCount]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (leaderBound.trans nBound)
  have linear : N ≤ N^6 := Nat.le_self_pow (by decide) _
  have p5 : N^5 ≤ N^6 := Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ N^6 := one_le_pow₀ positive
  rw [inputWord_fields,active]
  simp only [List.length_append,Encoding.frame_length,Encoding.natural_length,Encoding.optional,
    List.length_singleton]
  change (Encoding.vista.encode (states receiver).vista).length ≤ 400*N^5 at view
  change (messagesCodec.encode _).length ≤ 406*N^6 at messages
  change _ ≤ 4000*N^6
  have lifted := view.trans (Nat.mul_le_mul_left 400 p5)
  omega

end Counting.StackMachine.ProtocolAdvance
