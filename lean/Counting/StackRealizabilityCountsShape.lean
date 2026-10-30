import Counting.StackRealizabilityCountsPrefix
import Counting.StackDagGuards

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def countsRoles : Fin 21 ↪ Fin 22 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b same;apply Fin.ext;exact congrArg (fun r:Fin 22=>r.val) same

def countsLengthRoles : Fin 6 ↪ Fin 22:=⟨![0,21,1,2,3,4],by decide⟩

def countsShape : Routine 20:=sequence (mapRegisters countsRoles countsPrefix)
  (DagValidation.equalityGuard 16 countsLengthRoles)

def countsShapeStore (store : Store 20) (accepted : Bool) (tail suffix : List Bool)
    (total expected : Nat) (values : List Nat) : Store 20:=
  Function.update (Function.update (Function.update (Function.update store 17 suffix)
    0 (List.replicate values.length true)) 19 (total+values.sum).bits)
      1 (((accepted && positiveCounts values) && decide (values.length=expected))::tail)

theorem countsShape_executes (store : Store 20) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 22,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e20 : store 20=[])
    (total expected : Nat) (accumulator : store 19=total.bits)
    (expectedCode : store 21=List.replicate expected true) (values : List Nat) (suffix : List Bool)
    (input : store 17=(Encoding.list Encoding.natural).encode values++suffix) :
    ∃ time ≤ 2030*((store 17).length+total.size+expected+1)^3,
      Executes countsShape store time (countsShapeStore store accepted tail suffix total expected values):=by
  let original : Store 19:=store ∘ countsRoles
  have originalWork (r : Fin 21) (small : r.val<17) (different : r≠1) : original r=[]:=by
    apply work (countsRoles r) small
    intro same
    exact different (countsRoles.injective (same.trans (show 1=countsRoles 1 from rfl)))
  obtain ⟨prefixTime,prefixBound,prefixRun⟩:=countsPrefix_executes original accepted tail status originalWork
    e18 e20 total accumulator values suffix input
  let parsed:=Function.update (Function.update (Function.update (Function.update store 17 suffix)
    0 (List.replicate values.length true)) 19 (total+values.sum).bits) 1
      ((accepted && positiveCounts values)::tail)
  have parsing : Executes (mapRegisters countsRoles countsPrefix) store prefixTime parsed:=by
    apply relocate_executes_frame countsPrefix countsRoles store parsed original
      (countsPrefixStore original accepted tail suffix total values) prefixTime rfl _ _ prefixRun
    · intro r
      fin_cases r <;> simp [parsed,countsPrefixStore,original,countsRoles]
    · intro r outside
      have n0 : r≠0:=by intro same;subst r;exact outside 0 rfl
      have n1 : r≠1:=by intro same;subst r;exact outside 1 rfl
      have n17 : r≠17:=by intro same;subst r;exact outside 17 rfl
      have n19 : r≠19:=by intro same;subst r;exact outside 19 rfl
      simp [parsed,n0,n1,n17,n19]
  have comparing:=DagValidation.equalityGuard_executes 16 countsLengthRoles parsed
    (accepted && positiveCounts values) tail (by simp [parsed,countsLengthRoles])
    (by simp [parsed,countsLengthRoles,work]) (by simp [parsed,countsLengthRoles,work])
    (by simp [parsed,countsLengthRoles,work])
  have first : parsed (countsLengthRoles 0)=List.replicate values.length true:=by simp [parsed,countsLengthRoles]
  have second : parsed (countsLengthRoles 1)=List.replicate expected true:=by simp [parsed,countsLengthRoles,expectedCode]
  have sameLength : (List.replicate values.length true=List.replicate expected true) ↔ values.length=expected:=by
    constructor
    · intro same;simpa only [List.length_replicate] using congrArg List.length same
    · intro same;rw [same]
  rw [first,second] at comparing
  simp only [sameLength] at comparing
  have final : Function.update parsed (countsLengthRoles 2)
      (((accepted && positiveCounts values) && decide (values.length=expected))::tail)=
      countsShapeStore store accepted tail suffix total expected values:=by
    change Function.update parsed 1 _=_
    simp only [parsed,Function.update_idem,countsShapeStore]
  rw [final] at comparing
  have comparisonBound:=Compare.preservingCost_le (List.replicate values.length true) (List.replicate expected true)
  simp only [List.length_replicate] at comparisonBound
  have countBound : values.length≤(store 17).length:=by
    have count:=VerifiedParser.sequence_count_le (codec:=Encoding.natural)
      (fun value=>by simp only [Encoding.natural_length];omega) values
    rw [input]
    change values.length≤((Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values)++suffix).length
    simp only [List.length_append]
    omega
  let S:=(store 17).length+total.size+expected+1
  have prefixLimit : prefixTime≤2000*S^3:=by
    apply prefixBound.trans;gcongr;change (store 17).length+total.size+1≤S;dsimp only [S];omega
  have linear : S≤S^3:=Nat.le_self_pow (by decide) _
  have one : 1≤S^3:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  have compareLimit : Compare.preservingCost (List.replicate values.length true)
      (List.replicate expected true)≤6*S+11:=by dsimp only [S];omega
  exact ⟨_,by change _≤2030*S^3;omega,parsing.sequence comparing⟩

end Counting.StackMachine.RealizabilityCheck
