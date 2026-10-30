import Counting.StackFrameReadPreserving
import Counting.StackDagGuards

/-! A total compact-count lookup checks that one selected field is exactly
one. The serialized source and the unary field index are preserved; a
missing field or malformed frame yields false. Canonical-list semantics
is stated separately from this raw-field behavior. -/
namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def countOneReaderRoles : Fin 8 ↪ Fin 9:=⟨![0,1,3,2,5,6,7,8],by decide⟩
def countOneCompareRoles : Fin 6 ↪ Fin 9:=⟨![3,4,2,5,6,7],by decide⟩

def countOneGuard : Routine 7:=sequence (FieldAccess.preservingRead 1 countOneReaderRoles)
  (sequence (ofProgram (combineFlagsProgram 7 2))
    (sequence (pushBit 4 true)
      (sequence (DagValidation.equalityGuard 3 countOneCompareRoles)
        (sequence (clear 3) (clear 4)))))

theorem selectPayload_length_le (input : List Bool) (index : Nat) :
    ((FieldAccess.selectPayload input index).getD []).length ≤ input.length:=by
  have payloadBound:=unframe_payload_length (FieldAccess.skipMany index input)
  have remaining:=FieldAccess.skipMany_length index input
  exact payloadBound.trans remaining

theorem countOneGuard_executes (store : Store 7) (accepted : Bool) (tail : List Bool)
    (status : store 2=accepted::tail)
    (empty : ∀ r : Fin 9,3≤r.val → store r=[]) :
    ∃ time ≤ 60*((store 0).length+(store 1).length+1),
      Executes countOneGuard store time (Function.update store 2
        ((accepted && decide (FieldAccess.selectPayload (store 0) (store 1).length=some [true]))::tail)):=by
  let selected:=FieldAccess.selectPayload (store 0) (store 1).length
  obtain ⟨readTime,readBound,reading⟩:=FieldAccess.preservingRead_executes 1 countOneReaderRoles store
    (empty 5 (by decide)) (empty 6 (by decide)) (empty 7 (by decide)) (empty 8 (by decide))
  let readStore:=Function.update (Function.update store 3 (selected.getD [])) 2 (selected.isSome::accepted::tail)
  have readAs : Executes (FieldAccess.preservingRead 1 countOneReaderRoles) store readTime readStore:=by
    simpa [countOneReaderRoles,selected,empty,status,readStore] using reading
  have combining:=combineFlags_executes 7 2 readStore accepted selected.isSome tail (by simp [readStore])
  let combined:=Function.update readStore 2 ((accepted && selected.isSome)::tail)
  have pushing:=pushBit_executes (4:Fin 9) true combined
  have four : combined 4=[]:=by simp [combined,readStore,empty]
  rw [four] at pushing
  let ready:=Function.update combined 4 [true]
  have comparing:=DagValidation.equalityGuard_executes 3 countOneCompareRoles ready
    (accepted && selected.isSome) tail (by simp [ready,combined,countOneCompareRoles])
    (by simp [ready,combined,readStore,countOneCompareRoles,empty])
    (by simp [ready,combined,readStore,countOneCompareRoles,empty])
    (by simp [ready,combined,readStore,countOneCompareRoles,empty])
  have first : ready (countOneCompareRoles 0)=selected.getD []:=by simp [ready,combined,readStore,countOneCompareRoles]
  have second : ready (countOneCompareRoles 1)=[true]:=by simp [ready,countOneCompareRoles]
  rw [first,second] at comparing
  let checked:=Function.update ready 2 (((accepted && selected.isSome) && decide (selected.getD []=[true]))::tail)
  have clearingPayload:=clear_executes (3:Fin 9) checked
  have payload : checked 3=selected.getD []:=by simp [checked,ready,combined,readStore]
  rw [payload] at clearingPayload
  let almost:=Function.update checked 3 []
  have clearingOne:=clear_executes (4:Fin 9) almost
  have one : almost 4=[true]:=by simp [almost,checked,ready]
  rw [one] at clearingOne
  have predicate : ((accepted && selected.isSome) && decide (selected.getD []=[true]))=
      (accepted && decide (selected=some [true])):=by
    cases selected <;> simp
  have final : Function.update almost 4 []=Function.update store 2 ((accepted && decide (selected=some [true]))::tail):=by
    funext r
    fin_cases r <;> simp [almost,checked,ready,combined,readStore,empty,predicate]
  rw [final] at clearingOne
  have selectedLength:=selectPayload_length_le (store 0) (store 1).length
  have compareBound:=Compare.preservingCost_le (selected.getD []) [true]
  change readTime≤10*(store 0).length+8*(store 1).length+14 at readBound
  refine ⟨_,?_,readAs.sequence (combining.sequence (pushing.sequence (comparing.sequence
    (clearingPayload.sequence clearingOne))))⟩
  simp only [List.length_cons,List.length_nil] at compareBound ⊢
  change (selected.getD []).length≤(store 0).length at selectedLength
  omega

theorem countOneGuard_naturalList (values : List Nat) (index : Nat) :
    FieldAccess.selectPayload ((Encoding.list Encoding.natural).encode values) (index+1)=some [true] ↔
      values[index]?=some 1:=by
  rw [FieldAccess.selectPayload_naturalList]
  cases valueEq:values[index]? with
  | none=>simp
  | some value=>
    simp only [Option.map_some,Option.some.injEq]
    rw [←show (1:Nat).bits=[true] by decide]
    exact Encoding.bits_injective.eq_iff

end Counting.StackMachine.RealizabilityCheck
