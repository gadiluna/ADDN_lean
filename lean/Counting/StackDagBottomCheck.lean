import Counting.StackDagReferenceTarget

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def bottomCompareRoles : Fin 6 ↪ Fin 35:=⟨![22,26,1,2,3,4],by decide⟩
def bottomCheck : Routine 33:=sequence (ofProgram (flaggedProgram 31 28 22 4 1))
  (sequence (ofProgram (combineFlagsProgram 33 1))
    (sequence (equalityGuard 29 bottomCompareRoles) (clear 22)))

theorem bottomCheck_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[]) (e22 : store 22=[])
    (expected bottom : Nat) (expectedCode : store 26=expected.bits)
    (suffix : List Bool) (input : store 28=Encoding.natural.encode bottom++suffix) :
    ∃ time ≤ 30*((store 28).length+expected.size+1),
      Executes bottomCheck store time
        (Function.update (Function.update store 28 suffix) 1 ((accepted && decide (bottom=expected))::tail)) := by
  obtain ⟨parseTime,parseBound,parsing⟩:=flagged_executes 31 28 22 4 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) store e4
  rw [flagged_result_updates 31 28 22 4 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) store e4] at parsing
  have parsed : Encoding.unframe (store 28)=some (bottom.bits,suffix):=by
    rw [input]
    exact Encoding.unframe_frame _ _
  let readStore:=Function.update (Function.update (Function.update store 28 suffix) 22 bottom.bits) 1 (true::accepted::tail)
  have parsingAs : Executes (ofProgram (flaggedProgram 31 28 22 4 1)) store parseTime readStore:=by
    simpa [unframePayload,unframeSuffix,parsed,e22,status,readStore] using parsing
  have combined:=combineFlags_executes 33 1 readStore accepted true tail (by simp [readStore])
  let ready:=Function.update readStore 1 (accepted::tail)
  have combining : Executes (ofProgram (combineFlagsProgram 33 1)) readStore 3 ready:=by
    simpa only [Bool.and_true] using combined
  have compared:=equalityGuard_executes 29 bottomCompareRoles ready accepted tail
    (by simp [bottomCompareRoles,ready]) (by simp [bottomCompareRoles,ready,readStore,e2])
    (by simp [bottomCompareRoles,ready,readStore,e3]) (by simp [bottomCompareRoles,ready,readStore,e4])
  have first : ready (bottomCompareRoles 0)=bottom.bits:=by simp [bottomCompareRoles,ready,readStore]
  have second : ready (bottomCompareRoles 1)=expected.bits:=by simp [bottomCompareRoles,ready,readStore,expectedCode]
  have predicate : decide (ready (bottomCompareRoles 0)=ready (bottomCompareRoles 1))=decide (bottom=expected):=by
    rw [first,second]
    simp only [Encoding.bits_injective.eq_iff]
  rw [predicate] at compared
  let checked:=Function.update ready 1 ((accepted && decide (bottom=expected))::tail)
  have clearing:=clear_executes (22:Fin 35) checked
  have selected : checked 22=bottom.bits:=by simp [checked,ready,readStore]
  rw [selected,Encoding.bits_length] at clearing
  have final : Function.update checked 22 []=
      Function.update (Function.update store 28 suffix) 1 ((accepted && decide (bottom=expected))::tail):=by
    funext r
    by_cases r1 : r=1 <;> by_cases r22 : r=22 <;> by_cases r28 : r=28 <;>
      simp [checked,ready,readStore,r1,r22,r28,e22]
  rw [final] at clearing
  have compareBound:=Compare.preservingCost_le (ready (bottomCompareRoles 0)) (ready (bottomCompareRoles 1))
  rw [first,second,Encoding.bits_length,Encoding.bits_length] at compareBound
  have inputLength : bottom.size≤(store 28).length:=by
    rw [input,List.length_append,Encoding.natural_length]
    omega
  change parseTime≤3*(store 28).length+4 at parseBound
  refine ⟨_,?_,parsingAs.sequence (combining.sequence (compared.sequence clearing))⟩
  rw [first,second]
  omega

end Counting.StackMachine.DagValidation
