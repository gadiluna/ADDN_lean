import Counting.StackDagClean
import Counting.StackEncodingPairSemantics

/-! One canonical incoming edge: parse its two binary fields, copy the
explicit current-index budget, perform the real graph reference check, and
restore the workspace. The multiplicity remains for the independent
positive/sorted incoming pass; it is not expanded into repeated messages. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def redItemPairRoles : Fin 5 ↪ Fin 32:=⟨![28,22,31,4,1],by decide⟩
def redItemCheckRoles : Fin 28 ↪ Fin 32 where
  toFun r:=⟨r.val,by have:=r.isLt;omega⟩
  inj':=by intro a b equal;apply Fin.ext;exact congrArg (fun r:Fin 32=>r.val) equal

def redItem : Routine 30:=
  sequence (pairRoutine 27 redItemPairRoles)
    (sequence (ofProgram (combineFlagsProgram 30 1))
      (sequence (clear 31)
        (sequence (ofProgram (ListPrograms.copyProgram 29 29 25 4))
          (mapRegisters redItemCheckRoles redReferenceClean))))

def redItemStore (store : Store 30) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current targetLevel : Nat) (edge : Nat×Nat)
    (suffix : List Bool) : Store 30:=
  Function.update (Function.update store 28 suffix) 1
    ((accepted && redCondition values current targetLevel edge.1)::tail)

theorem redItem_executes (store : Store 30) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 32,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 32,r∈({18,19,20,22,25,26,31}:Finset (Fin 32)) → store r=[])
    (values : List Executable.Node) (current targetLevel : Nat) (inside : current<values.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (level : store 21=targetLevel.bits) (budget : (store 29).length=current)
    (edge : Nat×Nat) (suffix : List Bool)
    (input : store 28=(Encoding.product Encoding.natural Encoding.natural).encode edge++suffix) :
    ∃ time ≤ 20100*((store 17).length+(store 28).length+targetLevel.size+1)^4,
      Executes redItem store time (redItemStore store accepted tail values current targetLevel edge suffix) := by
  obtain ⟨pairTime,pairBound,pairRun⟩:=pair_executes 27 redItemPairRoles redItemPairRoles.injective
    store (work 4 (by decide) (by decide))
  rw [pair_result_spec 27 redItemPairRoles redItemPairRoles.injective] at pairRun
  have parsed : parsePair (store 28)=⟨edge.1.bits,edge.2.bits,suffix,true⟩:=by
    rw [input]
    exact parsePair_frames _ _ _
  let parsedStore:=Function.update (Function.update (Function.update (Function.update store 28 suffix)
    22 edge.1.bits) 31 edge.2.bits) 1 (true::accepted::tail)
  have parsedEq : pairExpected 27 redItemPairRoles store=parsedStore := by
    funext r
    fin_cases r <;> simp [pairExpected,redItemPairRoles,parsed,parsedStore,status,extraWork,work]
  rw [parsedEq] at pairRun
  have combined:=combineFlags_executes 30 1 parsedStore accepted true tail (by simp [parsedStore])
  let joined:=Function.update parsedStore 1 (accepted::tail)
  have clearing:=clear_executes (31:Fin 32) joined
  have countValue : joined 31=edge.2.bits:=by simp [joined,parsedStore]
  rw [countValue] at clearing
  let cleared:=Function.update joined 31 []
  have copied:=copy_executes 29 29 25 4 (by decide) (by decide) (by decide) cleared
    (by simp [cleared,joined,parsedStore,work])
  have budgetSource : cleared 29=store 29:=by simp [cleared,joined,parsedStore]
  have budgetEmpty : cleared 25=[]:=by simp [cleared,joined,parsedStore,extraWork]
  rw [budgetSource,budgetEmpty,List.append_nil] at copied
  let ready:=Function.update cleared 25 (store 29)
  let localStore : Store 26:=ready ∘ redItemCheckRoles
  have localStatus : localStore 1=accepted::tail:=by simp [localStore,ready,cleared,joined,parsedStore,redItemCheckRoles]
  have localWork (r : Fin 28) (small : r.val<17) (ne : r≠1) : localStore r=[] := by
    have movedSmall : (redItemCheckRoles r).val<17:=small
    have movedNe : redItemCheckRoles r≠1:=by
      intro eq;apply ne;apply Fin.ext;exact congrArg (fun r:Fin 32=>r.val) eq
    have ne22 : redItemCheckRoles r≠22:=by intro eq;rw [eq] at movedSmall;norm_num at movedSmall
    have ne25 : redItemCheckRoles r≠25:=by intro eq;rw [eq] at movedSmall;norm_num at movedSmall
    have ne28 : redItemCheckRoles r≠28:=by intro eq;rw [eq] at movedSmall;norm_num at movedSmall
    have ne31 : redItemCheckRoles r≠31:=by intro eq;rw [eq] at movedSmall;norm_num at movedSmall
    simp [localStore,ready,cleared,joined,parsedStore,movedNe,ne22,ne25,ne28,ne31,work _ movedSmall movedNe]
  have localExtra (r : Fin 28) (member : r∈({18,19,20,26}:Finset (Fin 28))) : localStore r=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl
    all_goals simp [localStore,ready,cleared,joined,parsedStore,redItemCheckRoles,extraWork]
  have localSource : localStore 17=Encoding.sequence Encoding.node values++sourceSuffix:=by
    simp [localStore,ready,cleared,joined,parsedStore,redItemCheckRoles,source]
  obtain ⟨checkTime,checkBound,checkRun⟩:=redReferenceClean_executes localStore accepted tail localStatus localWork
    localExtra values current targetLevel edge.1 inside sourceSuffix localSource
    (by simp [localStore,ready,cleared,joined,parsedStore,redItemCheckRoles,level])
    (by simp [localStore,ready,cleared,joined,parsedStore,redItemCheckRoles])
    (by simp [localStore,ready,cleared,joined,parsedStore,redItemCheckRoles,budget])
  have relocated : Executes (mapRegisters redItemCheckRoles redReferenceClean) ready checkTime
      (redItemStore store accepted tail values current targetLevel edge suffix) := by
    apply relocate_executes_frame redReferenceClean redItemCheckRoles ready
      (redItemStore store accepted tail values current targetLevel edge suffix) localStore
      (redCleanStore localStore accepted tail values current targetLevel edge.1) checkTime rfl _ _ checkRun
    · intro r
      fin_cases r <;> simp [redItemStore,redCleanStore,localStore,ready,cleared,joined,parsedStore,
        redItemCheckRoles,extraWork]
    · intro r outside
      have n1 : r≠1:=by intro eq;subst r;exact outside 1 rfl
      have n22 : r≠22:=by intro eq;subst r;exact outside 22 rfl
      have n25 : r≠25:=by intro eq;subst r;exact outside 25 rfl
      by_cases r31 : r=31
      · subst r;simp [redItemStore,ready,cleared,extraWork]
      · simp [redItemStore,ready,cleared,joined,parsedStore,n1,n22,n25,r31]
  have combinedRun : Executes (ofProgram (combineFlagsProgram 30 1)) parsedStore 3 joined:=by
    simpa only [Bool.and_true] using combined
  have composed:=pairRun.sequence (combinedRun.sequence (clearing.sequence (copied.sequence relocated)))
  have inputLength : edge.1.size+edge.2.size≤(store 28).length := by
    rw [input]
    simp only [Encoding.product,List.length_append,Encoding.natural_length]
    omega
  have count:=node_sequence_count_le values
  have currentBound : current≤(store 17).length:=by rw [source,List.length_append];omega
  have same : localStore 17=store 17:=by simp [localStore,ready,cleared,joined,parsedStore,redItemCheckRoles]
  rw [same] at checkBound
  have checkLimit : checkTime+(6*(store 28).length+edge.2.size+5*current+23) ≤
      20100*((store 17).length+(store 28).length+targetLevel.size+1)^4 := by
    have mono : checkTime≤20020*((store 17).length+(store 28).length+targetLevel.size+1)^4:=by
      apply checkBound.trans
      gcongr
      omega
    have growth:=Nat.le_self_pow (by decide : 4≠0)
      ((store 17).length+(store 28).length+targetLevel.size+1)
    omega
  change pairTime≤6*(store 28).length+13 at pairBound
  refine ⟨_,?_,composed⟩
  rw [Encoding.bits_length,budget]
  omega

end Counting.StackMachine.DagValidation
