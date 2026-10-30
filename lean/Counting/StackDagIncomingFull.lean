import Counting.StackDagIncomingOrdered
import Counting.StackDagRedPrefix
import Counting.StackRoutineMove

/-! Complete incoming-edge condition of `nodeValid`: the first real pass
checks binary multiplicities and strictly increasing bounded references;
the second reads the serialized source nodes and checks their levels.
The input copy and its cleanup are charged explicitly. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def fullIncomingOrderRoles : FullIncomingWorkspace 15:=
  ⟨![28,1,0,2,30,3,8,9,4,10,11,5,6,7,12,13,14,33,24,34],by decide⟩
def fullIncomingRedRoles : Fin 32 ↪ Fin 35 where
  toFun r:=⟨r.val,by have:=r.isLt;omega⟩
  inj':=by intro a b equal;apply Fin.ext;exact congrArg (fun r:Fin 35=>r.val) equal

def fullIncomingPrefix : Routine 33:=
  sequence (ofProgram (ListPrograms.copyProgram 32 28 32 4))
    (sequence (orderedIncomingPrefix 15 fullIncomingOrderRoles)
      (sequence (clear 28)
        (sequence (move 32 32 28 4) (mapRegisters fullIncomingRedRoles redIncomingPrefix))))

def incomingCondition (values : List Executable.Node) (current targetLevel : Nat)
    (edges : List (Nat×Nat)) : Bool:=
  incomingCheck current none edges && edges.all (fun edge=>redCondition values current targetLevel edge.1)

def fullIncomingStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current targetLevel : Nat) (edges : List (Nat×Nat))
    (suffix : List Bool) : Store 33:=
  Function.update (Function.update store 28 suffix) 1
    ((accepted && incomingCondition values current targetLevel edges)::tail)

theorem fullIncomingPrefix_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({18,19,20,22,25,26,30,31,32,33,34}:Finset (Fin 35)) → store r=[])
    (values : List Executable.Node) (current targetLevel : Nat) (inside : current<values.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (level : store 21=targetLevel.bits) (currentBits : store 24=current.bits) (budget : (store 29).length=current)
    (edges : List (Nat×Nat)) (suffix : List Bool)
    (input : store 28=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix) :
    ∃ time ≤ 26000*((store 17).length+(store 28).length+targetLevel.size+current.size+1)^5,
      Executes fullIncomingPrefix store time (fullIncomingStore store accepted tail values current targetLevel edges suffix) := by
  have copied:=copy_executes 32 28 32 4 (by decide) (by decide) (by decide) store
    (work 4 (by decide) (by decide))
  rw [extraWork 32 (by decide),List.append_nil] at copied
  let ready:=Function.update store 32 (store 28)
  have orderWork (i : Fin 20) (lower : 2≤ i.val) (upper : i.val≤17) : ready (fullIncomingOrderRoles i)=[]:=by
    fin_cases i
    all_goals try (norm_num at lower)
    all_goals try (norm_num at upper)
    all_goals simp [ready,fullIncomingOrderRoles,work,extraWork]
  obtain ⟨orderTime,orderBound,ordered⟩:=orderedIncomingPrefix_executes 15 fullIncomingOrderRoles ready accepted tail
    (by simp [ready,fullIncomingOrderRoles,status]) orderWork
    (by simp [ready,fullIncomingOrderRoles,extraWork]) current
    (by simp [ready,fullIncomingOrderRoles,currentBits]) edges suffix
    (by simp [ready,fullIncomingOrderRoles,input])
  let orderedFlag:=accepted && incomingCheck current none edges
  let checked:=orderedIncomingStore 15 fullIncomingOrderRoles ready accepted tail current edges suffix
  have checkedSource : checked 28=suffix:=by simp [checked,orderedIncomingStore,fullIncomingOrderRoles]
  have cleared:=clear_executes (28:Fin 35) checked
  rw [checkedSource] at cleared
  let middle:=Function.update checked 28 []
  have moved:=move_executes 32 32 28 4 (by decide) (by decide) (by decide) middle
    (by simp [middle,checked,orderedIncomingStore,fullIncomingOrderRoles,ready,work])
  have backup : middle 32=store 28:=by simp [middle,checked,orderedIncomingStore,fullIncomingOrderRoles,ready]
  have destination : middle 28=[]:=by simp [middle]
  rw [backup,destination,List.append_nil] at moved
  let restored:=Function.update (Function.update middle 28 (store 28)) 32 []
  have restored_eq : restored=Function.update store 1 (orderedFlag::tail):=by
    funext r
    by_cases r1 : r=1
    · subst r;simp [restored,middle,checked,orderedIncomingStore,fullIncomingOrderRoles,orderedFlag]
    · by_cases r28 : r=28
      · subst r;simp [restored,r1]
      · by_cases r32 : r=32
        · subst r;simp [restored,extraWork]
        · simp [restored,middle,checked,orderedIncomingStore,fullIncomingOrderRoles,ready,r1,r28,r32]
  let localStore : Store 30:=restored ∘ fullIncomingRedRoles
  have localWork (r : Fin 32) (small : r.val<17) (ne : r≠1) : localStore r=[]:=by
    have movedNe : fullIncomingRedRoles r≠1:=by
      intro eq;apply ne;apply Fin.ext;exact congrArg (fun r:Fin 35=>r.val) eq
    simp [localStore,restored_eq,movedNe,work _ small movedNe]
  have localExtra (r : Fin 32) (member : r∈({18,19,20,22,25,26,31}:Finset (Fin 32))) : localStore r=[]:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [localStore,restored_eq,fullIncomingRedRoles,extraWork]
  obtain ⟨redTime,redBound,redRun⟩:=redIncomingPrefix_executes localStore orderedFlag tail
    (by simp [localStore,restored_eq,fullIncomingRedRoles]) localWork localExtra
    (by simp [localStore,restored_eq,fullIncomingRedRoles,extraWork]) values current targetLevel inside sourceSuffix
    (by simp [localStore,restored_eq,fullIncomingRedRoles,source])
    (by simp [localStore,restored_eq,fullIncomingRedRoles,level])
    (by simp [localStore,restored_eq,fullIncomingRedRoles,budget]) edges suffix
    (by simp [localStore,restored_eq,fullIncomingRedRoles,input])
  have relocated : Executes (mapRegisters fullIncomingRedRoles redIncomingPrefix) restored redTime
      (fullIncomingStore store accepted tail values current targetLevel edges suffix):=by
    apply relocate_executes_frame redIncomingPrefix fullIncomingRedRoles restored
      (fullIncomingStore store accepted tail values current targetLevel edges suffix) localStore
      (redPrefixStore localStore orderedFlag tail values current targetLevel edges suffix) redTime rfl _ _ redRun
    · intro r
      fin_cases r <;> simp [fullIncomingStore,redPrefixStore,localStore,restored_eq,fullIncomingRedRoles,
        orderedFlag,incomingCondition,Bool.and_assoc]
    · intro r outside
      have n1 : r≠1:=by intro eq;subst r;exact outside 1 rfl
      have n28 : r≠28:=by intro eq;subst r;exact outside 28 rfl
      simp [fullIncomingStore,restored_eq,n1,n28]
  have sourceLength : localStore 17=store 17:=by simp [localStore,restored_eq,fullIncomingRedRoles]
  have inputLength : localStore 28=store 28:=by simp [localStore,restored_eq,fullIncomingRedRoles]
  rw [sourceLength,inputLength] at redBound
  change orderTime≤2520*((ready 28).length+current.size+1)^3 at orderBound
  have readyInput : ready 28=store 28:=by simp [ready]
  rw [readyInput] at orderBound
  have suffixBound : suffix.length≤(store 28).length:=by rw [input,List.length_append];omega
  let S:=(store 17).length+(store 28).length+targetLevel.size+current.size+1
  have positiveS : 1≤S:=by dsimp [S];omega
  have orderLimit : orderTime≤2520*S^3:=by apply orderBound.trans;gcongr;dsimp [S];omega
  have redLimit : redTime≤23000*S^5:=by apply redBound.trans;gcongr;dsimp [S];omega
  have cube : S^3≤S^5:=Nat.pow_le_pow_right positiveS (by decide)
  have linear : S≤S^5:=Nat.le_self_pow (by decide) _
  have inputLimit : (store 28).length≤S:=by dsimp [S];omega
  refine ⟨_,?_,copied.sequence (ordered.sequence (cleared.sequence (moved.sequence relocated)))⟩
  change (5*(store 28).length+2)+1+(orderTime+1+(suffix.length+1+1+(6*(store 28).length+4+1+redTime)))≤26000*S^5
  omega

theorem incomingCondition_vista (vista : Executable.Vista) (current : Nat) :
    incomingCondition vista.nodes.toList current (vista.node current).level (vista.node current).incoming=
      (Executable.countsSorted (vista.node current).incoming &&
        (vista.node current).incoming.all (fun edge=>edge.1<current &&
          (vista.node edge.1).level+1==(vista.node current).level)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [incomingCondition,Bool.and_eq_true,incomingCheck_iff,List.all_eq_true]
  simp only [redCondition_vista,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  constructor
  · exact fun h=>⟨h.1.1,h.2⟩
  · intro h
    exact ⟨⟨h.1,fun edge member=>(h.2 edge member).1⟩,h.2⟩

end Counting.StackMachine.DagValidation
