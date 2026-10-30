import Counting.StackDagRedLoop
import Counting.StackEncodingListReadHeader

/-! Check every referenced source level in a canonical incoming-list code.
The count header is read by the bounded parser, and each item performs its
own physical serialized-node lookup. Multiplicities remain binary fields. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def redPrefixHeaderRoles : FullListWorkspace 15:=
  ⟨![28,1,0,2,30,3,8,9,4,10,11,5,6,7,12,13,14],by decide⟩

def redIncomingPrefix : Routine 30:=
  sequence (readListHeader 15 redPrefixHeaderRoles) (forEach 30 redItem)

def redPrefixStore (store : Store 30) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current targetLevel : Nat) (edges : List (Nat×Nat))
    (suffix : List Bool) : Store 30:=
  Function.update (Function.update store 28 suffix) 1
    ((accepted && edges.all (fun edge=>redCondition values current targetLevel edge.1))::tail)

theorem redIncomingPrefix_executes (store : Store 30) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 32,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 32,r∈({18,19,20,22,25,26,31}:Finset (Fin 32)) → store r=[])
    (counterEmpty : store 30=[])
    (values : List Executable.Node) (current targetLevel : Nat) (inside : current<values.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (level : store 21=targetLevel.bits) (budget : (store 29).length=current)
    (edges : List (Nat×Nat)) (suffix : List Bool)
    (input : store 28=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix) :
    ∃ time ≤ 23000*((store 17).length+(store 28).length+targetLevel.size+1)^5,
      Executes redIncomingPrefix store time (redPrefixStore store accepted tail values current targetLevel edges suffix) := by
  let codec:=Encoding.product Encoding.natural Encoding.natural
  have positive (edge : Nat×Nat) : 0<(codec.encode edge).length := by
    simp [codec,Encoding.product,Encoding.natural_length]
  have headerWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (redPrefixHeaderRoles i)=[] := by
    fin_cases i <;> simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [redPrefixHeaderRoles,work,counterEmpty]
  obtain ⟨headerTime,headerBound,headerRun⟩:=readListHeader_canonical 15 redPrefixHeaderRoles store accepted tail
    status headerWork codec positive edges suffix input
  let middle:=Function.update (Function.update store 28 (Encoding.sequence codec edges++suffix))
    30 (List.replicate edges.length true)
  have middleStatus : middle 1=accepted::tail:=by simp [middle,status]
  have middleWork (r : Fin 32) (small : r.val<17) (ne : r≠1) : middle r=[] := by
    have n28 : r≠28:=by intro eq;subst r;norm_num at small
    have n30 : r≠30:=by intro eq;subst r;norm_num at small
    simp [middle,n28,n30,work r small ne]
  have middleExtra (r : Fin 32) (member : r∈({18,19,20,22,25,26,31}:Finset (Fin 32))) : middle r=[] := by
    have n28 : r≠28:=by intro eq;subst r;exact (by decide : (28:Fin 32)∉({18,19,20,22,25,26,31}:Finset (Fin 32))) member
    have n30 : r≠30:=by intro eq;subst r;exact (by decide : (30:Fin 32)∉({18,19,20,22,25,26,31}:Finset (Fin 32))) member
    simp [middle,n28,n30,extraWork r member]
  have inputLength : (middle 28).length≤(store 28).length := by
    rw [input]
    change (Encoding.sequence codec edges++suffix).length≤
      ((Encoding.natural.encode edges.length++Encoding.sequence codec edges)++suffix).length
    simp only [List.length_append]
    omega
  obtain ⟨loopTime,loopBound,loopRun⟩:=redLoop_executes middle accepted tail middleStatus middleWork middleExtra
    values current targetLevel inside sourceSuffix (by simp [middle,source]) (by simp [middle,level])
    (by simp [middle,budget]) edges suffix (by simp [middle,codec])
    (List.replicate edges.length true) (by simp [middle]) (by simp) (store 28).length inputLength
  have sourceSame : middle 17=store 17:=by simp [middle]
  rw [sourceSame] at loopBound
  have restored : redLoopStore middle accepted tail values current targetLevel edges suffix=
      redPrefixStore store accepted tail values current targetLevel edges suffix := by
    funext r
    by_cases r1 : r=1
    · subst r;simp [redLoopStore,redPrefixStore]
    · by_cases r28 : r=28
      · subst r;simp [redLoopStore,redPrefixStore]
      · by_cases r30 : r=30
        · subst r;simp [redLoopStore,redPrefixStore,counterEmpty]
        · simp [redLoopStore,redPrefixStore,middle,r1,r28,r30]
  rw [restored] at loopRun
  have countBound : edges.length≤(store 28).length := by
    have count:=VerifiedParser.sequence_count_le positive edges
    rw [input]
    change edges.length≤((Encoding.natural.encode edges.length++Encoding.sequence codec edges)++suffix).length
    simp only [List.length_append]
    omega
  change headerTime≤1820*((store 28).length+1)^3 at headerBound
  let S:=(store 17).length+(store 28).length+targetLevel.size+1
  have positiveS : 1≤S:=by dsimp [S];omega
  have countS : edges.length≤S:=by dsimp [S];omega
  have headerLimit : headerTime≤1820*S^3 := by
    apply headerBound.trans
    gcongr
    dsimp [S]
    omega
  have loopLimit : loopTime≤20100*S^5+2*S+1 := by
    have bound : loopTime≤S*(20100*S^4+2)+1:=loopBound.trans (by gcongr)
    nlinarith [show S*S^4=S^5 by ring]
  have cube : S^3≤S^5:=Nat.pow_le_pow_right positiveS (by decide)
  have single : S≤S^5:=Nat.le_self_pow (by decide) _
  refine ⟨headerTime+1+loopTime,?_,headerRun.sequence loopRun⟩
  change headerTime+1+loopTime≤23000*S^5
  omega

end Counting.StackMachine.DagValidation
