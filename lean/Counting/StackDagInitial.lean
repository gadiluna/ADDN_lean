import Counting.StackDagParentFields
import Counting.StackDagSelectedHeader

/-! Exact initial-level semantic validation. The degree and incoming-list
suffix is compared to the actual canonical encoding of (0,[]). This checks
structure, not merely successful decoding. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def initialLevelRoles : Fin 6 ↪ Fin 8:=⟨![0,4,3,5,6,7],by decide⟩
def initialParentRoles : Fin 6 ↪ Fin 8:=⟨![1,4,3,5,6,7],by decide⟩
def initialSuffixRoles : Fin 6 ↪ Fin 8:=⟨![2,4,3,5,6,7],by decide⟩

def initialCheckRoutine : Routine 6:=
  sequence (equalityGuard 2 initialLevelRoles)
    (sequence (equalityGuard 2 initialParentRoles)
      (sequence (prepend 4 [false,false])
        (sequence (equalityGuard 2 initialSuffixRoles) (clear 4))))

def initialCheck (store : Store 6) : Bool:=
  decide (store 0=[]) && decide (store 1=[]) && decide (store 2=[false,false])

def initialCost (store : Store 6) : Nat:=
  (Compare.preservingCost (store 0) []+4)+1+
    ((Compare.preservingCost (store 1) []+4)+1+(4+1+
      ((Compare.preservingCost (store 2) [false,false]+4)+1+3)))

theorem initialCheck_executes (store : Store 6) (accepted : Bool) (tail : List Bool)
    (status : store 3=accepted::tail) (work : ∀ r : Fin 8,4≤r.val → store r=[]) :
    Executes initialCheckRoutine store (initialCost store)
      (Function.update store 3 ((accepted && initialCheck store)::tail)) := by
  have level:=equalityGuard_executes 2 initialLevelRoles store accepted tail status
    (work 5 (by decide)) (work 6 (by decide)) (work 7 (by decide))
  change Executes (equalityGuard 2 initialLevelRoles) store
    (Compare.preservingCost (store 0) (store 4)+4)
    (Function.update store 3 ((accepted && decide (store 0=store 4))::tail)) at level
  rw [work 4 (by decide)] at level
  let first:=Function.update store 3 ((accepted && decide (store 0=[]))::tail)
  have parent:=equalityGuard_executes 2 initialParentRoles first (accepted && decide (store 0=[])) tail
    (by simp [first,initialParentRoles])
    (by simp [first,initialParentRoles,work]) (by simp [first,initialParentRoles,work])
    (by simp [first,initialParentRoles,work])
  let second:=Function.update store 3 (((accepted && decide (store 0=[])) && decide (store 1=[]))::tail)
  have parentRun : Executes (equalityGuard 2 initialParentRoles) first (Compare.preservingCost (store 1) []+4) second := by
    simpa [first,second,initialParentRoles,work 4 (by decide)] using parent
  have pushing:=prepend_executes (4:Fin 8) [false,false] second
  have secondEmpty : second 4=[]:=by simp [second,work]
  rw [secondEmpty,List.append_nil] at pushing
  let constant:=Function.update second 4 [false,false]
  have suffix:=equalityGuard_executes 2 initialSuffixRoles constant
    ((accepted && decide (store 0=[])) && decide (store 1=[])) tail
    (by simp [constant,second,initialSuffixRoles])
    (by simp [constant,second,initialSuffixRoles,work])
    (by simp [constant,second,initialSuffixRoles,work])
    (by simp [constant,second,initialSuffixRoles,work])
  let checked:=Function.update constant 3
    ((((accepted && decide (store 0=[])) && decide (store 1=[])) && decide (store 2=[false,false]))::tail)
  have suffixRun : Executes (equalityGuard 2 initialSuffixRoles) constant
      (Compare.preservingCost (store 2) [false,false]+4) checked := by
    simpa [constant,second,checked,initialSuffixRoles] using suffix
  have clearing:=clear_executes (4:Fin 8) checked
  have constantValue : checked 4=[false,false]:=by simp [checked,constant]
  rw [constantValue] at clearing
  have final : Function.update checked 4 []=Function.update store 3 ((accepted && initialCheck store)::tail) := by
    funext r
    fin_cases r <;> simp [checked,constant,second,initialCheck,Bool.and_assoc,work 4 (by decide)]
  rw [final] at clearing
  exact level.sequence (parentRun.sequence (pushing.sequence (suffixRun.sequence clearing)))

theorem initialCost_le (store : Store 6) :
    initialCost store≤100*((store 0).length+(store 1).length+(store 2).length+1) := by
  have a:=Compare.preservingCost_le (store 0) []
  have b:=Compare.preservingCost_le (store 1) []
  have c:=Compare.preservingCost_le (store 2) [false,false]
  simp only [List.length_nil,List.length_cons] at a b c
  unfold initialCost
  omega

theorem nodeSuffix_empty_iff (node : Executable.Node) :
    nodeSuffix node=[false,false] ↔ node.degree=0 ∧ node.incoming=[] := by
  let codec:=Encoding.product Encoding.natural (Encoding.list (Encoding.product Encoding.natural Encoding.natural))
  change codec.encode (node.degree,node.incoming)=codec.encode (0,[]) ↔ _
  rw [codec.injective.eq_iff]
  simp

theorem parentCode_zero_iff (node : Executable.Node) : parentCode node=0 ↔ node.parent=none := by
  cases reference:node.parent <;> simp [parentCode,reference]

theorem initialCheck_typed (node : Executable.Node) :
    initialCheck ![node.level.bits,(parentCode node).bits,nodeSuffix node,[],[],[],[],[]]=true ↔
      node.level=0 ∧ node.parent=none ∧ node.degree=0 ∧ node.incoming=[] := by
  change ((decide (node.level.bits=[]) && decide ((parentCode node).bits=[]) &&
    decide (nodeSuffix node=[false,false]))=true) ↔ _
  have zero (n : Nat) : n.bits=[] ↔ n=0 := by
    change n.bits=Nat.bits 0 ↔ n=0
    exact Encoding.bits_injective.eq_iff
  simp only [Bool.and_eq_true,decide_eq_true_eq,zero,parentCode_zero_iff,nodeSuffix_empty_iff]
  tauto

end Counting.StackMachine.DagValidation
