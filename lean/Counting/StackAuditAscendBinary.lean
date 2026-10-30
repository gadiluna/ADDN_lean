import Counting.StackAuditAscendParent
import Counting.StackEncodingBoundedNatural

namespace Counting.StackMachine.AuditAscend
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def countRoles : CountWorkspace 13 := ⟨![21,18,0,2,3,4,20,5,6,7,22],by decide⟩
def readRoles : Fin 20 ↪ Fin 24 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b same;exact Fin.ext (congrArg (fun r : Fin 24=>r.val) same)⟩

/-- The query is a canonical framed natural. Its unary work counter is capped
by the physical table's bit length, never by the numeric index. -/
def binaryParentAt : Routine 22 := sequence (ofProgram (ListPrograms.copyProgram 21 17 22 23))
  (sequence (boundedCount 13 countRoles)
    (sequence (pushBit 1 true)
      (sequence (relocate readParent readRoles)
        (sequence (clear 18) (discardBit 20)))))

theorem clipped_parent (nodes : List Executable.Node) (index budget : Nat)
    (long : nodes.length≤budget) :
    nodes[min index budget]?.getD default=nodes[index]?.getD default := by
  by_cases fits : index≤budget
  · rw [Nat.min_eq_left fits]
  · rw [Nat.min_eq_right (by omega)]
    have missing : nodes[index]?=none := List.getElem?_eq_none (by omega)
    rw [List.getElem?_eq_none long,missing]

theorem binaryParentAt_executes (store : Store 22) (nodes : List Executable.Node) (index : Nat)
    (source : store 17=Encoding.sequence Encoding.node nodes)
    (query : store 21=Encoding.natural.encode index)
    (empty : ∀ r : Fin 24,r≠17 → r≠21 → store r=[]) :
    ∃ time ≤ 200000*((store 17).length+(store 21).length+1)^4,
      Executes binaryParentAt store time
        (Function.update store 2 (DagValidation.parentCode (nodes[index]?.getD default)).bits) := by
  have a:=copy_executes 21 (17:Fin 24) 22 23 (by decide) (by decide) (by decide) store
    (empty 23 (by decide) (by decide))
  rw [empty 22 (by decide) (by decide),List.append_nil] at a
  let copied:=Function.update store 22 (store 17)
  obtain ⟨countTime,countBound,b⟩:=boundedNatural_executes 13 countRoles copied index
    (by simp [copied,countRoles,query]) (by simp [copied,countRoles,empty]) (by
      intro i member;fin_cases i <;> simp_all [copied,countRoles])
  let counted:=boundedNaturalResult 13 countRoles copied index
  let clipped:=min index (store 17).length
  have counter : counted 18=List.replicate clipped true := by
    simp [counted,boundedNaturalResult,countRoles,copied,clipped]
  have status : counted 1=[] := by simp [counted,boundedNaturalResult,countRoles,copied,empty]
  have c:=pushBit_executes (1:Fin 24) true counted
  rw [status] at c
  let prepared:=Function.update counted 1 [true]
  let localStore : Store 18:=prepared ∘ readRoles
  have localSource : localStore 17=Encoding.sequence Encoding.node nodes := by
    simp [localStore,prepared,counted,boundedNaturalResult,countRoles,copied,readRoles,source]
  have localStatus : localStore 1=[true] := by simp [localStore,prepared,readRoles]
  have localEmpty (r : Fin 20) (n1 : r≠1) (n17 : r≠17) (n18 : r≠18) : localStore r=[] := by
    fin_cases r <;> simp_all [localStore,prepared,counted,boundedNaturalResult,countRoles,copied,readRoles]
  obtain ⟨readTime,readBound,d⟩:=readParent_executes localStore nodes localSource localStatus localEmpty
  have localCounter : localStore 18=List.replicate clipped true := by
    simpa [localStore,prepared,readRoles] using counter
  rw [localCounter,List.length_replicate] at d readBound
  have entries : nodes.length ≤ (store 17).length := by
    rw [source];exact DagValidation.node_sequence_count_le nodes
  have same:=clipped_parent nodes index (store 17).length entries
  rw [same] at d
  let result:=Function.update counted 2 (DagValidation.parentCode (nodes[index]?.getD default)).bits
  have wide : Executes (relocate readParent readRoles) prepared readTime result := by
    apply relocate_executes_frame readParent readRoles prepared result localStore _ readTime rfl _ _ d
    · intro r
      fin_cases r <;> simp [result,localStore,prepared,readRoles,status]
    · intro r outside
      have n1 : r≠1 := by intro eq;subst r;exact outside 1 rfl
      have n2 : r≠2 := by intro eq;subst r;exact outside 2 rfl
      simp [result,prepared,n1,n2]
  have e:=clear_executes (18:Fin 24) result
  have counterAt : result 18=List.replicate clipped true := by simp [result,counter]
  rw [counterAt,List.length_replicate] at e
  let cleaned:=Function.update result 18 []
  have f:=discardBit_executes (20:Fin 24) cleaned
  have flagAt : cleaned 20=[decide (index≤(store 17).length)] := by
    simp [cleaned,result,counted,boundedNaturalResult,countRoles,copied,empty]
  rw [flagAt,List.tail_cons] at f
  have final : Function.update cleaned 20 []=
      Function.update store 2 (DagValidation.parentCode (nodes[index]?.getD default)).bits := by
    funext r
    fin_cases r <;> simp [cleaned,result,counted,boundedNaturalResult,countRoles,copied,empty]
  rw [final] at f
  have budgetAt : copied (countRoles 10)=store 17 := by simp [copied,countRoles]
  have tableAt : localStore 17=store 17 := by
    simp [localStore,prepared,readRoles,counted,boundedNaturalResult,countRoles,copied]
  rw [budgetAt,←query] at countBound
  rw [tableAt] at readBound
  let K:=(store 17).length+(store 21).length+1
  have clippedBound : clipped≤(store 17).length := Nat.min_le_right _ _
  have twice : (store 17).length+clipped+1≤2*K := by dsimp only [K];omega
  have raised:=readBound.trans (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left twice 4))
  have positive : 1≤K := by dsimp only [K];omega
  have linear : K≤K^4 := Nat.le_self_pow (by decide) _
  have cube : K^3≤K^4 := Nat.pow_le_pow_right positive (by decide)
  change countTime≤64*K^3 at countBound
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (wide.sequence (e.sequence f))))⟩
  change _≤200000*K^4
  have tableLength : (store 17).length≤K := by dsimp only [K];omega
  nlinarith only [raised,countBound,clippedBound,tableLength,linear,cube,positive]

end Counting.StackMachine.AuditAscend

