import Counting.StackEncodingDagParser
import Counting.StackEncodingPairSemantics

/-! Charged extraction of the level, optional-parent code and leader bit
from a serialized node. The separate node codec validator establishes
canonicality; this reader also has a precise total behavior on malformed
words. It leaves the degree and incoming-list suffix available for checks. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

structure Header where
  level : List Bool
  parent : List Bool
  leader : List Bool
  suffix : List Bool
  accepted : Bool
  deriving DecidableEq,Repr

def header (input : List Bool) : Header :=
  let pair:=parsePair input
  let status:=booleanEffect pair.suffix
  ⟨pair.first,pair.second,status.code,status.suffix,pair.accepted && status.accepted⟩

abbrev HeaderWorkspace (extra : Nat):=Fin 6 ↪ Fin (extra+6)

def pairRoles (extra : Nat) (w : HeaderWorkspace extra) : Fin 5 ↪ Fin (extra+6) where
  toFun i:=w (![0,1,2,5,4] i)
  inj':=by
    intro a b equal
    have h:=w.injective equal
    fin_cases a <;> fin_cases b <;> simp_all

def headerRoutine (extra : Nat) (w : HeaderWorkspace extra) : Routine (extra+4) :=
  sequence (pairRoutine (extra+1) (pairRoles extra w))
    (booleanItem (extra+4) (w 0) (w 4) (w 3))

def headerStore (extra : Nat) (w : HeaderWorkspace extra)
    (store : Store (extra+4)) : Store (extra+4) :=
  let result:=header (store (w 0))
  fun r=>if r=w 0 then result.suffix else if r=w 1 then result.level++store r
    else if r=w 2 then result.parent++store r else if r=w 3 then result.leader.reverse++store r
    else if r=w 4 then result.accepted::store r else store r

theorem header_executes (extra : Nat) (w : HeaderWorkspace extra) (store : Store (extra+4))
    (scratch : store (w 5)=[]) :
    ∃ time ≤ 6*(store (w 0)).length+17,
      Executes (headerRoutine extra w) store time (headerStore extra w store) := by
  have ne (i j : Fin 6) (h : i≠j) : w i≠w j:=fun equal=>h (w.injective equal)
  obtain ⟨pairTime,pairBound,pairRun⟩:=pair_executes (extra+1) (pairRoles extra w)
    (pairRoles extra w).injective store scratch
  rw [pair_result_spec (extra+1) (pairRoles extra w) (pairRoles extra w).injective] at pairRun
  let paired:=pairExpected (extra+1) (pairRoles extra w) store
  have nextStatus : paired (w 4)=(parsePair (store (w 0))).accepted::store (w 4) := by
    simp [paired,pairExpected,pairRoles,w.injective.eq_iff]
  have nextSource : paired (w 0)=(parsePair (store (w 0))).suffix := by
    simp [paired,pairExpected,pairRoles]
  have booleanRun:=booleanItem_executes (extra+4) (w 0) (w 4) (w 3)
    (ne 0 4 (by decide)) (ne 0 3 (by decide)) (ne 4 3 (by decide)) paired
    (parsePair (store (w 0))).accepted (store (w 4)) nextStatus
  rw [nextSource] at booleanRun
  have composed:=pairRun.sequence booleanRun
  have result : parseStore (w 0) (w 4) (w 3) paired (parsePair (store (w 0))).accepted
      (store (w 4)) (booleanEffect (parsePair (store (w 0))).suffix)=headerStore extra w store := by
    funext r
    by_cases r0 : r=w 0
    · subst r;simp [parseStore,headerStore,header]
    · by_cases r1 : r=w 1
      · subst r;simp [parseStore,headerStore,header,paired,pairExpected,pairRoles,w.injective.eq_iff]
      · by_cases r2 : r=w 2
        · subst r;simp [parseStore,headerStore,header,paired,pairExpected,pairRoles,w.injective.eq_iff]
        · by_cases r3 : r=w 3
          · subst r;simp [parseStore,headerStore,header,paired,pairExpected,pairRoles,w.injective.eq_iff]
          · by_cases r4 : r=w 4
            · subst r;simp [parseStore,headerStore,header,w.injective.eq_iff]
            · by_cases r5 : r=w 5
              · subst r;simp [parseStore,headerStore,paired,pairExpected,pairRoles,w.injective.eq_iff,scratch]
              · simp [parseStore,headerStore,paired,pairExpected,pairRoles,r0,r1,r2,r3,r4,r5]
  rw [result] at composed
  refine ⟨_,?_,composed⟩
  change pairTime≤6*(store (w 0)).length+13 at pairBound
  split <;> omega

def parentCode (node : Executable.Node) : Nat:=node.parent.map (·+1) |>.getD 0

theorem header_node (node : Executable.Node) (suffix : List Bool) :
    header (Encoding.node.encode node++suffix)=
      ⟨node.level.bits,(parentCode node).bits,[node.leader],
        Encoding.natural.encode node.degree++
          (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming++suffix,true⟩ := by
  change header ((Encoding.natural.encode node.level++
    (Encoding.natural.encode (parentCode node)++
      ([node.leader]++(Encoding.natural.encode node.degree++
        (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming))))++suffix)=_
  simp only [List.append_assoc,header,parsePair,Encoding.natural,Encoding.unframe_frame,
    booleanEffect,Bool.true_and,List.cons_append,List.nil_append]

theorem header_suffix_le (input : List Bool) : (header input).suffix.length ≤ input.length := by
  have pair:=parsePair_length_bound input
  have tail : (booleanEffect (parsePair input).suffix).suffix.length≤(parsePair input).suffix.length := by
    cases suffix:(parsePair input).suffix <;> simp [booleanEffect]
  change (booleanEffect (parsePair input).suffix).suffix.length ≤ input.length
  omega

end Counting.StackMachine.DagValidation
