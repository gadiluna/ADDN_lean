import Counting.StackAuditPrefixValidate
import Counting.StackAuditPrefixTable
import Counting.StackAuditPrefixDepth
import Counting.AuditPrefixSpec

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def openingFile (vista : Executable.Vista) (leaders candidate last : Nat) (accepted : Bool) : Store 50 :=
  Function.update (tableFile (inputFile [] leaders.bits candidate.bits last.bits (Encoding.vista.encode vista)) vista)
    1 [accepted]

abbrev validDepthBranch : Routine 50 := sequence (pushBit 1 true) checkDepth
abbrev guardedDepth : Routine 50 := branchRoutine 1 validDepthBranch (pushBit 1 false)
abbrev opening : Routine 50 := sequence prepareValidated
  (sequence labelGuards (sequence prepareTable guardedDepth))

/-- All literal opening tests of auditPrefix? run on the actual encoded
input. The only unary quantity prepared is the actual stored-node count.
Invalid vistas skip the bottom lookup and produce a false status. -/
theorem opening_executes (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time ≤ 230000000*((inputWord vista leaders candidate last).length+1)^6,
      Executes opening (inputStore 50 (inputWord vista leaders candidate last)) time
        (openingFile vista leaders candidate last (openingAccepted vista leaders candidate last)) := by
  let raw:=inputFile [] leaders.bits candidate.bits last.bits (Encoding.vista.encode vista)
  let validated:=Function.update raw 1 [vista.valid]
  obtain ⟨validateTime,validateBound,a⟩:=prepareValidated_executes vista leaders candidate last
  change Executes prepareValidated _ validateTime validated at a
  obtain ⟨labelTime,labelBound,b⟩:=labelGuards_executes validated leaders candidate last
    (by simp [validated,raw,inputFile]) (by simp [validated,raw,inputFile])
    (by simp [validated,raw,inputFile]) (by simp [validated,raw,inputFile])
    (by simp [validated,raw,inputFile]) (by simp [validated,raw,inputFile])
    vista.valid [] (by simp [validated])
  let accepted:=((vista.valid && decide (0<leaders)) && decide (leaders≤candidate)) && decide (0<last)
  let checked:=Function.update raw 1 [accepted]
  have bResult : Function.update validated 1 [accepted]=checked := by simp [validated,checked]
  rw [bResult] at b
  obtain ⟨tableTime,tableBound,c⟩:=prepareTable_executes checked vista
    (by simp [checked,raw,inputFile]) accepted [] (by simp [checked])
    (by simp [checked,raw,inputFile]) (by simp [checked,raw,inputFile]) (by
      intro i member;fin_cases i <;> simp_all [checked,raw,inputFile,tableHeaderRoles])
  let prepared:=openingFile vista leaders candidate last accepted
  have cResult : tableFile checked vista=prepared := by
    funext r
    by_cases a:r=1 <;> by_cases b:r=17 <;> by_cases c:r=20 <;>
      simp [tableFile,checked,prepared,openingFile,raw,a,b,c]
  rw [cResult] at c
  let L:=(inputWord vista leaders candidate last).length+1
  have length:=inputWord_length vista leaders candidate last
  have positive : 1≤L := by dsimp only [L];omega
  have linear : L≤L^6 := Nat.le_self_pow (by decide) _
  have one : 1≤L^6 := Nat.one_le_pow _ _ positive
  have tableLimit : tableTime≤2000*L^6 := tableBound.trans
    (Nat.mul_le_mul_left 2000 ((Nat.pow_le_pow_left (by dsimp only [L];omega) 3).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have labels : labelTime≤50*L^6 := by
    have labelLength : leaders.size+candidate.size≤L := by dsimp only [L];omega
    omega
  change validateTime≤227000000*L^6 at validateBound
  cases acceptedEq:accepted with
  | false=>
    have outcome : openingAccepted vista leaders candidate last=false := by
      change (accepted && decide (last≤(vista.node vista.bottom).level))=false
      rw [acceptedEq];rfl
    have flag : prepared 1=[false] := by simp [prepared,openingFile,acceptedEq]
    have push:=pushBit_executes (1:Fin 52) false (Function.update prepared 1 [])
    have restored : Function.update (Function.update prepared 1 []) 1
        (false::Function.update prepared 1 [] 1)=prepared := by
      simp only [Function.update_self,Function.update_idem]
      rw [←flag,Function.update_eq_self]
    rw [restored] at push
    have d:=branch_executes_false (1:Fin 52) validDepthBranch (pushBit 1 false) prepared prepared [] 1 flag push
    have final : prepared=openingFile vista leaders candidate last (openingAccepted vista leaders candidate last) := by
      simp [prepared,acceptedEq,outcome]
    refine ⟨validateTime+1+(labelTime+1+(tableTime+1+(1+1))),?_,?_⟩
    · change validateTime+1+(labelTime+1+(tableTime+1+(1+1)))≤230000000*L^6
      omega
    · simpa only [final] using a.sequence (b.sequence (c.sequence d))
  | true=>
    have valid:vista.valid=true := by
      dsimp only [accepted] at acceptedEq
      simp only [Bool.and_eq_true,decide_eq_true_eq] at acceptedEq
      exact acceptedEq.1.1.1
    have flag : prepared 1=[true] := by simp [prepared,openingFile,acceptedEq]
    have push:=pushBit_executes (1:Fin 52) true (Function.update prepared 1 [])
    have restored : Function.update (Function.update prepared 1 []) 1
        (true::Function.update prepared 1 [] 1)=prepared := by
      simp only [Function.update_self,Function.update_idem]
      rw [←flag,Function.update_eq_self]
    rw [restored] at push
    obtain ⟨depthTime,depthBound,read⟩:=checkDepth_executes prepared vista valid true [] flag
      (by intro r small different;fin_cases r <;> simp_all [prepared,openingFile,tableFile,inputFile])
      (by simp [prepared,openingFile,tableFile,inputFile])
      (by simp [prepared,openingFile,tableFile,inputFile])
      (by simp [prepared,openingFile,tableFile,inputFile])
      (Encoding.natural.encode vista.bottom) (by simp [prepared,openingFile,tableFile])
      (by simp [prepared,openingFile,tableFile]) last (by simp [prepared,openingFile,tableFile,inputFile])
    have final : Function.update prepared 1 [true && decide (last≤(vista.node vista.bottom).level)]=
        openingFile vista leaders candidate last (openingAccepted vista leaders candidate last) := by
      have outcome : openingAccepted vista leaders candidate last=decide (last≤(vista.node vista.bottom).level) := by
        change (accepted && decide (last≤(vista.node vista.bottom).level))=_
        rw [acceptedEq];rfl
      simp [prepared,openingFile,outcome]
    rw [final] at read
    have d:=branch_executes_true (1:Fin 52) validDepthBranch (pushBit 1 false) prepared _ []
      (1+1+depthTime) flag (push.sequence read)
    have tableSize : (prepared 17).length≤(Encoding.vista.encode vista).length := by
      change (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length≤
        (Encoding.natural.encode vista.nodes.size++Encoding.sequence Encoding.node vista.nodes.toList++
          Encoding.natural.encode vista.bottom).length
      simp only [List.length_append]
      omega
    have depthLimit : depthTime≤10000*L^6 := depthBound.trans
      (Nat.mul_le_mul_left 10000 ((Nat.pow_le_pow_left (by dsimp only [L];omega) 4).trans
        (Nat.pow_le_pow_right positive (by decide))))
    refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
    change validateTime+1+(labelTime+1+(tableTime+1+(1+(1+1+depthTime))))≤230000000*L^6
    omega

end Counting.StackMachine.AuditPrefix
