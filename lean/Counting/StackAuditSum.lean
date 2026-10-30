import Counting.StackRealizabilityCountsPrefix
import Counting.StackComparePreserving

namespace Counting.StackMachine.AuditSum
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def file (source candidate values count total flag : List Bool) : Store 22 :=
  fun r=>if r=17 then source else if r=21 then candidate else if r=22 then values
    else if r=0 then count else if r=19 then total else if r=1 then flag else []

def countsRoles : Fin 21 ↪ Fin 24 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b eq;exact Fin.ext (congrArg (fun i:Fin 24=>i.val) eq)⟩
def equalityRoles : Fin 6 ↪ Fin 24 := ⟨![19,21,1,2,3,4],by decide⟩

/-- The natural array and binary candidate are preserved for subsequent
propagation. Every entry is physically scanned and added in binary. -/
abbrev check : Routine 22 := sequence (pushBit 1 true)
  (sequence (ofProgram (ListPrograms.copyProgram 21 22 17 4))
    (sequence (relocate RealizabilityCheck.countsPrefix countsRoles)
      (sequence (Compare.preservingEquality 18 equalityRoles)
        (sequence (ofProgram (combineFlagsProgram 22 1))
          (sequence (clear 0) (clear 19))))))

def accepts (values : List Nat) (candidate : Nat) : Bool :=
  RealizabilityCheck.positiveCounts values && decide (values.sum=candidate)

private theorem sum_size (values : List Nat) :
    values.sum.size≤(Encoding.sequence Encoding.natural values).length := by
  induction values with
  | nil => decide
  | cons value values ih =>
    have bounded := RealizabilityCheck.nat_add_size_le value values.sum
    simp only [List.sum_cons,Encoding.sequence,List.length_append,Encoding.natural_length]
    omega

theorem check_executes (values : List Nat) (candidate : Nat) :
    ∃ time≤3000*(((Encoding.list Encoding.natural).encode values).length+candidate.size+1)^3,
      Executes check (file [] candidate.bits ((Encoding.list Encoding.natural).encode values) [] [] []) time
        (file [] candidate.bits ((Encoding.list Encoding.natural).encode values) [] [] [accepts values candidate]) := by
  let word := (Encoding.list Encoding.natural).encode values
  let start := file [] candidate.bits word [] [] []
  let flagged := file [] candidate.bits word [] [] [true]
  have a := pushBit_executes (1:Fin 24) true start
  have as' : Function.update start 1 (true::start 1)=flagged := by
    funext r;fin_cases r <;> simp [start,flagged,file]
  rw [as'] at a
  let copied := file word candidate.bits word [] [] [true]
  have b := copy_executes 21 (22:Fin 24) 17 4 (by decide) (by decide) (by decide) flagged rfl
  have bs : Function.update flagged 17 (flagged 22++flagged 17)=copied := by
    funext r;fin_cases r <;> simp [flagged,copied,file]
  rw [bs] at b
  change Executes _ flagged (5*word.length+2) copied at b
  let inner : Store 19 := fun r=>if r=17 then word else if r=1 then [true] else []
  obtain ⟨sumTime,sumBound,c0⟩ := RealizabilityCheck.countsPrefix_executes inner true [] rfl
    (by
      intro r bound ne
      have other : r≠17 := by intro equal;subst r;norm_num at bound
      simp [inner,ne,other])
    rfl rfl 0 rfl values [] (by simp [inner,word])
  let counted := file [] candidate.bits word (List.replicate values.length true) values.sum.bits
    [RealizabilityCheck.positiveCounts values]
  have c : Executes (relocate RealizabilityCheck.countsPrefix countsRoles) copied sumTime counted := by
    apply relocate_executes_frame RealizabilityCheck.countsPrefix countsRoles copied counted inner
      (RealizabilityCheck.countsPrefixStore inner true [] [] 0 values) sumTime _ _ _ c0
    · funext r;fin_cases r <;> simp [countsRoles,copied,file,inner]
    · intro r;fin_cases r <;> simp [countsRoles,counted,file,RealizabilityCheck.countsPrefixStore,inner]
    · intro r outside
      have bound : 21≤r.val := by
        by_contra h
        have small : r.val<21 := by omega
        exact outside ⟨r.val,small⟩ (Fin.ext rfl)
      have r0 : r≠0 := by intro eq;subst r;norm_num at bound
      have r1 : r≠1 := by intro eq;subst r;norm_num at bound
      have r17 : r≠17 := by intro eq;subst r;norm_num at bound
      have r19 : r≠19 := by intro eq;subst r;norm_num at bound
      simp [copied,counted,file,r0,r1,r17,r19]
  have d := Compare.preservingEquality_executes 18 equalityRoles counted rfl rfl rfl
  have first : counted (equalityRoles 0)=values.sum.bits := rfl
  have second : counted (equalityRoles 1)=candidate.bits := rfl
  have flag : counted (equalityRoles 2)=[RealizabilityCheck.positiveCounts values] := rfl
  rw [first,second,flag] at d
  have bitsEq : values.sum.bits=candidate.bits ↔ values.sum=candidate := by
    constructor
    · intro eq;simpa only [Encoding.value_bits] using congrArg Encoding.value eq
    · intro eq;rw [eq]
  simp only [bitsEq] at d
  let compared := file [] candidate.bits word (List.replicate values.length true) values.sum.bits
    [decide (values.sum=candidate),RealizabilityCheck.positiveCounts values]
  have ds : Function.update counted (equalityRoles 2)
      [decide (values.sum=candidate),RealizabilityCheck.positiveCounts values]=compared := by
    funext r;fin_cases r <;> simp [equalityRoles,counted,compared,file]
  rw [ds] at d
  let joined := file [] candidate.bits word (List.replicate values.length true) values.sum.bits [accepts values candidate]
  have e := combineFlags_executes 22 (1:Fin 24) compared
    (RealizabilityCheck.positiveCounts values) (decide (values.sum=candidate)) [] rfl
  have es : Function.update compared 1 [accepts values candidate]=joined := by
    funext r;fin_cases r <;> simp [compared,joined,file]
  change Executes _ _ 3 (Function.update compared 1 [accepts values candidate]) at e
  rw [es] at e
  let noCount := file [] candidate.bits word [] values.sum.bits [accepts values candidate]
  have f := clear_executes (0:Fin 24) joined
  have fs : Function.update joined 0 []=noCount := by
    funext r;fin_cases r <;> simp [joined,noCount,file]
  have countAt : joined 0=List.replicate values.length true := rfl
  rw [countAt,List.length_replicate] at f
  rw [fs] at f
  have g := clear_executes (19:Fin 24) noCount
  have gs : Function.update noCount 19 []=file [] candidate.bits word [] [] [accepts values candidate] := by
    funext r;fin_cases r <;> simp [noCount,file]
  change Executes _ _ (values.sum.bits.length+1) _ at g
  rw [gs] at g
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence (e.sequence (f.sequence g)))))⟩
  have sumLength := sum_size values
  have countLength := VerifiedParser.sequence_count_le (codec:=Encoding.natural)
    (fun value=>by rw [Encoding.natural_length];omega) values
  have sequenceLength : (Encoding.sequence Encoding.natural values).length≤word.length := by
    change _≤(Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values).length
    rw [List.length_append];omega
  have compareCost := Compare.preservingCost_le values.sum.bits candidate.bits
  simp only [Encoding.bits_length] at compareCost ⊢
  change sumTime≤2000*(word.length+1)^3 at sumBound
  let size := word.length+candidate.size+1
  have raised : (word.length+1)^3≤size^3 := Nat.pow_le_pow_left (by dsimp only [size];omega) 3
  have linear : size≤size^3 := Nat.le_self_pow (by decide) _
  have one : 1≤size^3 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
  change _≤3000*size^3
  have wordSize : word.length≤size := by dsimp only [size];omega
  have candidateSize : candidate.size≤size := by dsimp only [size];omega
  omega

end Counting.StackMachine.AuditSum
