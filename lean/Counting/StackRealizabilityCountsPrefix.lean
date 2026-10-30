import Counting.StackRealizabilityCountsLoop
import Counting.StackEncodingListReadHeader
import Counting.StackEncodingParserMany

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def countsHeaderRoles : FullListWorkspace 4:=⟨![17,1,0,4,18,5,8,9,6,10,11,7,12,13,14,15,16],by decide⟩

def countsPrefix : Routine 19:=sequence (readListHeader 4 countsHeaderRoles)
  (sequence (ofProgram (ListPrograms.copyProgram 18 18 0 4)) (forEach 18 countItem))

def countsPrefixStore (store : Store 19) (accepted : Bool) (tail suffix : List Bool)
    (total : Nat) (values : List Nat) : Store 19:=
  Function.update (Function.update (Function.update (Function.update store 17 suffix)
    0 (List.replicate values.length true)) 19 (total+values.sum).bits)
      1 ((accepted && positiveCounts values)::tail)

/-- The unary count is the number of explicitly serialized entries, never
the magnitude of a population count. It is bounded by the input length. -/
theorem countsPrefix_executes (store : Store 19) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 21,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e20 : store 20=[])
    (total : Nat) (accumulator : store 19=total.bits) (values : List Nat) (suffix : List Bool)
    (input : store 17=(Encoding.list Encoding.natural).encode values++suffix) :
    ∃ time ≤ 2000*((store 17).length+total.size+1)^3,
      Executes countsPrefix store time (countsPrefixStore store accepted tail suffix total values):=by
  have positive (value : Nat) : 0<(Encoding.natural.encode value).length:=by
    simp only [Encoding.natural_length];omega
  have headerWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (countsHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [countsHeaderRoles,work,e18]
  obtain ⟨headerTime,headerBound,headerRun⟩:=readListHeader_canonical 4 countsHeaderRoles store accepted tail
    status headerWork Encoding.natural positive values suffix input
  let ready:=Function.update (Function.update store 17 (Encoding.sequence Encoding.natural values++suffix))
    18 (List.replicate values.length true)
  have copying:=copy_executes 18 18 0 4 (by decide) (by decide) (by decide) ready (by simp [ready,work])
  have count : ready 18=List.replicate values.length true:=by simp [ready]
  have empty : ready 0=[]:=by simp [ready,work]
  rw [count,empty,List.append_nil,List.length_replicate] at copying
  let copied:=Function.update ready 0 (List.replicate values.length true)
  obtain ⟨loopTime,loopBound,loopRun⟩:=countValues_executes copied accepted tail
    (by simp [copied,ready,status]) (by simp [copied,ready,work]) (by simp [copied,ready,work])
    (by simp [copied,ready,work]) (by simp [copied,ready,e20]) total (by simp [copied,ready,accumulator])
    values suffix (by simp [copied,ready]) (List.replicate values.length true)
    (by simp [copied,ready]) (by simp)
  have final : countValuesStore copied accepted tail suffix total values=countsPrefixStore store accepted tail suffix total values:=by
    funext r
    by_cases r0 : r=0 <;> by_cases r1 : r=1 <;> by_cases r17 : r=17 <;> by_cases r18 : r=18 <;>
      by_cases r19 : r=19 <;>
      simp [countValuesStore,countsPrefixStore,copied,ready,r0,r1,r17,r18,r19,e18]
  rw [final] at loopRun
  have shorter : (copied 17).length≤(store 17).length:=by
    rw [input]
    change (Encoding.sequence Encoding.natural values++suffix).length≤
      ((Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values)++suffix).length
    simp only [List.length_append]
    omega
  have countBound : values.length≤(store 17).length:=by
    have count:=VerifiedParser.sequence_count_le positive values
    rw [input]
    change values.length≤((Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values)++suffix).length
    simp only [List.length_append]
    omega
  let S:=(store 17).length+total.size+1
  have spos : 1≤S:=by dsimp only [S];omega
  have countS : values.length≤S:=by dsimp only [S];omega
  have inputS : (copied 17).length+total.size+1≤S:=by dsimp only [S];omega
  have loopLimit : loopTime≤40*S^2+2*S+1:=by
    have bounded : loopTime≤S*(40*S+2)+1:=loopBound.trans (by gcongr)
    nlinarith
  change headerTime≤1820*((store 17).length+1)^3 at headerBound
  have headerLimit : headerTime≤1820*S^3:=by apply headerBound.trans;gcongr;dsimp only [S];omega
  have square : S^2≤S^3:=Nat.pow_le_pow_right spos (by decide)
  have linear : S≤S^3:=Nat.le_self_pow (by decide) _
  have one : 1≤S^3:=Nat.one_le_pow _ _ spos
  exact ⟨headerTime+1+(5*values.length+2+1+loopTime),by change _≤2000*S^3;omega,
    headerRun.sequence (copying.sequence loopRun)⟩

end Counting.StackMachine.RealizabilityCheck
