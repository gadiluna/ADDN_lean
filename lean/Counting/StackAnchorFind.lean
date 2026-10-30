import Counting.StackAnchorFindLoop
import Counting.StackEncodingListReadHeader
import Counting.StackRegisterFrames
import Counting.EncodingDag

namespace Counting.StackMachine.AnchorFind
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- The canonical incoming list is consumed, its suffix remains in cell0,
and the query in cell17 is preserved. Cells1–16 and19–20 are workspace. -/
def bank (input query result pending counter flag : List Bool) : Store 19 :=
  fun r=>if r=0 then input else if r=17 then query else if r=18 then result
    else if r=19 then pending else if r=20 then counter else if r=1 then flag else []

def headerRoles : Fin 17 ↪ Fin 21 := ⟨![0,1,2,3,20,5,6,7,8,9,10,11,12,13,14,15,16],by decide⟩
def loopRoles : Fin 13 ↪ Fin 21 := ⟨![0,17,2,3,18,19,6,7,8,9,10,11,20],by decide⟩
abbrev initializeFlags : Routine 19 := sequence (pushBit 1 true) (pushBit 19 true)
abbrev readHeader : Routine 19 := readListHeader 4 headerRoles
abbrev lookup : Routine 19 := sequence initializeFlags
  (sequence readHeader (sequence (relocate loop loopRoles) (sequence (clear 19) (clear 1))))

theorem initializeFlags_executes (input query : List Bool) :
    Executes initializeFlags (bank input query [] [] [] []) 3 (bank input query [] [true] [] [true]) := by
  have first := pushBit_executes (1:Fin 21) true (bank input query [] [] [] [])
  have firstStore : Function.update (bank input query [] [] [] []) 1 [true]=bank input query [] [] [] [true] := by
    funext r;fin_cases r <;> simp [bank]
  change Executes _ _ 1 (Function.update (bank input query [] [] [] []) 1 [true]) at first
  rw [firstStore] at first
  have second := pushBit_executes (19:Fin 21) true (bank input query [] [] [] [true])
  have secondStore : Function.update (bank input query [] [] [] [true]) 19 [true]=bank input query [] [true] [] [true] := by
    funext r;fin_cases r <;> simp [bank]
  change Executes _ _ 1 (Function.update (bank input query [] [] [] [true]) 19 [true]) at second
  rw [secondStore] at second
  exact first.sequence second

theorem readHeader_executes (edges : List (Nat×Nat)) (suffix query : List Bool) :
    ∃ time  ≤ 1820*(((Encoding.list edgeCodec).encode edges++suffix).length+1)^3,
      Executes readHeader (bank ((Encoding.list edgeCodec).encode edges++suffix) query [] [true] [] [true]) time
        (bank (Encoding.sequence edgeCodec edges++suffix) query [] [true] (List.replicate edges.length true) [true]) := by
  obtain ⟨time,bounded,ran⟩ := readListHeader_canonical 4 headerRoles
    (bank ((Encoding.list edgeCodec).encode edges++suffix) query [] [true] [] [true]) true [] rfl
    (by intro i member;fin_cases i <;> simp_all [headerRoles,bank]) edgeCodec
    (by intro edge;simp [edgeCodec,Encoding.product,Encoding.natural,Encoding.frame_length])
    edges suffix rfl
  have same : Function.update (Function.update
      (bank ((Encoding.list edgeCodec).encode edges++suffix) query [] [true] [] [true]) 0
      (Encoding.sequence edgeCodec edges++suffix)) 20 (List.replicate edges.length true)=
      bank (Encoding.sequence edgeCodec edges++suffix) query [] [true] (List.replicate edges.length true) [true] := by
    funext r;fin_cases r <;> simp [bank]
  change Executes _ _ _ (Function.update (Function.update
      (bank ((Encoding.list edgeCodec).encode edges++suffix) query [] [true] [] [true]) 0
      (Encoding.sequence edgeCodec edges++suffix)) 20 (List.replicate edges.length true)) at ran
  rw [same] at ran
  exact ⟨time,bounded,ran⟩

private theorem edge_count_le (edges : List (Nat×Nat)) :
    edges.length ≤ (Encoding.sequence edgeCodec edges).length := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
    have positive : 0<(edgeCodec.encode edge).length := by
      simp [edgeCodec,Encoding.product,Encoding.natural,Encoding.frame_length]
    simp only [Encoding.sequence,List.length_append,List.length_cons]
    omega

theorem lookup_executes (edges : List (Nat×Nat)) (query : Nat) (suffix : List Bool) :
    ∃ time  ≤  5000*(((Encoding.list edgeCodec).encode edges++suffix).length+query.size+1)^3,
      Executes lookup (bank ((Encoding.list edgeCodec).encode edges++suffix) query.bits [] [] [] []) time
        (bank suffix query.bits
          (((edges.find? (fun edge=>edge.1==query)).map Prod.snd).getD 0).bits [] [] []) := by
  let input := (Encoding.list edgeCodec).encode edges++suffix
  let source := Encoding.sequence edgeCodec edges++suffix
  have inputLength : input.length=2*edges.length.size+1+source.length := by
    simp [input,source,Encoding.list,Encoding.natural,Encoding.frame_length,Encoding.bits_length,Nat.add_assoc]
  have before := initializeFlags_executes input query.bits
  obtain ⟨headerTime,headerBound,headerRun⟩ := readHeader_executes edges suffix query.bits
  obtain ⟨loopTime,loopBound,loopRun⟩ := loop_executes query.bits edges suffix true []
    (List.replicate edges.length true) (by simp) input.length (by change source.length ≤ input.length;omega) (by simp)
  let finish := search query.bits edges true []
  have lifted : Executes (relocate loop loopRoles)
      (bank source query.bits [] [true] (List.replicate edges.length true) [true]) loopTime
      (bank suffix query.bits finish.2 [finish.1] [] [true]) := by
    apply relocate_executes_frame loop loopRoles _ _ _ _ loopTime _ _ _ loopRun
    · funext r;fin_cases r <;> simp [bank,file,loopRoles,source]
    · intro r;fin_cases r <;> simp [bank,file,loopRoles,finish]
    · intro r outside
      have n0 : r≠0 := by intro eq;subst r;exact outside 0 rfl
      have n18 : r≠18 := by intro eq;subst r;exact outside 4 rfl
      have n19 : r≠19 := by intro eq;subst r;exact outside 5 rfl
      have n20 : r≠20 := by intro eq;subst r;exact outside 12 rfl
      simp [bank,n0,n18,n19,n20]
  have erasePending := clear_executes (19:Fin 21) (bank suffix query.bits finish.2 [finish.1] [] [true])
  have pendingStore : Function.update (bank suffix query.bits finish.2 [finish.1] [] [true]) 19 []=
      bank suffix query.bits finish.2 [] [] [true] := by funext r;fin_cases r <;> simp [bank]
  rw [pendingStore] at erasePending
  have eraseFlag := clear_executes (1:Fin 21) (bank suffix query.bits finish.2 [] [] [true])
  have flagStore : Function.update (bank suffix query.bits finish.2 [] [] [true]) 1 []=
      bank suffix query.bits finish.2 [] [] [] := by funext r;fin_cases r <;> simp [bank]
  rw [flagStore] at eraseFlag
  have result : finish.2=(((edges.find? (fun edge=>edge.1==query)).map Prod.snd).getD 0).bits := by
    dsimp only [finish]
    rw [search_find]
    cases found : edges.find? (fun edge=>edge.1==query) <;> simp
  have composed := before.sequence (headerRun.sequence (lifted.sequence (erasePending.sequence eraseFlag)))
  rw [result] at composed
  refine ⟨_,?_,composed⟩
  change 3+1+(headerTime+1+(loopTime+1+(2+1+2))) ≤  _
  change headerTime ≤ 1820*(input.length+1)^3 at headerBound
  have count := edge_count_le edges
  have countBound : edges.length ≤ input.length := by
    have sourceLength : source.length=(Encoding.sequence edgeCodec edges).length+suffix.length := List.length_append
    omega
  rw [Encoding.bits_length] at loopBound
  have headerRaised : headerTime ≤ 1820*(input.length+query.size+1)^3 := headerBound.trans (by gcongr;omega)
  have linear : input.length+query.size+1 ≤ (input.length+query.size+1)^3 := Nat.le_self_pow (by decide) _
  have square : (input.length+query.size+1)^2 ≤ (input.length+query.size+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have loopRaised : loopTime ≤  202*(input.length+query.size+1)^2+1 := by nlinarith
  nlinarith

/-- Exact `Executable.countFrom` correspondence on arbitrary canonical
incoming lists, without sortedness, positivity or uniqueness hypotheses. -/
theorem lookup_countFrom (node : Executable.Node) (query : Nat) (suffix : List Bool) :
    ∃ time  ≤  5000*(((Encoding.list edgeCodec).encode node.incoming++suffix).length+query.size+1)^3,
      Executes lookup (bank ((Encoding.list edgeCodec).encode node.incoming++suffix) query.bits [] [] [] []) time
        (bank suffix query.bits (Executable.countFrom node query).bits [] [] []) :=
  lookup_executes node.incoming query suffix

end Counting.StackMachine.AnchorFind
