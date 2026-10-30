import Counting.StackAnchorMatrixBank
import Counting.StackBinaryPredecessor
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.AnchorMatrix
set_option maxHeartbeats 2000000
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def inputWord (anchor leaders : Nat) (vista : Executable.Vista) : List Bool :=
  Encoding.natural.encode anchor++Encoding.natural.encode leaders++Encoding.vista.encode vista

def inputFile (input anchor leaders previous table count outer flag : List Bool) : Store 48 :=
  fun r=>if r=0 then input else if r=34 then anchor else if r=49 then leaders
    else if r=41 then previous else if r=40 then table else if r=45 then count
    else if r=48 then outer else if r=1 then flag else []

def inputHeaderRoles : FullListWorkspace 33 :=
  ⟨![0,1,2,3,45,4,5,6,7,8,9,10,11,12,13,14,15],by decide⟩
def predecessorRoles : Binary.PredWorkspace 42 := ⟨![34,41,2,3,4,5,6,7],by decide⟩

abbrev prepareInput : Routine 48 := sequence (ofProgram (unframeProgram 47 0 34 39))
  (sequence (ofProgram (unframeProgram 47 0 49 39))
    (sequence (pushBit 1 true) (sequence (readListHeader 33 inputHeaderRoles)
      (sequence (clear 1) (sequence (Binary.predecessor 42 predecessorRoles)
        (sequence (ofProgram (ListPrograms.copyProgram 47 0 40 39))
          (ofProgram (ListPrograms.copyProgram 47 45 48 39))))))))

/-- Both external parameters stay binary. The sole unary input count comes
from the number of actual stored DAG nodes, checked against the source. -/
theorem initialize_executes (anchor leaders : Nat) (vista : Executable.Vista) :
    ∃ time ≤ 2000*((inputWord anchor leaders vista).length+1)^3,
      Executes prepareInput (inputFile (inputWord anchor leaders vista) [] [] [] [] [] [] []) time
        (bank (AnchorRow.file (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
            [] anchor.bits [] [] [] [] [] [])
          (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
          (anchor-1).bits [] (List.replicate vista.nodes.size true) [] []
          (List.replicate vista.nodes.size true) leaders.bits) := by
  let code := Encoding.vista.encode vista
  let table := Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom
  let count := List.replicate vista.nodes.size true
  let initial := inputFile (inputWord anchor leaders vista) [] [] [] [] [] [] []
  let first := inputFile (Encoding.natural.encode leaders++code) anchor.bits [] [] [] [] [] []
  have a := unframe_canonical_executes 47 (0:Fin 50) 34 39 (by decide) (by decide) (by decide)
    initial anchor.bits (Encoding.natural.encode leaders++code)
    (by simp [initial,inputFile,inputWord,Encoding.natural,code,List.append_assoc]) rfl
  have as' : Function.update (Function.update initial 0 (Encoding.natural.encode leaders++code)) 34
      (anchor.bits++initial 34)=first := by
    funext r;fin_cases r <;> simp [initial,first,inputFile]
  rw [as'] at a
  let parameters := inputFile code anchor.bits leaders.bits [] [] [] [] []
  have b := unframe_canonical_executes 47 (0:Fin 50) 49 39 (by decide) (by decide) (by decide)
    first leaders.bits code rfl rfl
  have bs : Function.update (Function.update first 0 code) 49 (leaders.bits++first 49)=parameters := by
    funext r;fin_cases r <;> simp [first,parameters,inputFile]
  rw [bs] at b
  let ready := inputFile code anchor.bits leaders.bits [] [] [] [] [true]
  have c := pushBit_executes (1:Fin 50) true parameters
  have cs : Function.update parameters 1 (true::parameters 1)=ready := by
    funext r;fin_cases r <;> simp [parameters,ready,inputFile]
  rw [cs] at c
  obtain ⟨headerTime,headerBound,d⟩ := readListHeader_canonical 33 inputHeaderRoles ready true [] rfl
    (by intro i member;fin_cases i <;> simp_all [ready,inputFile,inputHeaderRoles])
    Encoding.node (by intro node;rw [Encoding.node_length];unfold Encoding.nodeBits;omega)
    vista.nodes.toList (Encoding.natural.encode vista.bottom) rfl
  let counted := inputFile table anchor.bits leaders.bits [] [] count [] [true]
  have ds : Function.update (Function.update ready (inputHeaderRoles 0)
      (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom))
      (inputHeaderRoles 4) (List.replicate vista.nodes.toList.length true)=counted := by
    funext r;fin_cases r <;> simp [ready,counted,inputFile,inputHeaderRoles,table,count]
  rw [ds] at d
  let cleared := inputFile table anchor.bits leaders.bits [] [] count [] []
  have e := clear_executes (1:Fin 50) counted
  have es : Function.update counted 1 []=cleared := by
    funext r;fin_cases r <;> simp [counted,cleared,inputFile]
  rw [es] at e
  change Executes _ counted 2 cleared at e
  obtain ⟨predTime,predBound,f⟩ := Binary.predecessor_executes 42 predecessorRoles cleared anchor rfl
    (by intro i member;fin_cases i <;> simp_all [cleared,inputFile,predecessorRoles])
  let previous := inputFile table anchor.bits leaders.bits (anchor-1).bits [] count [] []
  have fs : Function.update cleared (predecessorRoles 1) (anchor-1).bits=previous := by
    funext r;fin_cases r <;> simp [cleared,previous,inputFile,predecessorRoles]
  rw [fs] at f
  let copied := inputFile table anchor.bits leaders.bits (anchor-1).bits table count [] []
  have g := copy_executes 47 (0:Fin 50) 40 39 (by decide) (by decide) (by decide) previous rfl
  have gs : Function.update previous 40 (previous 0++previous 40)=copied := by
    funext r;fin_cases r <;> simp [previous,copied,inputFile]
  rw [gs] at g
  change Executes _ previous (5*table.length+2) copied at g
  let final := bank (AnchorRow.file table [] anchor.bits [] [] [] [] [] []) table (anchor-1).bits [] count [] [] count leaders.bits
  have h := copy_executes 47 (45:Fin 50) 48 39 (by decide) (by decide) (by decide) copied rfl
  have hs : Function.update copied 48 (copied 45++copied 48)=final := by
    funext r;fin_cases r <;> simp [copied,final,inputFile,bank,AnchorRow.file]
  rw [hs] at h
  change Executes _ copied (5*count.length+2) final at h
  have composed := a.sequence (b.sequence (c.sequence (d.sequence (e.sequence (f.sequence (g.sequence h))))))
  refine ⟨_,?_,composed⟩
  have inputLength : (inputWord anchor leaders vista).length=2*anchor.size+1+(2*leaders.size+1)+code.length := by
    simp [inputWord,code,List.length_append,Encoding.natural_length];omega
  have codeEq : code=Encoding.natural.encode vista.nodes.toList.length++table := by
    simp [code,table,Encoding.vista,Encoding.transport,Encoding.product,Encoding.list,List.append_assoc]
  have tableLength : table.length ≤ code.length := by
    rw [codeEq]
    simp only [List.length_append];omega
  have nodesLength : vista.nodes.size ≤ code.length := by
    have bound := AnchorRow.nodes_length vista.nodes.toList
    simp only [Array.length_toList] at bound
    have bound' : (Encoding.sequence Encoding.node vista.nodes.toList).length ≤ table.length := by
      simp only [table,List.length_append];omega
    omega
  have codeBound : code.length+1 ≤ (inputWord anchor leaders vista).length+1 := by omega
  have raised := headerBound.trans (Nat.mul_le_mul_left 1820 (Nat.pow_le_pow_left codeBound 3))
  have linear : (inputWord anchor leaders vista).length+1 ≤ ((inputWord anchor leaders vista).length+1)^3 :=
    Nat.le_self_pow (by decide) _
  simp only [Encoding.bits_length,count,List.length_replicate]
  omega

theorem inputWord_codec (anchor leaders : Nat) (vista : Executable.Vista) :
    inputWord anchor leaders vista=
      (Encoding.product Encoding.natural (Encoding.product Encoding.natural Encoding.vista)).encode (anchor,leaders,vista) := by
  simp [inputWord,Encoding.product,List.append_assoc]

end Counting.StackMachine.AnchorMatrix
