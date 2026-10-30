import Counting.StackAuditPrefixOpening
import Counting.StackAuditPrefixRounds
import Counting.StackAuditPrefixWidth

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def rootAccepted (vista : Executable.Vista) (candidate : Nat) : Bool :=
  (Executable.levelNodes vista 0).any (fun i=>(vista.node i).leader) &&
    decide ((Executable.levelNodes vista 0).length≤candidate)

def loopSeed (vista : Executable.Vista) (leaders candidate last : Nat) : Store 50 :=
  Function.update (Function.update (Function.update (Function.update
    (openingFile vista leaders candidate last true) 21 candidate.bits)
      45 (List.replicate last true)) 1 [rootAccepted vista candidate]) 30 [true]

abbrev prepareActive : Routine 50 := sequence (ofProgram (ListPrograms.copyProgram 49 38 21 51))
  (sequence prepareRounds (sequence rootLeaderGuard (sequence widthGuard (pushBit 30 true))))

/-- Prepare the outer scan with paid copies and bounded conversion; test
root leader presence and level-zero width before advancing the child-level
query to one. The saved optional anchor starts as the empty zero payload. -/
theorem prepareActive_executes (vista : Executable.Vista) (leaders candidate last : Nat)
    (fits : last≤vista.nodes.size) :
    ∃ time ≤ 60000*((inputWord vista leaders candidate last).length+1)^5,
      Executes prepareActive (openingFile vista leaders candidate last true) time
        (loopSeed vista leaders candidate last) := by
  let initial:=openingFile vista leaders candidate last true
  have a:=copy_executes 49 (38:Fin 52) 21 51 (by decide) (by decide) (by decide) initial
    (by simp [initial,openingFile,tableFile,inputFile])
  have source : initial 38=candidate.bits := by simp [initial,openingFile,tableFile,inputFile]
  have target : initial 21=[] := by simp [initial,openingFile,tableFile,inputFile]
  rw [source,target,List.append_nil] at a
  let copied:=Function.update initial 21 candidate.bits
  obtain ⟨roundTime,roundBound,b⟩:=prepareRounds_executes copied last vista.nodes.size
    (by simp [copied,initial,openingFile,tableFile,inputFile])
    (by simp [copied,initial,openingFile,tableFile]) (by
      intro i member;fin_cases i <;> simp_all [copied,initial,openingFile,tableFile,inputFile])
  rw [Nat.min_eq_left fits] at b
  let ready:=Function.update copied 45 (List.replicate last true)
  have readyWork (r:Fin 52) (small:r.val<17) (different:r≠1) : ready r=[] := by
    fin_cases r <;> simp_all [ready,copied,initial,openingFile,tableFile,inputFile]
  obtain ⟨leaderTime,leaderBound,c⟩:=rootLeaderGuard_executes ready vista true []
    (by simp [ready,copied,initial,openingFile]) readyWork
    (by simp [ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [ready,copied,initial,openingFile,tableFile,inputFile])
    (Encoding.natural.encode vista.bottom) (by simp [ready,copied,initial,openingFile,tableFile])
    (by simp [ready,copied,initial,openingFile,tableFile])
  simp only [Bool.true_and] at c
  let hasLeader:=(Executable.levelNodes vista 0).any (fun i=>(vista.node i).leader)
  let leaderChecked:=Function.update ready 1 [hasLeader]
  have leaderWork (r:Fin 52) (small:r.val<17) (different:r≠1) : leaderChecked r=[] := by
    simp [leaderChecked,different,readyWork r small different]
  obtain ⟨widthTime,widthBound,d⟩:=widthGuard_executes leaderChecked vista 0 candidate hasLeader []
    (by simp [leaderChecked]) leaderWork
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile])
    (Encoding.natural.encode vista.bottom) (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile])
    (by simp [leaderChecked,ready,copied,initial,openingFile,tableFile,inputFile,Nat.bits])
    (by simp [leaderChecked,ready,copied])
  let checked:=Function.update ready 1 [rootAccepted vista candidate]
  have dResult : Function.update leaderChecked 1
      [hasLeader && decide ((Executable.levelNodes vista 0).length≤candidate)]=checked := by
    simp [leaderChecked,checked,rootAccepted,hasLeader]
  rw [dResult] at d
  have e:=pushBit_executes (30:Fin 52) true checked
  have empty30 : checked 30=[] := by simp [checked,ready,copied,initial,openingFile,tableFile,inputFile]
  rw [empty30] at e
  change Executes _ checked 1 (loopSeed vista leaders candidate last) at e
  let table:=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom
  have tableReady : ready 17=table := by simp [ready,copied,initial,openingFile,tableFile,table]
  have tableChecked : leaderChecked 17=table := by simp [leaderChecked,tableReady]
  rw [tableReady] at leaderBound
  rw [tableChecked] at widthBound
  simp only [Nat.size_zero,Nat.add_zero] at widthBound
  have tableLength : table.length≤(Encoding.vista.encode vista).length := by
    change table.length≤(Encoding.natural.encode vista.nodes.size++
      Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length
    dsimp only [table]
    simp only [List.length_append];omega
  have nodes:=Encoding.vista_nodes_le_length vista
  have length:=inputWord_length vista leaders candidate last
  let L:=(inputWord vista leaders candidate last).length+1
  have positive:1≤L := by dsimp only [L];omega
  have linear:L≤L^5:=Nat.le_self_pow (by decide) _
  have one:1≤L^5:=Nat.one_le_pow _ _ positive
  have roundLimit:roundTime≤1000*L^5:=roundBound.trans
    (Nat.mul_le_mul_left 1000 ((Nat.pow_le_pow_left (by dsimp only [L];omega) 3).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have leaderLimit:leaderTime≤21000*L^5:=leaderBound.trans
    (Nat.mul_le_mul_left 21000 (Nat.pow_le_pow_left (by dsimp only [L];omega) 5))
  have widthLimit:widthTime≤31000*L^5:=widthBound.trans
    (Nat.mul_le_mul_left 31000 (Nat.pow_le_pow_left (by dsimp only [L];omega) 5))
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  simp only [Encoding.bits_length]
  change 5*candidate.size+2+1+(roundTime+1+(leaderTime+1+(widthTime+1+1)))≤60000*L^5
  have candidateSize:candidate.size≤L := by dsimp only [L];omega
  omega

end Counting.StackMachine.AuditPrefix
