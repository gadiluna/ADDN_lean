import Counting.StackAuditBalanceInput
import Counting.StackEncodingBoundedNatural
import Counting.StackRoutineFixedPrefix

namespace Counting.StackMachine.AuditBalance
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def balanceRoundRoles : CountWorkspace 39 :=
  ⟨![2,48,3,4,5,6,7,8,9,10,13],by decide⟩

abbrev prepareBalanceRounds : Routine 48 := sequence (ofProgram (ListPrograms.copyProgram 47 36 0 47))
  (sequence (frameRoutine 47 0 2 47)
    (sequence (ofProgram (ListPrograms.copyProgram 47 49 13 47))
      (sequence (boundedCount 39 balanceRoundRoles)
        (sequence (clear 2) (sequence (clear 7) (sequence (clear 36)
          (sequence (discardBit 48) (pushBit 22 true))))))))

/-- Read a bounded number of rounds from the binary anchor, then remove
the first skipped round. Even an excessive anchor causes no unary blowup. -/
theorem prepareBalanceRounds_executes (store : Store 48) (anchor n : Nat)
    (anchorAt : store 36=anchor.bits) (countAt : store 49=List.replicate n true)
    (empty : ∀ i : Fin 50,i∈({0,2,3,4,5,6,7,8,9,10,13,22,48,47}:Finset (Fin 50)) → store i=[]) :
    ∃ time ≤ 1200*(n+anchor.size+1)^3,
      Executes prepareBalanceRounds store time
        (Function.update (Function.update (Function.update store 36 []) 48
          (List.replicate (min anchor n-1) true)) 22 [true]) := by
  have a:=copy_executes 47 (36:Fin 50) 0 47 (by decide) (by decide) (by decide) store
    (empty _ (by decide))
  rw [anchorAt,empty 0 (by decide),List.append_nil] at a
  let copied:=Function.update store 0 anchor.bits
  have b:=frame_executes_updates 47 (0:Fin 50) 2 47 (by decide) (by decide) (by decide) copied
    (by simp [copied,empty 47 (by decide)])
  let framed:=Function.update store 2 (Encoding.natural.encode anchor)
  have bResult : Function.update (Function.update copied 0 []) 2
      (Encoding.frame (copied 0)++copied 2)=framed := by
    funext r
    by_cases a:r=0 <;> by_cases b:r=2 <;> simp [copied,framed,a,b,empty 0 (by decide),empty 2 (by decide),Encoding.natural]
  rw [bResult] at b
  change Executes _ copied (5*anchor.bits.length+4) framed at b
  have c:=copy_executes 47 (49:Fin 50) 13 47 (by decide) (by decide) (by decide) framed
    (by simp [framed,empty 47 (by decide)])
  have source : framed 49=List.replicate n true := by simp [framed,countAt]
  have target : framed 13=[] := by simp [framed,empty 13 (by decide)]
  rw [source,target,List.append_nil,List.length_replicate] at c
  let ready:=Function.update framed 13 (List.replicate n true)
  obtain ⟨time,bound,d⟩:=boundedNatural_executes 39 balanceRoundRoles ready anchor
    (by simp [ready,framed,balanceRoundRoles])
    (by simp [ready,framed,balanceRoundRoles,empty 48 (by decide)])
    (by intro i member;fin_cases i <;> simp_all [ready,framed,balanceRoundRoles])
  let counted:=Function.update (Function.update framed 48 (List.replicate (min anchor n) true)) 7
    [decide (anchor≤n)]
  have dResult : boundedNaturalResult 39 balanceRoundRoles ready anchor=counted := by
    funext r
    by_cases a:r=13 <;> by_cases b:r=48 <;> by_cases c:r=7 <;>
      simp [boundedNaturalResult,balanceRoundRoles,ready,framed,counted,a,b,c,
        empty 13 (by decide),empty 7 (by decide)]
  rw [dResult] at d
  have e:=clear_executes (2:Fin 50) counted
  let cleared:=Function.update (Function.update store 48 (List.replicate (min anchor n) true)) 7
    [decide (anchor≤n)]
  have eResult : Function.update counted 2 []=cleared := by
    funext r
    by_cases a:r=2 <;> by_cases b:r=48 <;> by_cases c:r=7 <;>
      simp [counted,framed,cleared,a,b,c,empty 2 (by decide)]
  rw [eResult] at e
  change Executes _ counted ((Encoding.natural.encode anchor).length+1) cleared at e
  have f:=clear_executes (7:Fin 50) cleared
  let unflagged:=Function.update store 48 (List.replicate (min anchor n) true)
  have fResult : Function.update cleared 7 []=unflagged := by
    funext r
    by_cases a:r=7 <;> by_cases b:r=48 <;> simp [cleared,unflagged,a,b,empty 7 (by decide)]
  rw [fResult] at f
  change Executes _ cleared 2 unflagged at f
  have g:=clear_executes (36:Fin 50) unflagged
  have anchorStill : unflagged 36=anchor.bits := by simp [unflagged,anchorAt]
  rw [anchorStill] at g
  let erased:=Function.update unflagged 36 []
  have h:=discardBit_executes (48:Fin 50) erased
  have tailEq : (erased 48).tail=List.replicate (min anchor n-1) true := by
    simp [erased,unflagged,List.tail_replicate]
  rw [tailEq] at h
  let decremented:=Function.update erased 48 (List.replicate (min anchor n-1) true)
  have i:=pushBit_executes (22:Fin 50) true decremented
  have levelEmpty : decremented 22=[] := by simp [decremented,erased,unflagged,empty 22 (by decide)]
  rw [levelEmpty] at i
  have result : Function.update decremented 22 [true]=
      Function.update (Function.update (Function.update store 36 []) 48
        (List.replicate (min anchor n-1) true)) 22 [true] := by
    funext r
    by_cases a:r=22 <;> by_cases b:r=36 <;> by_cases c:r=48 <;>
      simp [decremented,erased,unflagged,a,b,c]
  rw [result] at i
  change time ≤ 64*((List.replicate n true).length+(Encoding.natural.encode anchor).length+1)^3 at bound
  simp only [List.length_replicate,Encoding.natural_length] at bound
  have raised:=bound.trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left
    (by omega : n+(2*anchor.size+1)+1 ≤ 2*(n+anchor.size+1)) 3))
  have linear : n+anchor.size+1 ≤ (n+anchor.size+1)^3 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence (e.sequence (f.sequence (g.sequence (h.sequence i)))))))⟩
  simp only [Encoding.bits_length,Encoding.natural_length]
  nlinarith only [raised,linear,Nat.zero_le n,Nat.zero_le anchor.size]

end Counting.StackMachine.AuditBalance
