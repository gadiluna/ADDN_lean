import Counting.StackAuditPropagationInput
import Counting.StackEncodingBoundedNatural

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def propagationRoundRoles : CountWorkspace 33 :=
  ⟨![2,41,3,4,5,6,7,8,9,10,13],by decide⟩

abbrev preparePropagationRounds : Routine 42 := sequence (ofProgram (ListPrograms.copyProgram 41 42 0 43))
  (sequence (frameRoutine 41 0 2 43)
    (sequence (ofProgram (ListPrograms.copyProgram 41 40 13 43))
      (sequence (boundedCount 33 propagationRoundRoles) (sequence (clear 2) (clear 7)))))

/-- A binary anchor is converted using the actual stored-node count as
budget. Even an excessive anchor never causes an unbounded unary expansion. -/
theorem preparePropagationRounds_executes (store : Store 42) (anchor n : Nat)
    (anchorAt : store 42=anchor.bits) (countAt : store 40=List.replicate n true)
    (empty : ∀ i : Fin 44,i∈({0,2,3,4,5,6,7,8,9,10,13,41,43}:Finset (Fin 44)) → store i=[]) :
    ∃ time ≤ 1000*(n+anchor.size+1)^3,
      Executes preparePropagationRounds store time
        (Function.update store 41 (List.replicate (min anchor n) true)) := by
  have a:=copy_executes 41 (42:Fin 44) 0 43 (by decide) (by decide) (by decide) store
    (empty _ (by decide))
  rw [anchorAt,empty 0 (by decide),List.append_nil] at a
  let copied:=Function.update store 0 anchor.bits
  have b:=frame_executes_updates 41 (0:Fin 44) 2 43 (by decide) (by decide) (by decide) copied
    (by simp [copied,empty 43 (by decide)])
  let framed:=Function.update store 2 (Encoding.natural.encode anchor)
  have bResult : Function.update (Function.update copied 0 []) 2
      (Encoding.frame (copied 0)++copied 2)=framed := by
    funext r
    by_cases a:r=0 <;> by_cases b:r=2 <;> simp [copied,framed,a,b,empty 0 (by decide),empty 2 (by decide),Encoding.natural]
  rw [bResult] at b
  change Executes _ copied (5*anchor.bits.length+4) framed at b
  have c:=copy_executes 41 (40:Fin 44) 13 43 (by decide) (by decide) (by decide) framed
    (by simp [framed,empty 43 (by decide)])
  have source : framed 40=List.replicate n true := by simp [framed,countAt]
  have target : framed 13=[] := by simp [framed,empty 13 (by decide)]
  rw [source,target,List.append_nil,List.length_replicate] at c
  let ready:=Function.update framed 13 (List.replicate n true)
  obtain ⟨time,bound,d⟩:=boundedNatural_executes 33 propagationRoundRoles ready anchor
    (by simp [ready,framed,propagationRoundRoles])
    (by simp [ready,framed,propagationRoundRoles,empty 41 (by decide)])
    (by intro i member;fin_cases i <;> simp_all [ready,framed,propagationRoundRoles])
  let counted:=Function.update (Function.update framed 41 (List.replicate (min anchor n) true)) 7
    [decide (anchor≤n)]
  have dResult : boundedNaturalResult 33 propagationRoundRoles ready anchor=counted := by
    funext r
    by_cases a:r=13 <;> by_cases b:r=41 <;> by_cases c:r=7 <;>
      simp [boundedNaturalResult,propagationRoundRoles,ready,framed,counted,a,b,c,
        empty 13 (by decide),empty 7 (by decide)]
  rw [dResult] at d
  have e:=clear_executes (2:Fin 44) counted
  let cleared:=Function.update (Function.update store 41 (List.replicate (min anchor n) true)) 7
    [decide (anchor≤n)]
  have eResult : Function.update counted 2 []=cleared := by
    funext r
    by_cases a:r=2 <;> by_cases b:r=41 <;> by_cases c:r=7 <;>
      simp [counted,framed,cleared,a,b,c,empty 2 (by decide)]
  rw [eResult] at e
  change Executes _ counted ((Encoding.natural.encode anchor).length+1) cleared at e
  have f:=clear_executes (7:Fin 44) cleared
  have fResult : Function.update cleared 7 []=Function.update store 41 (List.replicate (min anchor n) true) := by
    funext r
    by_cases a:r=7 <;> by_cases b:r=41 <;> simp [cleared,a,b,empty 7 (by decide)]
  rw [fResult] at f
  change Executes _ cleared 2 _ at f
  change time ≤ 64*((List.replicate n true).length+(Encoding.natural.encode anchor).length+1)^3 at bound
  simp only [List.length_replicate,Encoding.natural_length] at bound
  have raised:=bound.trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left
    (by omega : n+(2*anchor.size+1)+1 ≤ 2*(n+anchor.size+1)) 3))
  have linear : n+anchor.size+1 ≤ (n+anchor.size+1)^3 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence (e.sequence f))))⟩
  simp only [Encoding.bits_length,Encoding.natural_length]
  nlinarith only [raised,linear,Nat.zero_le n,Nat.zero_le anchor.size]

theorem preparePropagationRounds_setup (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    ∃ time ≤ 1000*(vista.nodes.size+anchor.size+1)^3,
      Executes preparePropagationRounds (propagationSetupFile anchor vista values) time
        (Function.update (propagationSetupFile anchor vista values) 41 (List.replicate anchor true)) := by
  simpa only [Nat.min_eq_left fits] using
    preparePropagationRounds_executes (propagationSetupFile anchor vista values) anchor vista.nodes.size
      (by simp [propagationSetupFile,propagationInputFile])
      (by simp [propagationSetupFile]) (by
        intro r member;fin_cases r <;> simp_all [propagationSetupFile,propagationInputFile])

end Counting.StackMachine.AuditPropagation
