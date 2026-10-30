import Counting.StackAuditPrefixRoundBounds
import Counting.AuditPrefixRoundSpec

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

abbrev completeLoop : Routine 50 := forEach 45 prefixRound

theorem scanAnchor_bound (vista : Executable.Vista) (start count : Nat) (anchor : Option Nat)
    (bound : ∀ value∈anchor,value ≤ start) :
    ∀ value∈scanAnchor vista start count anchor,value ≤ start+count := by
  induction count generalizing start anchor with
  | zero=>simpa only [scanAnchor_zero,Nat.add_zero] using bound
  | succ count ih=>
    rw [scanAnchor_succ]
    simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      ih (start+1) (nextAnchor vista start anchor) (nextAnchor_bound vista start anchor bound)

/-- The complete bounded scan visits all requested levels. The persistent
anchor and status agree with the exact executable prefix specification. -/
theorem completeLoop_executes (vista : Executable.Vista) (valid : vista.valid=true)
    (leaders candidate last start count : Nat)
    (depth : last≤(vista.node vista.bottom).level) (fits : last≤vista.nodes.size)
    (within : start+count≤last) (accepted : Bool) (anchor : Option Nat)
    (saved : ∀ value∈anchor,value ≤ start) :
    ∃ time ≤ count*(50000000000*((inputWord vista leaders candidate last).length+1)^6+2)+1,
      Executes completeLoop
        (roundFile vista leaders candidate last start (List.replicate count true) accepted anchor) time
        (roundFile vista leaders candidate last (start+count) []
          (accepted && scanCheck vista candidate start count) (scanAnchor vista start count anchor)) := by
  induction count generalizing start accepted anchor with
  | zero=>
    let store:=roundFile vista leaders candidate last start [] accepted anchor
    have empty : store 45=[] := by simp [store,roundFile]
    obtain ⟨run,halt⟩:=repeat_empty (45:Fin 52) prefixRound store empty
    refine ⟨1,by simp,⟨1,store⟩,run,halt,?_⟩
    simp [store]
  | succ count ih=>
    let store:=roundFile vista leaders candidate last start (List.replicate (count+1) true) accepted anchor
    let popped:=roundFile vista leaders candidate last start (List.replicate count true) accepted anchor
    have consumed : Function.update store 45 (List.replicate count true)=popped := by
      funext r
      by_cases r1:r=1 <;> by_cases r46:r=46 <;> by_cases r45:r=45 <;>
        simp [store,popped,roundFile,r1,r46,r45]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=
      prefixRound_bounded vista valid leaders candidate last start depth (by omega) fits
        (List.replicate count true) accepted anchor saved
    have first:=repeat_iteration (45:Fin 52) prefixRound store true (List.replicate count true)
      (by simp [store,roundFile,List.replicate_succ]) bodyTime bodyFinish
      (by rw [consumed];exact bodyRun) bodyHalt
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih (start+1)
      (by omega) (accepted && roundCheck vista candidate start) (nextAnchor vista start anchor)
      (nextAnchor_bound vista start anchor saved)
    have final :
        roundFile vista leaders candidate last (start+1+count) []
          ((accepted && roundCheck vista candidate start) && scanCheck vista candidate (start+1) count)
          (scanAnchor vista (start+1) count (nextAnchor vista start anchor)) =
        roundFile vista leaders candidate last (start+(count+1)) []
          (accepted && scanCheck vista candidate start (count+1))
          (scanAnchor vista start (count+1) anchor) := by
      rw [scanCheck_succ,scanAnchor_succ,Bool.and_assoc]
      congr 1; omega
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · nlinarith only [bodyBound,tailBound]
    · rw [Machine.run_add,first,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.AuditPrefix
