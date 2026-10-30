import Counting.StackAuditPrefixSetup
import Counting.StackAuditPrefixChildAll
import Counting.StackAuditPrefixSave
import Counting.AuditPrefixLastMatch

namespace Counting.StackMachine.AuditPrefix
open Routine

def anchorCode (anchor : Option Nat) : Nat := anchor.map (·+1) |>.getD 0

theorem anchorCode_le {anchor : Option Nat} {level : Nat}
    (bound : ∀ value∈anchor,value≤level) : anchorCode anchor≤level+1 := by
  cases anchor with
  | none=>simp [anchorCode]
  | some value=>have := bound value rfl;simp [anchorCode];omega

def roundFile (vista : Executable.Vista) (leaders candidate last level : Nat)
    (remaining : List Bool) (accepted : Bool) (anchor : Option Nat) : Store 50 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (openingFile vista leaders candidate last accepted) 21 candidate.bits)
      30 (level+1).bits) 41 level.bits) 45 remaining) 46 (anchorCode anchor).bits) 1 [accepted]

theorem loopSeed_eq_roundFile (vista : Executable.Vista) (leaders candidate last : Nat) :
    loopSeed vista leaders candidate last=roundFile vista leaders candidate last 0
      (List.replicate last true) (rootAccepted vista candidate) none := by
  funext r
  fin_cases r <;> simp [loopSeed,roundFile,openingFile,tableFile,inputFile,anchorCode,Nat.bits]

def roundCheck (vista : Executable.Vista) (candidate level : Nat) : Bool :=
  decide ((Executable.levelNodes vista (level+1)).length≤candidate) && childrenPresent vista level

def nextAnchor (vista : Executable.Vista) (level : Nat) (anchor : Option Nat) : Option Nat :=
  if Executable.flat vista (level+1) then some (level+1) else anchor

theorem nextAnchor_bound (vista : Executable.Vista) (level : Nat) (anchor : Option Nat)
    (bound : ∀ value∈anchor,value≤level) :
    ∀ value∈nextAnchor vista level anchor,value≤level+1 := by
  intro value member
  unfold nextAnchor at member
  split at member
  · cases member;omega
  · exact (bound value member).trans (Nat.le_succ _)

end Counting.StackMachine.AuditPrefix
