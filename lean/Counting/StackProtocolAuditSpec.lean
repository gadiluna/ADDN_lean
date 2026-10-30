import Counting.StackProtocolAuditBank

namespace Counting.StackMachine.ProtocolAudit

/-- The normal scheduled-audit branch, after the local round is read from
its vista. The all-leader early-stop branch is handled by the caller. -/
def answer (vista : Executable.Vista) (leaders round : Nat) : Option Nat :=
  (Executable.candidateAt leaders round).bind fun selected=>
    if (Executable.audit? vista leaders selected.1 selected.2).isSome then some selected.1 else none

def inputWord (vista : Executable.Vista) (leaders round : Nat) : List Bool :=
  Encoding.natural.encode leaders++Encoding.natural.encode round++Encoding.vista.encode vista

def outputWord (value : Option Nat) : List Bool := (Encoding.optional Encoding.natural).encode value

def selectedWord (candidate last : Nat) : List Bool :=
  Encoding.natural.encode candidate++Encoding.natural.encode last

def metadata (vista : Executable.Vista) (leaders round candidate last : Nat) : Fin 8 → List Bool :=
  ![leaders.bits,round.bits,Encoding.vista.encode vista,candidate.bits,last.bits,[],[],[]]

theorem inputWord_length (vista : Executable.Vista) (leaders round : Nat) :
    (inputWord vista leaders round).length=
      2*leaders.size+2*round.size+(Encoding.vista.encode vista).length+2 := by
  simp [inputWord,Encoding.natural_length];omega

theorem selectedWord_length (candidate last : Nat) :
    (selectedWord candidate last).length=2*candidate.size+2*last.size+2 := by
  simp [selectedWord,Encoding.natural_length];omega

end Counting.StackMachine.ProtocolAudit
