import Counting.ExternalMatchingLiteralRead
import Counting.ExternalMatchingPort
import Counting.ExternalMatchingEmitter
import Counting.StackRoutineClearSelected

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine SATVerification
set_option backward.isDefEq.respectTransparency false

abbrev LiteralWorkspace (extra : Nat) := Fin 48 ↪ Fin (extra+48)

def LiteralWorkspace.reader (w : LiteralWorkspace extra) : SATWorkspace (extra+16) :=
  (⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 48=>i.val) h)⟩ : Fin 32 ↪ Fin 48).trans w

def literalPortPositions : Fin 8 ↪ Fin 48 := ⟨![26,32,34,33,21,37,38,39],by decide⟩
def LiteralWorkspace.port (w : LiteralWorkspace extra) : LiteralPortWorkspace (extra+40) := literalPortPositions.trans w

def literalEdgePositions : Fin 12 ↪ Fin 48 := ⟨![35,27,37,40,41,42,36,43,44,45,46,47],by decide⟩
def LiteralWorkspace.edge (w : LiteralWorkspace extra) : EdgeWorkspace (extra+36) := literalEdgePositions.trans w

def generateLiteral (extra : Nat) (w : LiteralWorkspace extra) : Routine (extra+46) :=
  sequence (readMatchingLiteral (extra+16) w.reader)
    (sequence (computePort (extra+40) w.port)
      (sequence (ofProgram (ListPrograms.copyProgram (extra+45) (w 35) (w 27) (w 39)))
        (sequence (emitEdge (extra+36) w.edge)
          (sequence (clearRegisters [w 26,w 27,w 37]) (pushBit (w 34) true)))))

def generateLiteralScratch : List (Fin 48) :=
  [2,3,4,5,6,9,10,11,12,18,19,21,26,27,28,37,38,39,40,41,42,43,44,45,46,47]

def literalEdge (first index width occurrence shift : Nat) (sign : Bool) : List Nat :=
  [first,first,portValue index width occurrence shift sign]

def generateLiteralResult (extra : Nat) (w : LiteralWorkspace extra) (store : Fin (extra+48) → List Bool)
    (index : Nat) (sign : Bool) (suffix : List Bool) :=
  Function.update (Function.update (Function.update store (w 0) suffix) (w 34) (true::store (w 34)))
    (w 36) (((Encoding.list Encoding.natural).encode (literalEdge (store (w 35)).length index
      (store (w 32)).length (store (w 34)).length (store (w 33)).length sign)).reverse++store (w 36))

def generateLiteralCost (input n width occurrence shift first : Nat) :=
  200*(input+n+1)^3+40*(n+width+occurrence+shift+1)^2+
    5*first+300*(2*first+n*width+occurrence+shift+1)^2+
    3*(n+first+n*width+occurrence+shift+2)+12

end Counting.External.MatchingMachine
