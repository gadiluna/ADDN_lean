import Counting.DagKeyOrder
import Counting.EncodingDag

namespace Counting.StackMachine.Lexicographic

structure LexState where
  left : List Nat
  right : List Nat
  unresolved : Bool
  answer : Bool

def LexState.advance (value : LexState) : LexState :=
  match value.left,value.right with
  | [],_ => value
  | _::_,[] => ⟨[],[],false,if value.unresolved then false else value.answer⟩
  | a::as,b::bs => ⟨as,bs,value.unresolved && decide (a=b),
      if value.unresolved && !(decide (a=b)) then decide (a≤b) else value.answer⟩

def LexState.Valid (value : LexState) : Prop := value.unresolved=true → value.answer=true

def LexState.finalValue (value : LexState) : Bool :=
  if value.unresolved then Executable.lexLE value.left value.right else value.answer

def LexState.encodedLength (value : LexState) : Nat :=
  (Encoding.sequence Encoding.natural value.left).length+
    (Encoding.sequence Encoding.natural value.right).length

end Counting.StackMachine.Lexicographic
