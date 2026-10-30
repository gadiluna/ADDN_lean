import Counting.ExternalUnaryEmission

namespace Counting.External.CookLevin.StackGenerator
open Machine InitialRows

def bitKind (bit : Bool) : InitialSymbolKind := if bit then .one else .zero

def initialKind (place offset : Nat) (header : List Bool) (capacity : Nat) : InitialSymbolKind :=
  if offset≤place then
    match header[place-offset]? with
    | some bit => bitKind bit
    | none => if header.length+capacity≤place-offset then .blank else .witness
  else .blank

theorem bitKind_allowed (bit : Bool) (symbol : Symbol) : (bitKind bit).allowed symbol ↔ symbol=bitSymbol bit := by
  cases bit <;> rfl

theorem initialKind_allowed {width : Nat} (setup : Setup width) (place : Fin width) (symbol : Symbol) :
    (initialKind place.val setup.offset.val setup.header setup.capacity).allowed symbol ↔ setup.symbolAllowed place symbol := by
  by_cases after : setup.offset.val≤place.val
  · have notBefore : ¬place.val<setup.offset.val := by omega
    rw [initialKind,if_pos after]
    cases found : setup.header[place.val-setup.offset.val]? with
    | some bit =>
        have inside := (List.getElem?_eq_some_iff.mp found).1
        have inHeader : place.val<setup.offset.val+setup.header.length := by omega
        have value : WitnessWord.read setup.header (place.val-setup.offset.val)=bitSymbol bit := by
          simp [WitnessWord.read,List.getElem?_map,found]
        simp only [bitKind_allowed,Setup.symbolAllowed,notBefore,if_false,inHeader,if_true,value]
    | none =>
        have outside : setup.header.length≤place.val-setup.offset.val := List.getElem?_eq_none_iff.mp found
        have notHeader : ¬place.val<setup.offset.val+setup.header.length := by omega
        simp only [Setup.symbolAllowed,notBefore,if_false,notHeader]
        by_cases past : setup.header.length+setup.capacity≤place.val-setup.offset.val
        · have notWitness : ¬place.val<setup.offset.val+setup.header.length+setup.capacity := by omega
          simp [past,notWitness,InitialSymbolKind.allowed]
        · have inWitness : place.val<setup.offset.val+setup.header.length+setup.capacity := by omega
          simp [past,inWitness,InitialSymbolKind.allowed]
  · have before : place.val<setup.offset.val := by omega
    simp [initialKind,after,Setup.symbolAllowed,before,InitialSymbolKind.allowed]

theorem initialAllowed_eq {width : Nat} (setup : Setup width) (program : Program) (place : Fin width)
    (value : Fin (Cellular.alphabet program)) :
    initialAllowed program (decide (place.val=setup.offset.val))
      (initialKind place.val setup.offset.val setup.header setup.capacity) value=
      (setup.unary program place).allowed (fun _ => value) := by
  unfold initialAllowed Setup.unary Setup.expectedControl
  have positions : (place.val=setup.offset.val) ↔ place=setup.offset := Fin.val_inj
  simp only [decide_eq_true_eq,positions,initialKind_allowed]

end Counting.External.CookLevin.StackGenerator
