import Counting.ExternalThreeDM
import Counting.EncodingBinary
import Counting.ComplexityModel

namespace Counting.External.ThreeDMEncoding

abbrev Input := Σ q : Nat,Σ m : Nat,ThreeDM q m
abbrev Triple (q : Nat) := Fin 3 → Fin q
abbrev Raw := List Bool × List (List Nat)

def rawCodec : Encoding.Codec Raw :=
  Encoding.product (Encoding.list Encoding.boolean) (Encoding.list (Encoding.list Encoding.natural))

def elementFromRaw (q value : Nat) : Option (Fin q) := if bounded : value<q then some ⟨value,bounded⟩ else none

def tripleRaw {q : Nat} (triple : Triple q) : List Nat := (List.ofFn triple).map Fin.val

def tripleFromRaw (q : Nat) (values : List Nat) : Option (Triple q) :=
  let parsed := values.filterMap (elementFromRaw q)
  if length : parsed.length=3 then some (fun part=>parsed[part.val]'(by rw [length];exact part.isLt)) else none

@[simp] theorem element_roundtrip {q : Nat} (value : Fin q) : elementFromRaw q value.val=some value := by
  simp [elementFromRaw,value.isLt]

@[simp] theorem elements_roundtrip {q : Nat} (values : List (Fin q)) :
    (values.map Fin.val).filterMap (elementFromRaw q)=values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [List.map_cons,List.filterMap_cons,element_roundtrip,ih]

@[simp] theorem triple_roundtrip {q : Nat} (triple : Triple q) : tripleFromRaw q (tripleRaw triple)=some triple := by
  simp [tripleFromRaw,tripleRaw]
  funext part;fin_cases part <;> rfl

def pack (q : Nat) (triples : List (Triple q)) : Input := ⟨q,triples.length,⟨fun j=>triples.get j⟩⟩

def inputTriples (input : Input) : List (Triple input.1) := List.ofFn input.2.2.edge

theorem pack_inputTriples (input : Input) : pack input.1 (inputTriples input)=input := by
  rcases input with ⟨q,m,inst⟩
  change pack q (List.ofFn inst.edge)=_
  generalize listEq : List.ofFn inst.edge=triples
  have sizeEq : triples.length=m := by rw [←listEq,List.length_ofFn]
  generalize lengthEq : triples.length=k at *
  subst k;subst m
  apply congrArg (Sigma.mk q)
  apply congrArg (Sigma.mk triples.length)
  have functionEq : (fun j=>triples.get j)=inst.edge := by
    funext j
    have same := congrArg (fun rows : List (Triple q)=>rows[j.val]?) listEq
    simp only [List.getElem?_ofFn,j.isLt,dif_pos,List.getElem?_eq_getElem] at same
    exact (Option.some.inj same).symm
  cases inst;cases functionEq;rfl

def toRaw (input : Input) : Raw := (List.replicate input.1 true,(inputTriples input).map tripleRaw)
def fromRaw (raw : Raw) : Input := pack raw.1.length (raw.2.filterMap (tripleFromRaw raw.1.length))

@[simp] theorem triples_roundtrip {q : Nat} (triples : List (Triple q)) :
    (triples.map tripleRaw).filterMap (tripleFromRaw q)=triples := by
  induction triples with
  | nil => rfl
  | cons triple rest ih => simp only [List.map_cons,List.filterMap_cons,triple_roundtrip,ih]

@[simp] theorem fromRaw_toRaw (input : Input) : fromRaw (toRaw input)=input := by
  rcases input with ⟨q,m,inst⟩
  dsimp only [fromRaw,toRaw]
  generalize tableEq : List.replicate q true=table
  have sizeEq : table.length=q := by rw [←tableEq,List.length_replicate]
  generalize lengthEq : table.length=k at *
  subst k;subst q
  rw [triples_roundtrip]
  exact pack_inputTriples ⟨table.length,m,inst⟩

def codec : Encoding.Codec Input := Encoding.transport rawCodec toRaw fromRaw fromRaw_toRaw

@[simp] theorem tripleRaw_length {q : Nat} (triple : Triple q) : (tripleRaw triple).length=3 := by simp [tripleRaw]
@[simp] theorem inputTriples_length (input : Input) : (inputTriples input).length=input.2.1 := List.length_ofFn

def MatchingLanguage : Complexity.Language := Complexity.encodedLanguage codec (fun input=>input.2.2.Yes)

theorem encoded_yes_iff (input : Input) : codec.encode input∈MatchingLanguage ↔ input.2.2.Yes :=
  Complexity.encodedLanguage_iff codec _ input

end Counting.External.ThreeDMEncoding
