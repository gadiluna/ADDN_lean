import Counting.ExternalCookLevin

namespace Counting.External.SATVerification
open CNFEncoding

def assignment (bits : List Bool) {n : Nat} : Fin n → Bool :=
  fun variableIndex => bits[variableIndex.val]?.getD false

def validRaw (raw : Raw) : Bool :=
  raw.1.all id && raw.2.all (fun clause => clause.all (fun literal => decide (literal.1<raw.1.length)))

def evalRaw (raw : Raw) (bits : List Bool) : Bool :=
  raw.2.all (fun clause => clause.any (fun literal => bits[literal.1]?.getD false == literal.2))

def checkRaw (raw : Raw) (bits : List Bool) : Bool :=
  validRaw raw && decide (bits.length=raw.1.length) && evalRaw raw bits

def check (input bits : List Bool) : Bool :=
  match rawCodec.decodeExact input with
  | none => false
  | some raw => checkRaw raw bits

theorem raw_literal_reencode (n : Nat) (clause : List (Nat×Bool))
    (bounded : ∀ literal∈clause,literal.1<n) :
    ((clause.filterMap (literalFromRaw n)).map literalRaw)=clause := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
    have first := bounded literal (by simp)
    have remaining : ∀ literal∈rest,literal.1<n := fun literal member => bounded literal (by simp [member])
    have item : literalFromRaw n literal=some ⟨⟨literal.1,first⟩,literal.2⟩ := dif_pos first
    rw [List.filterMap_cons,item,List.map_cons,ih remaining]
    rfl

theorem validRaw_reencode (raw : Raw) (valid : validRaw raw=true) : toRaw (fromRaw raw)=raw := by
  have checks : raw.1.all id=true ∧ ∀ clause∈raw.2,∀ literal∈clause,literal.1<raw.1.length := by
    simpa only [validRaw,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] using valid
  have table : List.replicate raw.1.length true=raw.1 := by
    apply Eq.symm
    apply List.eq_replicate_length.mpr
    simpa only [List.all_eq_true,id_eq] using checks.1
  apply Prod.ext
  · exact table
  · change (raw.2.map (List.filterMap (literalFromRaw raw.1.length))).map (List.map literalRaw)=raw.2
    rw [List.map_map]
    conv_rhs => rw [←List.map_id raw.2]
    apply List.map_congr_left
    intro clause member
    exact raw_literal_reencode raw.1.length clause (checks.2 clause member)

@[simp] theorem validRaw_toRaw (input : CNFInput) : validRaw (toRaw input)=true := by
  rcases input with ⟨n,formula⟩
  simp [validRaw,toRaw,literalRaw]

@[simp] theorem evalRaw_toRaw (input : CNFInput) (bits : List Bool) :
    evalRaw (toRaw input) bits=input.2.eval (assignment bits) := by
  simp [evalRaw,toRaw,CNF.eval,Literal.eval,literalRaw,assignment,Function.comp_def]

theorem checkRaw_toRaw (input : CNFInput) (bits : List Bool) :
    checkRaw (toRaw input) bits=true ↔ bits.length=input.1 ∧ input.2.eval (assignment bits)=true := by
  simp [checkRaw,toRaw,validRaw,literalRaw,evalRaw,assignment,CNF.eval,Literal.eval]

theorem check_iff (input bits : List Bool) :
    check input bits=true ↔ ∃ formula : CNFInput,
      codec.encode formula=input ∧ bits.length=formula.1 ∧ formula.2.eval (assignment bits)=true := by
  constructor
  · intro accepted
    cases decoded : rawCodec.decodeExact input with
    | none => simp [check,decoded] at accepted
    | some raw =>
      have rawAccepted : checkRaw raw bits=true := by simpa only [check,decoded] using accepted
      have checks : (validRaw raw=true ∧ decide (bits.length=raw.1.length)=true) ∧ evalRaw raw bits=true := by
        simpa only [checkRaw,Bool.and_eq_true] using rawAccepted
      have valid : validRaw raw=true := checks.1.1
      have same := validRaw_reencode raw valid
      refine ⟨fromRaw raw,?_,?_⟩
      · change rawCodec.encode (toRaw (fromRaw raw))=input
        rw [same]
        exact (rawCodec.decodeExact_iff input raw).mp decoded
      · rw [←same] at rawAccepted
        exact (checkRaw_toRaw _ bits).mp rawAccepted
  · rintro ⟨formula,rfl,length,satisfied⟩
    have decoded : rawCodec.decodeExact (codec.encode formula)=some (toRaw formula) :=
      (rawCodec.decodeExact_iff _ _).mpr rfl
    simp only [check,decoded]
    exact (checkRaw_toRaw formula bits).mpr ⟨length,satisfied⟩

theorem check_sound (input bits : List Bool) (accepted : check input bits=true) : input∈CookLevin.SAT := by
  obtain ⟨formula,encoded,_length,satisfied⟩ := (check_iff input bits).mp accepted
  exact ⟨formula,encoded,assignment bits,satisfied⟩

theorem check_witness_length (input bits : List Bool) (accepted : check input bits=true) : bits.length ≤ input.length := by
  obtain ⟨formula,encoded,length,_satisfied⟩ := (check_iff input bits).mp accepted
  rw [length,←encoded]
  exact (input_size_bounds formula).1

theorem exists_check_iff (input : List Bool) :
    input∈CookLevin.SAT ↔ ∃ bits, bits.length ≤ input.length ∧ check input bits=true := by
  constructor
  · rintro ⟨⟨n,formula⟩,encoded,values,satisfied⟩
    let bits := (List.finRange n).map values
    have length : bits.length=n := by simp [bits]
    have same : assignment bits=values := by
      funext i
      simp [assignment,bits,i.isLt]
    refine ⟨bits,?_,(check_iff input bits).mpr ⟨⟨n,formula⟩,encoded,length,?_⟩⟩
    · rw [length,←encoded]
      exact (input_size_bounds ⟨n,formula⟩).1
    · simpa only [same] using satisfied
  · rintro ⟨bits,_bounded,accepted⟩
    exact check_sound input bits accepted

end Counting.External.SATVerification
