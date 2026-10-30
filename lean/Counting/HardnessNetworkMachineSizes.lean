import Counting.HardnessNetworkMachineEncodingSpec
import Counting.HardnessNetworkMachinePath
import Counting.ExternalCoefficientSizes

namespace Counting.HardnessNetworkMachine
set_option backward.isDefEq.respectTransparency false

/-- A bound on each serialized item pays for every item in the explicit list. -/
theorem encodedSequence_length_le {α : Type} (codec : Encoding.Codec α) (values : List α)
    (bound : Nat) (bounded : ∀ a∈values,(codec.encode a).length ≤ bound) :
    (Encoding.sequence codec values).length ≤ values.length*bound := by
  induction values with
  | nil=>simp [Encoding.sequence]
  | cons a rest ih=>
    have first:=bounded a (by simp)
    have tail:=ih (fun b member=>bounded b (by simp [member]))
    simp only [Encoding.sequence,List.length_append,List.length_cons]
    nlinarith only [first,tail]

theorem oneHotRow_encoded_length (width target : Nat) (inside : target<width) :
    ((Encoding.list Encoding.natural).encode (oneHotRow width target)).length ≤ 3*width+3 := by
  rw [oneHotRow_encoding width target inside]
  have size : width.size ≤ width := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [List.length_append,List.length_replicate,Encoding.natural_length]
  have unit : (1 : Nat).size=1 := by decide
  rw [unit]
  omega

theorem consecutiveRows_encoded_length (width start count : Nat) (inside : start+count ≤ width) :
    (Encoding.sequence (Encoding.list Encoding.natural) (consecutiveRows width start count)).length ≤
      count*(3*width+3) := by
  induction count generalizing start with
  | zero=>simp [consecutiveRows,Encoding.sequence]
  | succ count ih=>
    have first:=oneHotRow_encoded_length width start (by omega)
    have tail:=ih (start+1) (by omega)
    simp only [consecutiveRows,Encoding.sequence,List.length_append]
    nlinarith only [first,tail]

theorem groupRows_encoded_length (width start size : Nat) (positive : 0<size)
    (inside : start+size ≤ width) :
    (Encoding.sequence (Encoding.list Encoding.natural) (groupRows width start size)).length ≤
      size*(3*width+3) := by
  have chain:=consecutiveRows_encoded_length width (start+1) (size-1) (by omega)
  have closing:=oneHotRow_encoded_length width 0 (by omega)
  simp only [groupRows,sequence_append,Encoding.sequence,List.length_append,List.length_nil,Nat.add_zero]
  have subtract : size-1+1=size := by omega
  nlinarith only [chain,closing,subtract]

theorem ordinaryGroupRows_encoded_length (width start size count : Nat) (positive : 0<size)
    (inside : start+count*size ≤ width) :
    (Encoding.sequence (Encoding.list Encoding.natural) (ordinaryGroupRows width start size count)).length ≤
      count*size*(3*width+3) := by
  induction count generalizing start with
  | zero=>simp [ordinaryGroupRows,Encoding.sequence]
  | succ count ih=>
    have first:=groupRows_encoded_length width start size positive (by nlinarith only [inside,Nat.zero_le (count*size)])
    have tail:=ih (start+size) (by nlinarith only [inside])
    rw [ordinaryGroupRows_succ,sequence_append,List.length_append]
    nlinarith only [first,tail]

theorem leaderRow_encoded_length (base first : Nat) (rest : List Nat) (bitWidth : Nat)
    (bounded : ∀ value∈first::rest,value.bits.length ≤ bitWidth) :
    ((Encoding.list Encoding.natural).encode (leaderRow base (first::rest))).length ≤
      networkOrder base (first::rest)*(2*bitWidth+3)+1 := by
  have entries : ∀ value∈leaderRow base (first::rest),value.bits.length ≤ bitWidth := by
    intro value member
    simp only [leaderRow,List.headD_cons,List.tail_cons,List.mem_cons,List.mem_append,List.mem_flatMap] at member
    rcases member with rfl|firstMember|⟨source,sourceMember,copy⟩
    · simp
    · have same : value=first := (List.mem_replicate.mp firstMember).2
      subst value
      exact bounded first (by simp)
    · have same : value=source := (List.mem_replicate.mp copy).2
      subst value
      exact bounded source (by simp [sourceMember])
  have stream:=External.CoefficientMachine.natural_sequence_length_le _ bitWidth entries
  have length : (leaderRow base (first::rest)).length=networkOrder base (first::rest) := by
    simp only [leaderRow_cons_length,networkOrder,List.length_cons]
  have header : (networkOrder base (first::rest)).size ≤ networkOrder base (first::rest) :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  rw [length] at stream
  simp only [Encoding.list,List.length_append,Encoding.natural_length,length]
  nlinarith only [stream,header]

theorem pathMatrix_encoded_length (base first : Nat) (rest : List Nat) (positive : 0<base) :
    ((Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix base (first::rest))).length ≤
      ((Encoding.list Encoding.natural).encode (leaderRow base (first::rest))).length+
        5*(networkOrder base (first::rest)+1)^2 := by
  let N:=networkOrder base (first::rest)
  have dimensions : N=base+2+rest.length*base := by simp [N,networkOrder];ring
  have baseline:=groupRows_encoded_length N 1 (base+1) (by omega) (by nlinarith only [dimensions,Nat.zero_le (rest.length*base)])
  have restBound:=ordinaryGroupRows_encoded_length N (base+2) base rest.length positive (by omega)
  have header : N.size ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
  change (Encoding.natural.encode (pathMatrix base (first::rest)).length++_).length ≤ _
  rw [pathMatrix_cons_length base first rest positive]
  simp only [pathMatrix,List.tail_cons,Encoding.sequence,sequence_append,List.length_append,Encoding.natural_length]
  change 2*N.size+1+(_+(_+_)) ≤ _+5*(N+1)^2
  nlinarith only [baseline,restBound,header,dimensions,Nat.zero_le N]

theorem starMatrix_encoded_length (base first : Nat) (rest : List Nat) :
    ((Encoding.list (Encoding.list Encoding.natural)).encode (starMatrix base (first::rest))).length ≤
      ((Encoding.list Encoding.natural).encode (leaderRow base (first::rest))).length+
        5*(networkOrder base (first::rest)+1)^2 := by
  let N:=networkOrder base (first::rest)
  have positive : 0<N := by simp [N,networkOrder]
  have row:=oneHotRow_encoded_length N 0 positive
  have remaining:=encodedSequence_length_le (Encoding.list Encoding.natural)
    (List.replicate (N-1) (oneHotRow N 0)) (3*N+3) (by
      intro value member
      have same : value=oneHotRow N 0 := (List.mem_replicate.mp member).2
      simpa only [same] using row)
  have header : N.size ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
  have length : (starMatrix base (first::rest)).length=N := by simp [starMatrix,N];omega
  change (Encoding.natural.encode (starMatrix base (first::rest)).length++_).length ≤ _
  rw [length]
  simp only [starMatrix,Encoding.sequence,List.length_append,Encoding.natural_length]
  simp only [List.length_replicate] at remaining
  change 2*N.size+1+(_+_) ≤ _+5*(N+1)^2
  have subtract : N-1 ≤ N := Nat.sub_le _ _
  have scaled:=Nat.mul_le_mul_right (3*N+3) subtract
  nlinarith only [remaining,scaled,header,Nat.zero_le N]

theorem networkWord_encoded_length (base first : Nat) (rest : List Nat) (positive : 0<base) :
    (networkWord base (first::rest)).length ≤
      3*networkOrder base (first::rest)+2*base+2+
        base*(((Encoding.list Encoding.natural).encode (leaderRow base (first::rest))).length+
          5*(networkOrder base (first::rest)+1)^2) := by
  let N:=networkOrder base (first::rest)
  have population : 0<N := by simp [N,networkOrder]
  have leaderCount : (networkLeaders base (first::rest)).length=N := by
    simp [networkLeaders,N];omega
  have roundsCount : (networkRounds base (first::rest)).length=base := by
    simp [networkRounds];omega
  have markers:=encodedSequence_length_le Encoding.boolean (networkLeaders base (first::rest)) 1
    (by intro value _;rfl)
  rw [leaderCount,Nat.mul_one] at markers
  have matrices:=encodedSequence_length_le (Encoding.list (Encoding.list Encoding.natural))
    (networkRounds base (first::rest))
    (((Encoding.list Encoding.natural).encode (leaderRow base (first::rest))).length+5*(N+1)^2) (by
      intro matrix member
      simp only [networkRounds,List.mem_append,List.mem_singleton,List.mem_replicate] at member
      rcases member with ⟨_,rfl⟩|rfl
      · exact pathMatrix_encoded_length base first rest positive
      · exact starMatrix_encoded_length base first rest)
  rw [roundsCount] at matrices
  have populationSize : N.size ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
  have baseSize : base.size ≤ base := Nat.size_le.mpr Nat.lt_two_pow_self
  change ((Encoding.natural.encode (networkLeaders base (first::rest)).length++
    Encoding.sequence Encoding.boolean (networkLeaders base (first::rest)))++
    (Encoding.natural.encode (networkRounds base (first::rest)).length++
      Encoding.sequence (Encoding.list (Encoding.list Encoding.natural))
        (networkRounds base (first::rest)))).length ≤ _
  simp only [List.length_append,Encoding.natural_length,leaderCount,roundsCount]
  change _ ≤ 3*N+2*base+2+_
  dsimp only [N] at matrices populationSize markers ⊢
  omega

theorem inputCoefficients_nonempty (input : X3CEncoding.Input) :
    External.CoefficientMachine.inputCoefficients input≠[] := by
  intro empty
  have length:=External.CoefficientMachine.inputCoefficients_length input
  rw [empty,List.length_nil] at length
  omega

theorem coefficient_networkOrder_bound (input : X3CEncoding.Input) (L : Nat)
    (qBound : input.1 ≤ L) (countBound : input.2.1 ≤ L) :
    networkOrder (X3C.base input.1) (External.CoefficientMachine.inputCoefficients input)+1 ≤ (L+4)^2 := by
  simp only [networkOrder,External.CoefficientMachine.inputCoefficients_length,X3C.base]
  have product:=Nat.mul_le_mul (Nat.add_le_add_right countBound 1) (Nat.add_le_add_right qBound 3)
  nlinarith only [product,Nat.zero_le L]

theorem coefficient_leaderRow_encoded_bound (input : X3CEncoding.Input) (L : Nat)
    (qBound : input.1 ≤ L) (countBound : input.2.1 ≤ L) :
    ((Encoding.list Encoding.natural).encode
      (leaderRow (X3C.base input.1) (External.CoefficientMachine.inputCoefficients input))).length ≤
        12*(L+4)^4 := by
  have width:=External.CoefficientMachine.coefficient_width_bound input.1 L qBound
  have entries : ∀ value∈External.CoefficientMachine.inputCoefficients input,value.bits.length ≤ 4*(L+4)^2 :=
    fun value member=>(External.CoefficientMachine.inputCoefficients_size input value member).trans width
  have population:=coefficient_networkOrder_bound input L qBound countBound
  generalize h : External.CoefficientMachine.inputCoefficients input=coefficients at entries population ⊢
  cases coefficients with
  | nil=>exact False.elim (inputCoefficients_nonempty input h)
  | cons first rest=>
    have row:=leaderRow_encoded_length (X3C.base input.1) first rest (4*(L+4)^2) entries
    have coefficient : 2*(4*(L+4)^2)+3 ≤ 11*(L+4)^2 := by nlinarith only [Nat.zero_le L]
    have scaled:=Nat.mul_le_mul (show networkOrder (X3C.base input.1) (first::rest) ≤ (L+4)^2 by omega) coefficient
    have one : 1 ≤ (L+4)^4 := Nat.one_le_pow _ _ (by omega)
    nlinarith only [row,scaled,one]

theorem coefficient_pathMatrix_encoded_bound (input : X3CEncoding.Input) (L : Nat)
    (qBound : input.1 ≤ L) (countBound : input.2.1 ≤ L) :
    ((Encoding.list (Encoding.list Encoding.natural)).encode
      (pathMatrix (X3C.base input.1) (External.CoefficientMachine.inputCoefficients input))).length ≤
        17*(L+4)^4 := by
  have row:=coefficient_leaderRow_encoded_bound input L qBound countBound
  have population:=coefficient_networkOrder_bound input L qBound countBound
  generalize h : External.CoefficientMachine.inputCoefficients input=coefficients at row population ⊢
  cases coefficients with
  | nil=>exact False.elim (inputCoefficients_nonempty input h)
  | cons first rest=>
    have matrix:=pathMatrix_encoded_length (X3C.base input.1) first rest (by simp [X3C.base])
    have square:=Nat.pow_le_pow_left population 2
    nlinarith only [row,matrix,square]

theorem coefficient_starMatrix_encoded_bound (input : X3CEncoding.Input) (L : Nat)
    (qBound : input.1 ≤ L) (countBound : input.2.1 ≤ L) :
    ((Encoding.list (Encoding.list Encoding.natural)).encode
      (starMatrix (X3C.base input.1) (External.CoefficientMachine.inputCoefficients input))).length ≤
        17*(L+4)^4 := by
  have row:=coefficient_leaderRow_encoded_bound input L qBound countBound
  have population:=coefficient_networkOrder_bound input L qBound countBound
  generalize h : External.CoefficientMachine.inputCoefficients input=coefficients at row population ⊢
  cases coefficients with
  | nil=>exact False.elim (inputCoefficients_nonempty input h)
  | cons first rest=>
    have matrix:=starMatrix_encoded_length (X3C.base input.1) first rest
    have square:=Nat.pow_le_pow_left population 2
    nlinarith only [row,matrix,square]

theorem coefficient_networkWord_encoded_bound (input : X3CEncoding.Input) (L : Nat)
    (qBound : input.1 ≤ L) (countBound : input.2.1 ≤ L) :
    (networkWord (X3C.base input.1) (External.CoefficientMachine.inputCoefficients input)).length ≤
        25*(L+4)^5 := by
  have row:=coefficient_leaderRow_encoded_bound input L qBound countBound
  have population:=coefficient_networkOrder_bound input L qBound countBound
  have base : X3C.base input.1 ≤ L+4 := by simp only [X3C.base];omega
  generalize h : External.CoefficientMachine.inputCoefficients input=coefficients at row population ⊢
  cases coefficients with
  | nil=>exact False.elim (inputCoefficients_nonempty input h)
  | cons first rest=>
    have word:=networkWord_encoded_length (X3C.base input.1) first rest (by simp [X3C.base])
    have square:=Nat.pow_le_pow_left population 2
    have rows : ((Encoding.list Encoding.natural).encode (leaderRow (X3C.base input.1) (first::rest))).length+
        5*(networkOrder (X3C.base input.1) (first::rest)+1)^2 ≤ 17*(L+4)^4 := by
      nlinarith only [row,square]
    have scaled:=Nat.mul_le_mul base rows
    have low : 3*(L+4)^2+2*(L+4)+2 ≤ 8*(L+4)^5 := by
      nlinarith only [Nat.zero_le L,Nat.le_self_pow (by decide : 2≠0) (L+4),
        Nat.pow_le_pow_right (by omega : 1 ≤ L+4) (by decide : 2 ≤ 5)]
    nlinarith only [word,scaled,low,population,base]

end Counting.HardnessNetworkMachine
