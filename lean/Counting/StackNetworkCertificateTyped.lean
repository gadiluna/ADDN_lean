import Counting.StackNetworkCertificateFields
import Counting.StackNetworkCertificateHeader
import Counting.StackNetworkCertificateLoop
import Counting.StackReadBranch

namespace Counting.StackMachine.NetworkCertificate
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 200000
set_option maxHeartbeats 2400000

def initialData (bits : List Bool) (accepted : Bool) : Fin 30→List Bool :=
  fun r => if r=4 then [accepted] else if r=8 then bits else []

def parsedData (input : Counting.NetworkCertificate.Input) : Fin 30→List Bool :=
  fun r => if r=2 then Encoding.natural.encode input.1 else if r=4 then [true]
    else if r=8 then Counting.NetworkCertificate.codec.encode input
    else if r=10 then (Encoding.list Encoding.vista).encode input.2.1
    else if r=11 then Encoding.networkWitness.encode input.2.2 else []

def preparedData (input : Counting.NetworkCertificate.Input) : Fin 30→List Bool :=
  fun r => if r=2 then Encoding.natural.encode input.1 else if r=4 then [true]
    else if r=8 then Counting.NetworkCertificate.codec.encode input
    else if r=10 then Encoding.sequence Encoding.vista input.2.1
    else if r=11 then Encoding.sequence Encoding.twoOrderWitness input.2.2
    else if r=12 then List.replicate input.2.1.length true
    else if r=13 then List.replicate input.2.2.length true else []

def checkedData (input : Counting.NetworkCertificate.Input) : Fin 30→List Bool :=
  Function.update (preparedData input) 4 [decide (input.2.1.length=input.2.2.length)]

def prepareTyped : Routine 128 := sequence (copyExternal 8 5) (sequence inputFields headers)

theorem prepareTyped_executes (input : Counting.NetworkCertificate.Input) :
    ∃ time ≤ 70000*((Counting.NetworkCertificate.codec.encode input).length+1)^5,
      Executes prepareTyped (file (initialData (Counting.NetworkCertificate.codec.encode input) true)) time
        (file (preparedData input)) := by
  let initial := initialData (Counting.NetworkCertificate.codec.encode input) true
  have r0 := copyExternal_executes initial 8 5 (by decide)
  rw [show initial 5=[] by simp [initial,initialData],List.append_nil] at r0
  let copied := Function.update initial 5 (Counting.NetworkCertificate.codec.encode input)
  obtain ⟨t1,b1,r1⟩ := inputFields_executes copied input true []
    (by simp [copied,initial,initialData]) (by simp [copied])
    (by simp [copied,initial,initialData]) (by simp [copied,initial,initialData])
    (by simp [copied,initial,initialData])
  have fieldsEq : inputFieldsData copied input=parsedData input := by
    funext r
    by_cases r2:r=2 <;> by_cases r4:r=4 <;> by_cases r5:r=5 <;> by_cases r8:r=8 <;>
      by_cases r10:r=10 <;> by_cases r11:r=11 <;>
      simp [inputFieldsData,parsedData,copied,initial,initialData,r2,r4,r5,r8,r10,r11]
  rw [fieldsEq] at r1
  obtain ⟨t2,b2,r2⟩ := headers_executes (parsedData input) input.2.1 input.2.2 true []
    (by simp [parsedData]) (by simp [parsedData]) (by simp [parsedData])
    (by simp [parsedData]) (by simp [parsedData])
  have headerEq : Function.update (Function.update (Function.update (Function.update (parsedData input)
      10 (Encoding.sequence Encoding.vista input.2.1)) 12 (List.replicate input.2.1.length true))
      11 (Encoding.sequence Encoding.twoOrderWitness input.2.2)) 13 (List.replicate input.2.2.length true)=
      preparedData input := by
    funext r
    by_cases r2:r=2 <;> by_cases r4:r=4 <;> by_cases r8:r=8 <;> by_cases r10:r=10 <;>
      by_cases r11:r=11 <;> by_cases r12:r=12 <;> by_cases r13:r=13 <;>
      simp [parsedData,preparedData,r2,r4,r8,r10,r11,r12,r13]
  rw [headerEq] at r2
  let L := (Counting.NetworkCertificate.codec.encode input).length
  have lengths : L=(Encoding.natural.encode input.1).length+
      ((Encoding.list Encoding.vista).encode input.2.1).length+
      (Encoding.networkWitness.encode input.2.2).length := by
    simp only [L,Counting.NetworkCertificate.codec,Encoding.product,List.length_append];omega
  have b2base : (parsedData input 10).length+(parsedData input 11).length+1≤L+1 := by
    simp [parsedData];omega
  have power := (Nat.pow_le_pow_left b2base 3).trans
    (Nat.pow_le_pow_right (by omega : 1≤L+1) (by decide : 3≤5))
  have cost2 := b2.trans (Nat.mul_le_mul_left 3641 power)
  change t1≤65000*(L+1)^5 at b1
  have linear : L+1≤(L+1)^5 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,r0.sequence (r1.sequence r2)⟩
  change 5*(initial 8).length+2+1+(t1+1+t2)≤70000*(L+1)^5
  have initialAt : initial 8=Counting.NetworkCertificate.codec.encode input := by simp [initial,initialData]
  rw [initialAt]
  change 5*L+2+1+(t1+1+t2)≤_
  omega

def selectedLoop : Routine 128 := branchRead (context 4) loop (skip 128)

def typed : Routine 128 := sequence prepareTyped (sequence countsEqual selectedLoop)
def typedCoefficient := 2^26*(itemCoefficient+100000)

theorem typed_executes (input : Counting.NetworkCertificate.Input) :
    ∃ time ≤ Complexity.polynomial typedCoefficient 27 (Counting.NetworkCertificate.codec.encode input).length,
      ∃ result, Executes typed (file (initialData (Counting.NetworkCertificate.codec.encode input) true)) time
        (file result) ∧ result 4=[Counting.NetworkCertificate.check input.1 input.2.1 input.2.2] := by
  obtain ⟨t0,b0,r0⟩ := prepareTyped_executes input
  obtain ⟨t1,b1,r1⟩ := countsEqual_executes (preparedData input) true [] (by simp [preparedData])
  have countEq : decide (preparedData input 12=preparedData input 13)=
      decide (input.2.1.length=input.2.2.length) := by simp [preparedData]
  rw [countEq,Bool.true_and] at r1
  change Executes countsEqual (file (preparedData input)) t1 (file (checkedData input)) at r1
  let L := (Counting.NetworkCertificate.codec.encode input).length
  have lengths : L=(Encoding.natural.encode input.1).length+
      ((Encoding.list Encoding.vista).encode input.2.1).length+
      (Encoding.networkWitness.encode input.2.2).length := by
    simp only [L,Counting.NetworkCertificate.codec,Encoding.product,List.length_append];omega
  have countV : input.2.1.length≤(Encoding.sequence Encoding.vista input.2.1).length :=
    VerifiedParser.sequence_count_le vista_encoding_positive _
  have countC : input.2.2.length≤(Encoding.sequence Encoding.twoOrderWitness input.2.2).length :=
    VerifiedParser.sequence_count_le witness_encoding_positive _
  have allLength : (Encoding.natural.encode input.1).length+
      (Encoding.sequence Encoding.vista input.2.1).length+
      (Encoding.sequence Encoding.twoOrderWitness input.2.2).length≤L := by
    simp only [Encoding.networkWitness,Encoding.list,List.length_append] at lengths
    omega
  have countBound : input.2.1.length≤L ∧ input.2.2.length≤L := by omega
  have normalLength := allLength
  simp only [Encoding.natural_length] at normalLength
  have compareBound : t1≤12*L+15 := by
    simp [preparedData] at b1
    omega
  have polynomialBound (t2 : Nat)
      (small : t2 ≤ input.2.1.length*(Complexity.polynomial itemCoefficient 25 (L+1)+2)+4) :
      t0+1+(t1+1+t2)≤Complexity.polynomial typedCoefficient 27 L := by
    have scale : (L+2)^25≤2^25*(L+1)^25 := by
      simpa only [Nat.mul_pow] using Nat.pow_le_pow_left (by omega : L+2≤2*(L+1)) 25
    have bodyBound : input.2.1.length*(Complexity.polynomial itemCoefficient 25 (L+1)+2)≤
        (itemCoefficient*2^25)*(L+1)^26+2*(L+1) := by
      unfold Complexity.polynomial
      calc
        _≤(L+1)*(itemCoefficient*(2^25*(L+1)^25)+2) := by gcongr;omega
        _=_ := by ring
    have p5 : (L+1)^5≤(L+1)^27 := Nat.pow_le_pow_right (by omega) (by decide)
    have p26 : (L+1)^26≤(L+1)^27 := Nat.pow_le_pow_right (by omega) (by decide)
    have linear : L+1≤(L+1)^27 := Nat.le_self_pow (by decide) _
    have coefficient : itemCoefficient*2^25+70040≤typedCoefficient := by
      unfold typedCoefficient;omega
    have cost0 := b0.trans (Nat.mul_le_mul_left 70000 p5)
    have cost2 := Nat.mul_le_mul_left (itemCoefficient*2^25) p26
    have budget := Nat.mul_le_mul_right ((L+1)^27) coefficient
    unfold Complexity.polynomial
    nlinarith only [bodyBound,small,cost0,cost2,compareBound,linear,budget]
  by_cases same : input.2.1.length=input.2.2.length
  · let pairs := input.2.1.zip input.2.2
    have mapV : pairs.map Prod.fst=input.2.1 := by simp [pairs,List.map_fst_zip,same]
    have mapC : pairs.map Prod.snd=input.2.2 := by simp [pairs,List.map_snd_zip,same]
    have pairCount : pairs.length=input.2.1.length := by simp [pairs,List.length_zip,same]
    have bounded : ∀r,(checkedData input r).length≤L+1 := by
      intro r
      fin_cases r <;> simp [checkedData,preparedData]
      all_goals omega
    obtain ⟨t2,b2,r2⟩ := loop_executes (checkedData input) input.1 pairs [] [] true []
      (by simp [checkedData,same]) (by simp [checkedData,preparedData])
      (by simp [checkedData,preparedData,mapV]) (by simp [checkedData,preparedData,mapC])
      (by intro r member;fin_cases r <;> simp_all [checkedData,preparedData])
      (List.replicate input.2.1.length true) (by simp [checkedData,preparedData])
      (by simp [pairCount]) (L+1) bounded (by simp [checkedData,preparedData];omega)
    let result := loopResult (checkedData input) [] [] true [] input.1 pairs
    have branch := branchRead_executes (context 4) loop (skip 128) true []
      (file (checkedData input)) (file result) t2 (by simp [checkedData,same]) r2
    refine ⟨t0+1+(t1+1+(t2+3)),polynomialBound _ (by rw [pairCount] at b2;omega),
      result,r0.sequence (r1.sequence branch),?_⟩
    simp [result,loopResult,Counting.NetworkCertificate.check,same,pairs]
  · have selected : Executes (if false then loop else skip 128) (file (checkedData input)) 0
        (file (checkedData input)) := skip_executes _
    have branch := branchRead_executes (context 4) loop (skip 128) false []
      (file (checkedData input)) (file (checkedData input)) 0 (by simp [checkedData,same]) selected
    refine ⟨t0+1+(t1+1+3),polynomialBound _ (by omega),checkedData input,
      r0.sequence (r1.sequence branch),?_⟩
    simp [checkedData,Counting.NetworkCertificate.check,same]

end Counting.StackMachine.NetworkCertificate
