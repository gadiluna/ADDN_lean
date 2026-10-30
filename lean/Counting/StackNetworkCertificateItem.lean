import Counting.StackNetworkCertificateRead
import Counting.StackNetworkCertificateParser
import Counting.StackRealizabilityVistaChecks
import Counting.StackRealizabilityWitnessFields

namespace Counting.StackMachine.NetworkCertificate
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 200000
set_option maxHeartbeats 3000000

def erased (selected : List (Fin 30)) (data : Fin 30→List Bool) : Fin 30→List Bool :=
  fun r => if r∈selected then [] else data r

def clearFields (selected : List (Fin 30)) : Routine 128 :=
  clearRegisters (selected.map context)

theorem clearFields_executes (selected : List (Fin 30)) (data : Fin 30→List Bool)
    (bound : Nat) (bounded : ∀ r, (data r).length≤bound) :
    ∃ time ≤ selected.length*(bound+2),
      Executes (clearFields selected) (file data) time (file (erased selected data)) := by
  obtain ⟨time,cost,run⟩ := clearRegisters_executes (selected.map context) (file data) bound (by
    intro r
    unfold file
    split
    · exact bounded _
    · simp)
  have result : clearedStore (selected.map context) (file data)=file (erased selected data) := by
    funext r
    by_cases inside : 100≤r.val
    · let i : Fin 30 := ⟨r.val-100,by omega⟩
      have same : r=context i := by apply Fin.ext;dsimp [context,i];omega
      rw [same]
      simp [clearedStore,erased,List.mem_map,context.injective.eq_iff]
    · have absent : r∉selected.map context := by
        rintro member
        obtain ⟨i,_,equal⟩ := List.mem_map.mp member
        have value := congrArg (fun r : Fin 130 => r.val) equal
        change 100+i.val=r.val at value
        omega
      simp [clearedStore,absent,file,inside]
  rw [result] at run
  exact ⟨time,by simpa only [List.length_map] using cost,run⟩

def itemFields : List (Fin 30) := [0,1,3,6,7]

def item : Routine 128 := sequence (consumeField DagParser.vista 10 0)
  (sequence (consumeField VistaComplement.witnessParser 11 9)
    (sequence (moveExternal 9 5)
      (sequence VistaComplement.witnessFields
        (sequence VistaComplement.checks (clearFields itemFields)))))

def itemResult (data : Fin 30→List Bool) (viewSuffix witnessSuffix : List Bool)
    (accepted : Bool) (tail : List Bool) (vista : Executable.Vista)
    (ell : Nat) (certificate : Encoding.TwoOrderData) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update data 10 viewSuffix) 11 witnessSuffix)
    4 ((accepted && Encoding.verifyTwoOrders vista ell certificate)::tail)

def itemCoefficient := VistaComplement.checksCoefficient+50000

theorem item_executes (data : Fin 30→List Bool) (vista : Executable.Vista)
    (ell : Nat) (certificate : Encoding.TwoOrderData) (viewSuffix witnessSuffix : List Bool)
    (accepted : Bool) (tail : List Bool) (status : data 4=accepted::tail)
    (leader : data 2=Encoding.natural.encode ell)
    (views : data 10=Encoding.vista.encode vista++viewSuffix)
    (certs : data 11=Encoding.twoOrderWitness.encode certificate++witnessSuffix)
    (empty : ∀r:Fin 30,r∈([0,1,3,5,6,7,9]:List (Fin 30)) → data r=[])
    (bound : Nat) (bounded : ∀r,(data r).length≤bound)
    (payload : (Encoding.vista.encode vista).length+
      (Encoding.natural.encode ell).length+(Encoding.twoOrderWitness.encode certificate).length≤bound) :
    ∃ time ≤ Complexity.polynomial itemCoefficient 25 bound,
      Executes item (file data) time
        (file (itemResult data viewSuffix witnessSuffix accepted tail vista ell certificate)) := by
  rcases certificate with ⟨⟨first,a⟩,⟨second,b⟩⟩
  obtain ⟨t0,b0,r0⟩ := consumeField_executes DagParser.vista data 10 0 (by decide) (by decide)
    (by decide) (by decide) (by decide) vista viewSuffix accepted tail views status
    (empty 5 (by simp)) (empty 0 (by simp))
  let d1 := Function.update (Function.update data 10 viewSuffix) 0 (Encoding.vista.encode vista)
  obtain ⟨t1,b1,r1⟩ := consumeField_executes VistaComplement.witnessParser d1 11 9
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ((first,a),(second,b)) witnessSuffix accepted tail
    (by simpa [d1] using certs) (by simp [d1,status])
    (by simp [d1,empty 5 (by simp)]) (by simp [d1,empty 9 (by simp)])
  let d2 := Function.update (Function.update d1 11 witnessSuffix) 9
    (Encoding.twoOrderWitness.encode ((first,a),(second,b)))
  have r2 := moveExternal_executes d2 9 5 (by decide) (by simp [d2,d1,empty 5 (by simp)])
  let d3 := Function.update (Function.update d2 5 (d2 9)) 9 []
  obtain ⟨t3,b3,r3⟩ := VistaComplement.witnessFields_executes d3 first second a b accepted tail
    (by simp [d3,d2,d1,status]) (by simp [d3,d2])
    (by simp [d3,d2,d1,empty 3 (by simp)]) (by simp [d3,d2,d1,empty 1 (by simp)])
    (by simp [d3,d2,d1,empty 6 (by simp)]) (by simp [d3,d2,d1,empty 7 (by simp)])
  let d4 := VistaComplement.witnessFieldsData d3 first second a b
  have fields : ∀r, d4 r=(if r=0 then Encoding.vista.encode vista else
      if r=1 then (Encoding.list Encoding.natural).encode a else if r=2 then Encoding.natural.encode ell else
      if r=3 then Encoding.natural.encode first else if r=5 then [] else
      if r=6 then Encoding.natural.encode second else if r=7 then (Encoding.list Encoding.natural).encode b else
      if r=9 then [] else if r=10 then viewSuffix else if r=11 then witnessSuffix else data r) := by
    intro r
    fin_cases r <;> simp [d4,VistaComplement.witnessFieldsData,VistaComplement.orderFieldsData,d3,d2,d1,leader]
  obtain ⟨t4,b4,r4⟩ := VistaComplement.checks_executes d4 vista ell first second a b
    (by simp [fields]) (by simp [fields]) (by simp [fields]) (by simp [fields])
    (by simp [fields]) (by simp [fields]) accepted tail (by simp [fields,status])
  let d5 := Function.update (VistaComplement.secondFieldsData d4) 4
    ((accepted && Encoding.verifyTwoOrders vista ell ((first,a),(second,b)))::tail)
  have lengths : (Encoding.twoOrderWitness.encode ((first,a),(second,b))).length=
      (Encoding.natural.encode first).length+((Encoding.list Encoding.natural).encode a).length+
      (Encoding.natural.encode second).length+((Encoding.list Encoding.natural).encode b).length := by
    simp only [Encoding.twoOrderWitness,Encoding.orderWitness,Encoding.product,List.length_append]
    omega
  have suffixV : viewSuffix.length≤bound := by have := bounded 10;rw [views,List.length_append] at this;omega
  have suffixC : witnessSuffix.length≤bound := by have := bounded 11;rw [certs,List.length_append] at this;omega
  have statusLength : (accepted::tail).length≤bound := by simpa only [←status] using bounded 4
  have normalPayload := payload
  have normalLengths := lengths
  have normalStatus := statusLength
  simp only [Encoding.vista,Encoding.transport,Encoding.product,Encoding.twoOrderWitness,
    Encoding.orderWitness,List.length_append,Encoding.natural_length,List.length_cons]
    at normalPayload normalLengths normalStatus
  have bounded5 : ∀r,(d5 r).length≤bound := by
    intro r
    fin_cases r <;> simp [d5,VistaComplement.secondFieldsData,fields]
    all_goals first | exact bounded _ | omega
  obtain ⟨t5,b5,r5⟩ := clearFields_executes itemFields d5 bound bounded5
  have final : erased itemFields d5=itemResult data viewSuffix witnessSuffix accepted tail
      vista ell ((first,a),(second,b)) := by
    funext r
    fin_cases r <;> simp [erased,itemFields,d5,VistaComplement.secondFieldsData,fields,itemResult,
      empty 0 (by simp),empty 1 (by simp),empty 3 (by simp),empty 5 (by simp),
      empty 6 (by simp),empty 7 (by simp),empty 9 (by simp),leader]
  rw [final] at r5
  have fieldsBound : VistaComplement.fieldsLength d4≤bound := by
    simp [VistaComplement.fieldsLength,fields]
    omega
  have checksBound := b4.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right fieldsBound 1) 25))
  have witnessLength : (Encoding.twoOrderWitness.encode ((first,a),(second,b))).length≤bound := by omega
  have witnessBound := b3.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right witnessLength 1) 4))
  have p4 : (bound+1)^4≤(bound+1)^25 := Nat.pow_le_pow_right (by omega) (by decide)
  have linear : bound+1≤(bound+1)^25 := Nat.le_self_pow (by decide) _
  have coefficient0 : DagParser.vista.coefficient=3890 := rfl
  have exponent0 : DagParser.vista.exponent=4 := rfl
  have coefficient1 : VistaComplement.witnessParser.coefficient≤10000 := by decide
  have exponent1 : VistaComplement.witnessParser.exponent≤4 := by decide
  have c0 := bounded 10
  have c1 : (d1 11).length≤bound := by simpa [d1] using bounded 11
  have firstBound : t0≤3890*(bound+1)^25+14*bound+12 := by
    have powers := (Nat.pow_le_pow_left (Nat.add_le_add_right c0 1) 4).trans p4
    have product := Nat.mul_le_mul_left 3890 powers
    simp only [Complexity.polynomial,coefficient0,exponent0] at b0
    omega
  have secondBound : t1≤10000*(bound+1)^25+14*bound+12 := by
    have powers := (Nat.pow_le_pow_left (Nat.add_le_add_right c1 1) VistaComplement.witnessParser.exponent).trans
      (Nat.pow_le_pow_right (by omega : 1≤bound+1) (exponent1.trans (by decide : 4≤25)))
    have product := Nat.mul_le_mul coefficient1 powers
    unfold Complexity.polynomial at b1
    omega
  have thirdBound := witnessBound.trans (Nat.mul_le_mul_left 16300 p4)
  have moveSize : (d2 9).length≤bound := by simpa [d2] using witnessLength
  refine ⟨_,?_,r0.sequence (r1.sequence (r2.sequence (r3.sequence (r4.sequence r5))))⟩
  change t4≤VistaComplement.checksCoefficient*(bound+1)^25 at checksBound
  change t5≤5*(bound+2) at b5
  simp only [Complexity.polynomial,itemCoefficient,Nat.add_mul]
  omega

end Counting.StackMachine.NetworkCertificate
