import Counting.StackNetworkCertificateItem

namespace Counting.StackMachine.NetworkCertificate
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 200000
set_option maxHeartbeats 2600000

def loop : Routine 128 := forEach (context 12) item

def loopResult (data : Fin 30→List Bool) (viewSuffix witnessSuffix : List Bool)
    (accepted : Bool) (tail : List Bool) (ell : Nat)
    (pairs : List (Executable.Vista × Encoding.TwoOrderData)) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update (Function.update data 12 [])
    10 viewSuffix) 11 witnessSuffix)
    4 ((accepted && Counting.NetworkCertificate.checkPairs ell pairs)::tail)

theorem loop_executes (data : Fin 30→List Bool) (ell : Nat)
    (pairs : List (Executable.Vista × Encoding.TwoOrderData)) (viewSuffix witnessSuffix : List Bool)
    (accepted : Bool) (tail : List Bool) (status : data 4=accepted::tail)
    (leader : data 2=Encoding.natural.encode ell)
    (views : data 10=Encoding.sequence Encoding.vista (pairs.map Prod.fst)++viewSuffix)
    (certs : data 11=Encoding.sequence Encoding.twoOrderWitness (pairs.map Prod.snd)++witnessSuffix)
    (empty : ∀r:Fin 30,r∈([0,1,3,5,6,7,9]:List (Fin 30)) → data r=[])
    (bits : List Bool) (counter : data 12=bits) (count : bits.length=pairs.length)
    (bound : Nat) (bounded : ∀r,(data r).length≤bound)
    (payload : (data 10).length+(data 11).length+(data 2).length≤bound) :
    ∃ time ≤ pairs.length*(Complexity.polynomial itemCoefficient 25 bound+2)+1,
      Executes loop (file data) time
        (file (loopResult data viewSuffix witnessSuffix accepted tail ell pairs)) := by
  induction pairs generalizing data accepted bits with
  | nil =>
    have bitsNil : bits=[] := List.length_eq_zero_iff.mp count
    have atCounter : file data (context 12)=[] := by simp [counter,bitsNil]
    obtain ⟨run,halt⟩ := repeat_empty (context 12) item (file data) atCounter
    have v : data 10=viewSuffix := by simpa only [List.map_nil,Encoding.sequence,List.nil_append] using views
    have c : data 11=witnessSuffix := by simpa only [List.map_nil,Encoding.sequence,List.nil_append] using certs
    have final : loopResult data viewSuffix witnessSuffix accepted tail ell []=data := by
      funext r
      by_cases r4 : r=4 <;> by_cases r10 : r=10 <;> by_cases r11 : r=11 <;> by_cases r12 : r=12 <;>
        simp [loopResult,Counting.NetworkCertificate.checkPairs,r4,r10,r11,r12,status,v,c,counter,bitsNil]
    refine ⟨1,by simp,⟨1,file data⟩,run,halt,?_⟩
    rw [final]
  | cons pair pairs ih =>
    rcases pair with ⟨vista,certificate⟩
    cases bits with
    | nil => simp at count
    | cons bit bits =>
      let consumed := Function.update data 12 bits
      let restV := Encoding.sequence Encoding.vista (pairs.map Prod.fst)++viewSuffix
      let restC := Encoding.sequence Encoding.twoOrderWitness (pairs.map Prod.snd)++witnessSuffix
      have viewInput : consumed 10=Encoding.vista.encode vista++restV := by
        simpa only [consumed,Function.update_of_ne (by decide : (10:Fin 30)≠12),
          List.map_cons,Encoding.sequence,List.append_assoc] using views
      have certInput : consumed 11=Encoding.twoOrderWitness.encode certificate++restC := by
        simpa only [consumed,Function.update_of_ne (by decide : (11:Fin 30)≠12),
          List.map_cons,Encoding.sequence,List.append_assoc] using certs
      have consumedBound : ∀r,(consumed r).length≤bound := by
        intro r
        by_cases same : r=12
        · subst r;have := bounded 12;rw [counter,List.length_cons] at this;simp only [consumed,Function.update_self];omega
        · simpa only [consumed,Function.update_of_ne same] using bounded r
      have itemPayload : (Encoding.vista.encode vista).length+(Encoding.natural.encode ell).length+
          (Encoding.twoOrderWitness.encode certificate).length≤bound := by
        rw [views,certs,leader] at payload
        simp only [List.map_cons,Encoding.sequence,List.length_append] at payload
        omega
      obtain ⟨t0,b0,finish0,run0,halt0,store0⟩ := item_executes consumed vista ell certificate restV restC
        accepted tail (by simp [consumed,status]) (by simp [consumed,leader]) viewInput certInput
        (by
          intro r member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          all_goals simpa [consumed] using empty _ (by simp))
        bound consumedBound itemPayload
      let middle := itemResult consumed restV restC accepted tail vista ell certificate
      let nextAccepted := accepted && Encoding.verifyTwoOrders vista ell certificate
      have smallV : restV.length≤(data 10).length := by
        have := congrArg List.length viewInput
        simp only [consumed,Function.update_of_ne (by decide : (10:Fin 30)≠12),List.length_append] at this
        omega
      have smallC : restC.length≤(data 11).length := by
        have := congrArg List.length certInput
        simp only [consumed,Function.update_of_ne (by decide : (11:Fin 30)≠12),List.length_append] at this
        omega
      have middleBound : ∀r,(middle r).length≤bound := by
        intro r
        by_cases r4:r=4
        · subst r;have := bounded 4;rw [status] at this;simpa only [middle,itemResult,Function.update_self,List.length_cons] using this
        by_cases r10:r=10
        · subst r;simpa [middle,itemResult] using smallV.trans (bounded 10)
        by_cases r11:r=11
        · subst r;simpa [middle,itemResult] using smallC.trans (bounded 11)
        simpa [middle,itemResult,r4,r10,r11] using consumedBound r
      have nextPayload : (middle 10).length+(middle 11).length+(middle 2).length≤bound := by
        simp [middle,itemResult,consumed]
        have := payload
        omega
      obtain ⟨t1,b1,finish1,run1,halt1,store1⟩ := ih middle nextAccepted
        (by simp [middle,itemResult,nextAccepted]) (by simp [middle,itemResult,consumed,leader])
        (by simp [middle,itemResult,restV]) (by simp [middle,itemResult,restC])
        (by
          intro r member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          all_goals simpa [middle,itemResult,consumed] using empty _ (by simp))
        bits (by simp [middle,itemResult,consumed]) (by simpa using count) middleBound nextPayload
      have physicalCounter : file data (context 12)=bit::bits := by simp [counter]
      have firstRun := repeat_iteration (context 12) item (file data) bit bits physicalCounter t0 finish0
        (by simpa only [file_update] using run0) halt0
      have firstRun' : Machine.run (step loop.program) (t0+2) ⟨0,file data⟩=
          some ⟨0,finish0.store⟩ := firstRun
      have final : loopResult middle viewSuffix witnessSuffix nextAccepted tail ell pairs=
          loopResult data viewSuffix witnessSuffix accepted tail ell ((vista,certificate)::pairs) := by
        funext r
        by_cases r4:r=4 <;> by_cases r10:r=10 <;> by_cases r11:r=11 <;> by_cases r12:r=12 <;>
          simp [loopResult,middle,itemResult,consumed,nextAccepted,Counting.NetworkCertificate.checkPairs,
            r4,r10,r11,r12,Bool.and_assoc]
      refine ⟨t0+2+t1,?_,finish1,?_,halt1,?_⟩
      · simp only [List.length_cons];nlinarith
      · rw [Machine.run_add,firstRun',Option.bind_some,store0]
        exact run1
      · exact store1.trans (congrArg file final)

end Counting.StackMachine.NetworkCertificate
