import Counting.EncodingNetworkWitness

namespace Counting.NetworkCertificate
open Encoding

abbrev Input := Nat × List Executable.Vista × List TwoOrderData

def codec : Encoding.Codec Input :=
  Encoding.product Encoding.natural
    (Encoding.product (Encoding.list Encoding.vista) Encoding.networkWitness)

def checkPairs (ell : Nat) (pairs : List (Executable.Vista × TwoOrderData)) : Bool :=
  pairs.all (fun pair => Encoding.verifyTwoOrders pair.1 ell pair.2)

def check (ell : Nat) (views : List Executable.Vista) (certificates : List TwoOrderData) : Bool :=
  (views.length == certificates.length) && checkPairs ell (views.zip certificates)

def predicate (bits : List Bool) : Bool :=
  match codec.decodeExact bits with
  | none => false
  | some input => check input.1 input.2.1 input.2.2

theorem predicate_encoded (input : Input) : predicate (codec.encode input)=check input.1 input.2.1 input.2.2 := by
  rw [predicate,(codec.decodeExact_iff _ _).mpr rfl]

theorem predicate_malformed (bits : List Bool) (invalid : codec.decodeExact bits=none) :
    predicate bits=false := by simp [predicate,invalid]

theorem check_length_mismatch (ell : Nat) (views : List Executable.Vista)
    (certificates : List TwoOrderData) (different : views.length≠certificates.length) :
    check ell views certificates=false := by simp [check,different]

theorem check_empty (ell : Nat) : check ell [] []=true := rfl

theorem check_iff (ell : Nat) (views : List Executable.Vista) (certificates : List TwoOrderData) :
    check ell views certificates=true ↔
      views.length=certificates.length ∧ ∀ i : Fin views.length,
        ∃ certificate, certificates[i.val]?=some certificate ∧
          Encoding.verifyTwoOrders views[i.val] ell certificate=true := by
  simp only [check,Bool.and_eq_true,beq_iff_eq]
  apply and_congr_right
  intro same
  simp only [checkPairs,List.all_eq_true,List.forall_mem_iff_forall_getElem,
    List.length_zip,List.getElem_zip]
  constructor
  · intro checked i
    let certificate := certificates[i.val]'(by omega)
    refine ⟨certificate,by simp [certificate],?_⟩
    exact checked i.val (by omega)
  · intro checked i inside
    obtain ⟨certificate,lookup,accepted⟩ := checked ⟨i,by omega⟩
    have cert : certificates[i]'(by omega)=certificate := by
      exact (List.getElem?_eq_some_iff.mp lookup).2
    simpa only [cert] using accepted

theorem check_inputVistas (input : Simulation.Input) (certificates : List TwoOrderData) :
    check (Encoding.inputLeaderCount input) (Encoding.inputVistas input).toList certificates=
      Encoding.verifyNetworkWitness input certificates := by
  apply Bool.eq_iff_iff.mpr
  rw [check_iff,Encoding.verifyNetworkWitness_iff]
  constructor
  · rintro ⟨length,checked⟩
    refine ⟨by simpa using length.symm,?_⟩
    intro agent
    obtain ⟨certificate,lookup,accepted⟩ := checked ⟨agent.val,by simp⟩
    exact ⟨certificate,lookup,by simpa only [Encoding.agentVista,Array.getElem_toList] using accepted⟩
  · rintro ⟨length,checked⟩
    refine ⟨by simpa using length.symm,?_⟩
    intro agent
    obtain ⟨certificate,lookup,accepted⟩ := checked ⟨agent.val,by simpa using agent.isLt⟩
    exact ⟨certificate,lookup,by simpa only [Encoding.agentVista,Array.getElem_toList] using accepted⟩

end Counting.NetworkCertificate
