import Counting.ExternalInitialPredicate
import Mathlib.Data.Fintype.Card

namespace Counting.External.CookLevin.StackGenerator
open FiniteConstraints

def InitialSymbolKind.allowedCount : InitialSymbolKind → Nat
  | .witness => 3
  | _ => 1

def allowedSymbolEquiv (program : Machine.Program) (head : Bool) (kind : InitialSymbolKind) :
    {v : Fin (Cellular.alphabet program) // initialAllowed program head kind v = true} ≃
      {s : Machine.Symbol // kind.allowed s} where
  toFun v := ⟨((Cellular.cellEquiv program).symm v.val).1, by
    have property := v.property
    simp only [initialAllowed,decide_eq_true_eq] at property
    exact property.2⟩
  invFun s := ⟨Cellular.cellEquiv program (s.val,if head then some 0 else none), by
    simp only [initialAllowed,Equiv.symm_apply_apply,decide_eq_true_eq]
    exact ⟨trivial,s.property⟩⟩
  left_inv v := by
    apply Subtype.ext
    have property := v.property
    simp only [initialAllowed,decide_eq_true_eq] at property
    apply (Cellular.cellEquiv program).symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Prod.ext rfl property.1.symm
  right_inv s := by
    apply Subtype.ext
    exact congrArg Prod.fst ((Cellular.cellEquiv program).symm_apply_apply _)

theorem initialAllowed_card (program : Machine.Program) (head : Bool) (kind : InitialSymbolKind) :
    Fintype.card {v : Fin (Cellular.alphabet program) // initialAllowed program head kind v = true} =
      kind.allowedCount := by
  rw [Fintype.card_congr (allowedSymbolEquiv program head kind)]
  cases kind <;> decide

theorem finRange_filter_card (n : Nat) (predicate : Fin n → Bool) :
    ((List.finRange n).filter predicate).length = Fintype.card {v : Fin n // predicate v = true} := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter predicate),Fintype.card_subtype]
  congr 1
  ext v
  simp

theorem tuples_one (alphabet : Nat) :
    tuples alphabet 1 = (List.finRange alphabet).map (fun value => fun _ : Fin 1 => value) := by
  simp only [tuples,List.map_singleton]
  rw [← List.map_eq_flatMap]
  apply List.map_congr_left
  intro value _
  funext i
  fin_cases i
  rfl

theorem unaryTemplate_length (alphabet : Nat) (allowed : Fin alphabet → Bool) :
    (unaryTemplate alphabet allowed).length =
      alphabet-Fintype.card {v : Fin alphabet // allowed v = true} := by
  simp only [unaryTemplate,List.length_map,tuples_one,List.filter_map,Function.comp_def,List.length_map]
  rw [finRange_filter_card]
  let complement : {v : Fin alphabet // (!allowed v)=true} ≃
      {v : Fin alphabet // ¬allowed v=true} :=
    Equiv.subtypeEquivRight (fun v => by cases allowed v <;> decide)
  rw [Fintype.card_congr complement,Fintype.card_subtype_compl,Fintype.card_fin]

theorem initialUnaryTemplate_length (program : Machine.Program) (head : Bool) (kind : InitialSymbolKind) :
    (unaryTemplate (Cellular.alphabet program) (initialAllowed program head kind)).length =
      Cellular.alphabet program-kind.allowedCount := by
  rw [unaryTemplate_length,initialAllowed_card]

end Counting.External.CookLevin.StackGenerator
