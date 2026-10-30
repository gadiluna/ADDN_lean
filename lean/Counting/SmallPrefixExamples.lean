import Counting.SmallFullPrefix

namespace Counting.SmallPrefix.Examples

def cycle : Fin 4 → Fin 4 → Nat := fun a b => if (a.val + 1) % 4 = b.val then 1 else 0
def visible : Finset (Fin 4) := {0, 1}

/-- An ordinary hidden agent keeps degree D and receives exactly one hub
message; the visible agents keep the original cycle degree. -/
theorem four_agent_degrees :
    (∑ b, normalize cycle visible 2 5 0 b) = 1 ∧
    (∑ b, normalize cycle visible 2 5 1 b) = 1 ∧
    (∑ b, normalize cycle visible 2 5 3 b) = 5 := by decide

theorem four_agent_hidden_column : ∀ a : Fin 4,
    normalize cycle visible 2 5 a 3 = if a = 2 then 1 else 0 := by decide

theorem four_agent_visible_columns : ∀ a : Fin 4,
    normalize cycle visible 2 5 a 0 = cycle a 0 ∧
    normalize cycle visible 2 5 a 1 = cycle a 1 := by decide

/-- Zero arcs are admissible for a singleton, and the normal-form theorem
preserves its observer history at every depth, including depth zero. -/
theorem singleton_zero_arcs (t : Nat) :
    history (network (fun _ (_ _ : Unit) => 0) (fun _ => true) t
      (history (fun _ (_ _ : Unit) => 0) (fun _ => true) t ())) (fun _ => true) t () =
      history (fun _ (_ _ : Unit) => 0) (fun _ => true) t () :=
  network_observer _ _ t ()

theorem binary_table_roundtrip (rows : List (List (List Nat))) :
    tableCodec.decode (tableCodec.encode rows) = some (rows, []) := by
  simpa using tableCodec.roundtrip rows []

end Counting.SmallPrefix.Examples
