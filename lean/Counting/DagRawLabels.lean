import Counting.DagRawArray

namespace Counting.Executable

theorem rawUpdate_bottom_leader (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) :
    ((rawUpdate old messages degree).node (rawUpdate old messages degree).bottom).leader =
      (old.node old.bottom).leader := by
  unfold rawUpdate
  rw [node_push_last]

end Counting.Executable

namespace Counting.Encoding
open Executable

/-- The offline input's original Boolean label is exactly the local
receiver label retained by every raw update. -/
theorem rawInputVistaRun_leader (input : Simulation.Input) (depth : Nat) (receiver : InputAgent input) :
    ((rawInputVistaRun input depth receiver).node (rawInputVistaRun input depth receiver).bottom).leader =
      inputLeader input receiver := by
  induction depth with
  | zero => simp [rawInputVistaRun,initialVista,Vista.node]
  | succ depth ih => simpa only [rawInputVistaRun,rawUpdate_bottom_leader] using ih

end Counting.Encoding
