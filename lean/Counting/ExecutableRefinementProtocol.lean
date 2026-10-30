import Counting.ExecutableRefinementSchedule
import Counting.DagSemanticsPhysical

namespace Counting.Executable
open scoped BigOperators

/-- Mathematical multiset adapter for the protocol interface. This adapter
is proof-only: the executable updater already accepts compact binary bundles.
Each physical packet is represented once here, without exposing sender IDs. -/
noncomputable def protocolPackets (messages : Multiset LocalState) : List (Vista × Nat) :=
  messages.toList.map (fun state => (state.vista, 1))

theorem protocolPackets_histories (messages : Multiset LocalState) (depth : Nat) :
    receivedHistories depth (protocolPackets messages) =
      messages.map (fun state => decodeNode state.vista depth state.vista.bottom) := by
  have helper : ∀ states : List LocalState,
      ((states.map (fun state => Multiset.replicate 1
        (decodeNode state.vista depth state.vista.bottom))).sum) =
      (states : Multiset LocalState).map (fun state => decodeNode state.vista depth state.vista.bottom) := by
    intro states
    induction states with
    | nil => rfl
    | cons state rest ih =>
        rw [List.map_cons, List.sum_cons, ih]
        simp
  simpa only [receivedHistories, protocolPackets, List.map_map, Function.comp_def,
    Multiset.coe_toList] using helper messages.toList

/-- The existing local program, placed in the paper's anonymous protocol
interface. Its error fallback is unreachable in the verified physical run. -/
noncomputable def executableProtocol : Counting.Protocol LocalState where
  init := initialState
  update := fun state messages degree => (advance? state (protocolPackets messages) degree).getD state
  out := fun state _ => state.output

structure StateRep (leaders depth : Nat) (H : Counting.FullHistory depth) (state : LocalState) : Prop where
  leaderCount : state.leaders = leaders
  valid : state.vista.valid = true
  level : (state.vista.node state.vista.bottom).level = depth
  history : decodeNode state.vista depth state.vista.bottom = H

theorem initialState_rep (leaders : Nat) (label : Bool) :
    StateRep leaders 0 label (initialState leaders label) := by
  exact ⟨rfl, initialVista_valid label, by simp [initialState, initialVista, Vista.node], rfl⟩

theorem scheduledOutput_history (leaders : Nat) (positive : 0 < leaders) (vista : Vista)
    (valid : vista.valid = true) (depth : Nat) (H : Counting.FullHistory depth)
    (level : (vista.node vista.bottom).level = depth)
    (history : decodeNode vista depth vista.bottom = H) :
    scheduledOutput leaders vista = Counting.TimingProtocol.optimizedDecision leaders depth H := by
  subst depth
  rw [scheduledOutput_optimized leaders vista positive valid]
  exact congrArg (Counting.TimingProtocol.optimizedDecision leaders _) history

theorem protocolPackets_valid (messages : Multiset LocalState) (leaders depth : Nat)
    (represented : ∀ state ∈ messages, ∃ H, StateRep leaders depth H state) :
    ∀ message ∈ protocolPackets messages,
      message.1.valid = true ∧ 0 < message.2 ∧ (message.1.node message.1.bottom).level = depth := by
  intro message present
  obtain ⟨state, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨H, rep⟩ := represented state (Multiset.mem_toList.mp member)
  exact ⟨rep.valid, by norm_num, rep.level⟩

/-- A physical all-active round runs the actual local `advance?` and obtains
exactly the mathematical decision on the newly reconstructed history. -/
theorem executable_update_physical {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth : Nat) (positive : 0 < ell)
    (states : V → LocalState)
    (represented : ∀ x, StateRep ell depth (Counting.history G leader depth x) (states x))
    (active : ∀ x, (states x).output = none) (receiver : V) :
    ∃ next, advance? (states receiver)
        (protocolPackets (Counting.incoming (G (depth + 1)) states receiver))
        (∑ sender, G (depth + 1) receiver sender) = some next ∧
      StateRep ell (depth + 1) (Counting.history G leader (depth + 1) receiver) next ∧
      next.output = Counting.TimingProtocol.optimizedDecision ell (depth + 1)
        (Counting.history G leader (depth + 1) receiver) := by
  classical
  let messages := Counting.incoming (G (depth + 1)) states receiver
  have allRepresented : ∀ state ∈ messages, ∃ H, StateRep ell depth H state := by
    intro state member
    have existsSender : ∃ sender, state = states sender := by
      unfold messages Counting.incoming at member
      obtain ⟨sender, _, hin⟩ := Multiset.mem_sum.mp member
      exact ⟨sender, (Multiset.mem_replicate.mp hin).2⟩
    obtain ⟨sender, rfl⟩ := existsSender
    exact ⟨_, represented sender⟩
  have packetValid := protocolPackets_valid messages ell depth allRepresented
  obtain ⟨vista, updated, vistaValid, vistaLevel⟩ := updateVista_total (states receiver).vista
    (protocolPackets messages) (∑ sender, G (depth + 1) receiver sender) (represented receiver).valid
    (by intro message hm; obtain ⟨hv, hp, hl⟩ := packetValid message hm
        exact ⟨hv, hp, hl.trans (represented receiver).level.symm⟩)
  have level : (vista.node vista.bottom).level = depth + 1 :=
    vistaLevel.trans (congrArg (fun t => t + 1) (represented receiver).level)
  have vistaHistory : decodeNode vista (depth + 1) vista.bottom =
      Counting.history G leader (depth + 1) receiver := by
    have sound := (updateVista_sound _ _ _ _ updated).2
    have oldLevel := (represented receiver).level
    subst depth
    rw [protocolPackets_histories] at sound
    have mapping : (fun sender => decodeNode (states sender).vista
        ((states receiver).vista.node (states receiver).vista.bottom).level (states sender).vista.bottom) =
        Counting.history G leader ((states receiver).vista.node (states receiver).vista.bottom).level := by
      funext sender
      exact (represented sender).history
    rw [Counting.incoming_map, mapping] at sound
    exact sound.trans (Prod.ext (represented receiver).history (Prod.ext rfl rfl))
  have output := scheduledOutput_history ell positive vista vistaValid (depth + 1)
    (Counting.history G leader (depth + 1) receiver) level vistaHistory
  let next : LocalState := { (states receiver) with
    vista := vista
    output := Counting.TimingProtocol.optimizedDecision ell (depth + 1)
      (Counting.history G leader (depth + 1) receiver) }
  refine ⟨next, ?_, ⟨(represented receiver).leaderCount, vistaValid, level, vistaHistory⟩, rfl⟩
  rw [advance_active_of_update _ _ _ vista (active receiver)
    (by rw [(represented receiver).leaderCount]; exact positive) updated,
    (represented receiver).leaderCount, output]
  simp only [next, (represented receiver).leaderCount]

/-- The silent protocol wrapper performs that same verified local step. -/
theorem executable_trace_step {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth : Nat) (positive : 0 < ell)
    (states : V → LocalState)
    (represented : ∀ x, StateRep ell depth (Counting.history G leader depth x) (states x))
    (active : ∀ x, (states x).output = none)
    (trace : ∀ x, executableProtocol.trace ell G leader depth x = .active (states x)) (receiver : V) :
    ∃ next, StateRep ell (depth + 1) (Counting.history G leader (depth + 1) receiver) next ∧
      next.output = Counting.TimingProtocol.optimizedDecision ell (depth + 1)
        (Counting.history G leader (depth + 1) receiver) ∧
      executableProtocol.trace ell G leader (depth + 1) receiver =
        match next.output with
        | none => .active next
        | some n => .halted next n := by
  obtain ⟨next, updated, rep, output⟩ := executable_update_physical G leader ell depth positive
    states represented active receiver
  refine ⟨next, rep, output, ?_⟩
  have all : executableProtocol.trace ell G leader depth = fun x => Counting.Status.active (states x) := funext trace
  rw [Counting.Protocol.trace, all, Counting.TimingProtocol.active_messages]
  simp only [Counting.Protocol.advance, executableProtocol, updated, Option.getD_some]
  rfl

end Counting.Executable
