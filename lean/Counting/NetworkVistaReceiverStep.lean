import Counting.NetworkVistaReceiverPrepare
import Counting.NetworkVistaReceiverCall

namespace Counting.StackMachine.NetworkVista.Receiver
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

def step : Routine 128 := sequence prepare rawCall

def stepCoefficient : Nat := DagUpdate.Raw.completeCoefficient*8^61+1000000010

def receiverUpdated (n depth : Nat) (leaders : Fin n→Bool) (views : Fin n→Executable.Vista)
    (graph : Simulation.RoundGraph) (receiver : Fin n) :=
  DagUpdate.Raw.updated depth (leaders receiver) (receiverDegree graph receiver) (views receiver)
    (receiverMessages n graph views receiver)

theorem step_executes (data : Fin 30→List Bool) (n depth : Nat)
    (leaders : Fin n→Bool) (views : Fin n→Executable.Vista) (graph : Simulation.RoundGraph) (receiver : Fin n)
    (shape : Encoding.matrixShape n graph=true)
    (depthAt : data 0=Encoding.natural.encode depth)
    (leadersAt : data 1=(Encoding.array Encoding.boolean).encode (Array.ofFn leaders))
    (viewsAt : data 2=(Encoding.array Encoding.vista).encode (Array.ofFn views))
    (graphAt : data 3=(Encoding.array (Encoding.array Encoding.natural)).encode graph)
    (position : (data 4).length=receiver.val)
    (empty : ∀r:Fin 30,7≤r.val → r.val≤15 → data r=[])
    (B : Nat) (positive : 1≤B) (population : n≤B) (bounded : ∀r,(data r).length≤B) :
    ∃ time ≤ Complexity.polynomial stepCoefficient 61 B,
      Executes step (file data) time
        (file (Function.update data 7 (Encoding.vista.encode (receiverUpdated n depth leaders views graph receiver)))) := by
  obtain ⟨t0,b0,r0,size⟩ := prepare_executes data n depth leaders views graph receiver shape
    depthAt leadersAt viewsAt graphAt position empty B positive population bounded
  let ready := Function.update data 13 (readyWord n depth leaders views graph receiver)
  obtain ⟨t1,b1,r1⟩ := rawCall_executes ready depth (receiverDegree graph receiver) (leaders receiver)
    (views receiver) (receiverMessages n graph views receiver) (by simp [ready,readyWord])
    (by simp [ready,empty 7 (by decide) (by decide)])
  have final : Function.update (Function.update ready 13 []) 7
        (Encoding.vista.encode (receiverUpdated n depth leaders views graph receiver))=
      Function.update data 7 (Encoding.vista.encode (receiverUpdated n depth leaders views graph receiver)) := by
    have restore : Function.update data 13 []=data := by
      funext r
      by_cases same:r=13
      · subst r;simp [empty 13 (by decide) (by decide)]
      · simp [same]
    simp only [ready,Function.update_idem,restore]
  change Executes rawCall (file ready) t1 (file (Function.update (Function.update ready 13 []) 7
    (Encoding.vista.encode (receiverUpdated n depth leaders views graph receiver)))) at r1
  rw [final] at r1
  have big : (readyWord n depth leaders views graph receiver).length+1≤8*(B+1) := by omega
  have power := Nat.pow_le_pow_left big 61
  rw [Nat.mul_pow] at power
  have lifted := Nat.mul_le_mul_left DagUpdate.Raw.completeCoefficient power
  have p6 : (B+1)^6≤(B+1)^61 := Nat.pow_le_pow_right (by omega) (by decide)
  have one : 1≤(B+1)^61 := Nat.one_le_pow _ _ (by omega)
  have firstBound := b0.trans (Nat.mul_le_mul_left 1000000000 p6)
  change t1≤DagUpdate.Raw.completeCoefficient*((readyWord n depth leaders views graph receiver).length+1)^61 at b1
  have rawBound : t1≤(DagUpdate.Raw.completeCoefficient*8^61)*(B+1)^61 :=
    b1.trans (by simpa only [←Nat.mul_assoc] using lifted)
  refine ⟨t0+1+t1,?_,r0.sequence r1⟩
  change t0+1+t1≤(DagUpdate.Raw.completeCoefficient*8^61+1000000010)*(B+1)^61
  rw [Nat.add_mul]
  omega

theorem receiverUpdated_eq_rawUpdate (n depth : Nat) (leaders : Fin n→Bool) (views : Fin n→Executable.Vista)
    (graph : Simulation.RoundGraph) (receiver : Fin n)
    (valid : ∀agent,(views agent).valid=true)
    (levels : ∀agent,((views agent).node (views agent).bottom).level=depth)
    (labels : ∀agent,((views agent).node (views agent).bottom).leader=leaders agent) :
    receiverUpdated n depth leaders views graph receiver=
      Executable.rawUpdate (views receiver) (receiverMessages n graph views receiver) (receiverDegree graph receiver) := by
  apply DagUpdate.Raw.updated_eq_rawUpdate depth (leaders receiver) (receiverDegree graph receiver)
    (views receiver) (receiverMessages n graph views receiver) (valid receiver) (levels receiver) (labels receiver)
  intro message member
  obtain ⟨sender,_,_,rfl⟩ := Executable.mem_senderBundles _ _ _ _ _ member
  exact ⟨valid sender,levels sender⟩

end Counting.StackMachine.NetworkVista.Receiver
