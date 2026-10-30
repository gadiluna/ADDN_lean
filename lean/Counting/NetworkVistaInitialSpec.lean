import Counting.NetworkVistaInitial
import Counting.EncodingNetworkViews

namespace Counting.StackMachine.NetworkVista
open Routine

/-- The actual tabulated simulator starts with exactly one canonical
initial DAG for each explicitly listed initial label. -/
theorem initialArray_actual (input:Simulation.Input) :
    Encoding.inputVistaArrayRun input 0=input.leaders.map Executable.initialVista := by
  change Array.ofFn (fun i:Fin input.leaders.size=>Executable.initialVista input.leaders[i.val])=_
  have mapped:=Array.map_ofFn (f:=fun i:Fin input.leaders.size=>input.leaders[i.val])
    (g:=Executable.initialVista)
  simpa only [Array.ofFn_getElem,Function.comp_def] using mapped.symm

theorem initialArray_encoded (input:Simulation.Input) :
    (Encoding.array Encoding.vista).encode (Encoding.inputVistaArrayRun input 0)=
      (Encoding.list Encoding.vista).encode (input.leaders.toList.map Executable.initialVista) := by
  rw [initialArray_actual]
  simp only [Encoding.array,Encoding.transport,Array.toList_map]

/-- On the actual binary network input, the concrete initializer leaves
the encoded round sequence untouched and emits the simulator's initial
array. Its unary population counter is computed from the explicit list. -/
theorem initialPrefix_network (store:Store 19) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (work:∀r:Fin 21,r.val<17 → r≠1 → store r=[])
    (e18:store 18=[]) (e19:store 19=[]) (e20:store 20=[])
    (input:Simulation.Input) (suffix:List Bool)
    (encoded:store 17=Encoding.networkInput.encode input++suffix) :
    ∃time ≤ 2000*((store 17).length+1)^3,
      Routine.Executes initialPrefix store time
        (Function.update
          (Function.update
            (Function.update store 17
              ((Encoding.array (Encoding.array (Encoding.array Encoding.natural))).encode input.rounds++suffix))
            0 (List.replicate input.leaders.size true))
          20 ((Encoding.array Encoding.vista).encode (Encoding.inputVistaArrayRun input 0))) := by
  obtain ⟨time,bound,run⟩:=initialPrefix_executes store accepted tail status work e18 e19 e20
    input.leaders.toList
    ((Encoding.array (Encoding.array (Encoding.array Encoding.natural))).encode input.rounds++suffix)
    (by rw [encoded];simp only [Encoding.networkInput,Encoding.transport,Encoding.product,
        Encoding.array,List.append_assoc])
  refine ⟨time,bound,?_⟩
  simpa only [initialPrefixStore,Array.length_toList,initialArray_encoded] using run

end Counting.StackMachine.NetworkVista
