import Counting.NetworkVistaRead
import Counting.NetworkRecognitionParser

namespace Counting.StackMachine.NetworkVista.Reader
open Routine EncodingPrograms

theorem preservingRead_executes_polynomial {α:Type} {codec:Encoding.Codec α}
    (parser:VerifiedParser 15 0 1 2 α codec) (store:Store 19) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail)
    (work:∀r:Fin 17,r≠1 → store (parserRoles r)=[])
    (output:store 19=[]) (scratch:store 20=[]) :
    ∃time ≤ (3*parser.coefficient+14)*((store 17).length+(store 18).length+1)^(parser.exponent+1),
      Executes (preservingRead parser) store time
        (preservingStore store accepted tail (readEffect parser.effect (store 18).length (store 17))) := by
  obtain ⟨time,bound,run⟩:=preservingRead_executes parser store accepted tail status work output scratch
  let S:=(store 17).length+(store 18).length+1
  have positive:1≤S:=by dsimp [S];omega
  have power:((store 17).length+1)^parser.exponent≤S^parser.exponent:=by dsimp [S];gcongr;omega
  have factor:2*(store 18).length+3≤3*S:=by dsimp [S];omega
  have linear:S≤S^(parser.exponent+1):=Nat.le_self_pow (by omega) _
  have remainder:6*(store 17).length+7*(store 18).length+14≤14*S:=by dsimp [S];omega
  unfold Complexity.polynomial at bound
  have product:(2*(store 18).length+3)*(parser.coefficient*((store 17).length+1)^parser.exponent)≤
      3*S*(parser.coefficient*S^parser.exponent):=by gcongr
  have rearrange:3*S*(parser.coefficient*S^parser.exponent)=3*parser.coefficient*S^(parser.exponent+1):=by
    rw [pow_succ];ring
  rw [rearrange] at product
  refine ⟨time,?_,run⟩
  change time≤(3*parser.coefficient+14)*S^(parser.exponent+1)
  nlinarith

end Counting.StackMachine.NetworkVista.Reader
