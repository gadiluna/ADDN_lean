import Counting.EncodingNetworkRecognition

namespace Counting.Encoding.NetworkRecognitionTests

private def require (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"Network recognition test failed: {name}")

def tests : IO Unit := do
  let depthZero : Simulation.Input := ⟨#[true], #[]⟩
  let depthOne : Simulation.Input := ⟨#[true], #[#[#[0]]]⟩
  let ambiguous : List TwoOrderData := [((1,[1]),(2,[1]))]
  let previous := networkWitness.encode ambiguous
  require "malformed network belongs to complement" (binaryNetworkComplementVerifier [] [])
  require "inadmissible network belongs to complement"
    (binaryNetworkComplementVerifier (networkInput.encode ⟨#[false], #[]⟩) [true])
  require "depth-zero singleton admits orders one and two"
    (binaryNetworkComplementVerifier (networkInput.encode depthZero) previous)
  require "depth-one zero-edge singleton rejects previous witness"
    (!(binaryNetworkComplementVerifier (networkInput.encode depthOne) previous))
  require "depth-one order one certificate accepted"
    (RealizabilityVerifier.verify (agentVista depthOne ⟨0, by decide⟩) #[1,1] 1 1)
  require "depth-one order two certificate rejected despite correct array length"
    (!(RealizabilityVerifier.verify (agentVista depthOne ⟨0, by decide⟩) #[1,1] 1 2))
  require "depth-one pair with matching count lengths rejected"
    (!(binaryNetworkComplementVerifier (networkInput.encode depthOne)
      (networkWitness.encode [((1,[1,1]),(2,[1,1]))])))
  require "malformed witness payload rejected on valid input"
    (!(binaryNetworkComplementVerifier (networkInput.encode depthZero) []))
  require "wrong number of agent certificates rejected"
    (!(binaryNetworkComplementVerifier (networkInput.encode depthZero) (networkWitness.encode [])))
  require "identical orders rejected"
    (!(binaryNetworkComplementVerifier (networkInput.encode depthZero)
      (networkWitness.encode [((1,[1]),(1,[1]))])))
  require "zero anonymity rejected"
    (!(binaryNetworkComplementVerifier (networkInput.encode depthZero)
      (networkWitness.encode [((1,[0]),(2,[1]))])))
  require "trailing witness bits rejected"
    (!(binaryNetworkComplementVerifier (networkInput.encode depthZero) (previous ++ [true])))
  IO.println "Binary network recognition tests passed (12 boundary and certificate cases)."

#eval tests
end Counting.Encoding.NetworkRecognitionTests
