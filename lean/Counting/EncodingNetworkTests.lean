import Counting.EncodingNetworkProperties

/-! Executed checks of the binary boundary and the actual cached DAG
reconstruction. General correctness is proved in EncodingNetworkViews. -/
namespace Counting.Encoding.NetworkTests
open Executable Simulation

private def require (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"Binary network test failed: {name}")

private def check (name : String) (input : Input) : IO Unit := do
  require s!"{name}: validation" (networkValid input)
  require s!"{name}: exact binary roundtrip" (decodeNetwork? (networkInput.encode input) == some input)
  let views := inputVistas input
  require s!"{name}: number of views" (views.size == input.leaders.size)
  require s!"{name}: valid shared DAGs" (views.all fun v => v.valid)
  require s!"{name}: final depth" (views.all fun v => (v.node v.bottom).level == input.rounds.size)
  for v in views do
    require s!"{name}: vista codec roundtrip" (vista.decodeExact (vista.encode v) == some v)

def tests : IO Unit := do
  check "depth zero" ⟨#[true], #[]⟩
  check "zero-edge singleton" ⟨#[true], #[#[#[0]], #[#[0]]]⟩
  check "large binary loops" ⟨#[true], #[#[#[2^100]], #[#[3]] ]⟩
  check "all leaders" ⟨#[true,true], #[#[#[0,1],#[1,0]], #[#[2,1],#[1,0]]]⟩
  check "one leader directed cycle" ⟨#[true,false,false], #[#[#[0,1,0],#[0,0,1],#[1,0,0]]]⟩
  check "several leaders" ⟨#[true,true,false], #[#[#[0,2,0],#[0,0,3],#[1,0,0]]]⟩
  require "empty population rejected" (!(networkValid ⟨#[], #[]⟩))
  require "zero leaders rejected" (!(networkValid ⟨#[false], #[]⟩))
  require "wrong row count rejected" (!(networkValid ⟨#[true], #[#[]]⟩))
  require "wrong column count rejected" (!(networkValid ⟨#[true], #[#[#[0,1]]]⟩))
  require "disconnected graph rejected" (!(networkValid ⟨#[true,false], #[#[#[1,0],#[0,1]]]⟩))
  require "invalid network binary rejected"
    ((decodeNetwork? (networkInput.encode ⟨#[true,false], #[#[#[1,0],#[0,1]]]⟩)).isNone)
  require "empty binary rejected" ((decodeNetwork? []).isNone)
  require "trailing bits rejected" ((decodeNetwork? (networkInput.encode ⟨#[true], #[]⟩ ++ [true])).isNone)
  IO.println "Binary network tests passed (6 valid reconstructions, 8 malformed/model-invalid cases)."

#eval tests
end Counting.Encoding.NetworkTests
