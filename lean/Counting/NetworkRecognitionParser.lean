import Counting.StackEncodingDagParser
import Counting.StackEncodingParserRecognition
import Counting.StackCompilerComplete
import Counting.EncodingNetworkSemantics

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- The explicit universe and every matrix dimension are parsed from their
actual list headers. This parser checks canonical serialization only. -/
def arrayParser {α : Type} {codec : Encoding.Codec α} (w : FullListWorkspace 0)
    (parser : VerifiedParser 15 (w 0) (w 1) (w 6) α codec) (unused : w 4∉parser.work)
    (positive : ∀value,0<(codec.encode value).length) :
    VerifiedParser 15 (w 0) (w 1) (w 6) (Array α) (Encoding.array codec) :=
  (listParser 0 w parser unused positive).transport Array.toList List.toArray
    (by intro values;simp) (by intro values;simp)

def booleans : VerifiedParser 15 0 1 2 (Array Bool) (Encoding.array Encoding.boolean) :=
  arrayParser DagParser.innerRoles DagParser.boolean (by decide) (by intro value;simp [Encoding.boolean])

def row : VerifiedParser 15 0 1 2 (Array Nat) (Encoding.array Encoding.natural) :=
  arrayParser DagParser.innerRoles DagParser.natural (by decide) (by intro value;rw [Encoding.natural_length];omega)

def matrix : VerifiedParser 15 0 1 2 (Array (Array Nat)) (Encoding.array (Encoding.array Encoding.natural)) :=
  arrayParser DagParser.outerRoles row (by decide) (Encoding.array_length_positive Encoding.natural)

def roundRoles : FullListWorkspace 0 := ⟨![0,1,3,4,10,5,2,7,6,9,8,11,12,13,14,15,16],by decide⟩

def rounds : VerifiedParser 15 0 1 2 (Array (Array (Array Nat)))
    (Encoding.array (Encoding.array (Encoding.array Encoding.natural))) :=
  arrayParser roundRoles matrix (by decide) (Encoding.array_length_positive (Encoding.array Encoding.natural))

def fields := booleans.product (by decide) (by decide) (by decide) rounds

def parser : VerifiedParser 15 0 1 2 Simulation.Input Encoding.networkInput :=
  fields.transport (β:=Simulation.Input) (fun input => (input.leaders,input.rounds)) (fun fields => ⟨fields.1,fields.2⟩)
    (by intro input;rfl) (by intro fields;cases fields;rfl)

theorem parser_accepts_iff (input : List Bool) :
    (parser.effect input).accepted=true ↔ ∃network suffix,Encoding.networkInput.encode network++suffix=input :=
  parser.accepts_iff input

def syntaxMachine : Machine.Program := Compiler.compile parser.recognition.program

theorem syntaxMachine_computes : Complexity.ComputesCleanIn syntaxMachine
    (fun input=>[(Encoding.networkInput.decodeExact input).isSome])
    (Complexity.polynomial (20*(parser.coefficient+40)^2) (2*(max 1 parser.exponent+1))) :=
  Compiler.computesCleanIn_polynomial _ _ parser.recognition_computes

end Counting.StackMachine.NetworkRecognition
