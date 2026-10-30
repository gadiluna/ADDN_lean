import Counting.StackEncodingParserNatural
import Counting.StackEncodingParserBoolean
import Counting.StackEncodingParserTransport
import Counting.StackEncodingParserList
import Counting.EncodingDag

/-! Concrete compositional parsers of the exact node and DAG binary codecs.
These check serialization and canonical fields; graph consistency is a
separate validator and is not asserted by these parsing theorems. -/
namespace Counting.StackMachine.EncodingPrograms.DagParser

set_option backward.isDefEq.respectTransparency false

def naturalRoles : ListWorkspace 9 where
  toFun i := ![0,3,5,1,6,9,2,10] i
  inj' := by decide

def innerRoles : FullListWorkspace 0 where
  toFun i := ![0,1,3,4,7,5,2,8,6,9,10,11,12,13,14,15,16] i
  inj' := by decide

def outerRoles : FullListWorkspace 0 where
  toFun i := ![0,1,3,4,8,5,2,7,6,9,10,11,12,13,14,15,16] i
  inj' := by decide

def natural : VerifiedParser 15 0 1 2 Nat Encoding.natural := naturalParser 9 naturalRoles

def boolean : VerifiedParser 15 0 1 2 Bool Encoding.boolean := booleanParser 15 0 1 2 (by decide) (by decide) (by decide)

def optionalNatural : VerifiedParser 15 0 1 2 (Option Nat) Encoding.optionalNatural :=
  natural.transport (fun value => value.map (·+1) |>.getD 0)
    (fun n => match n with | 0 => none | n+1 => some n)
    (by intro value;cases value <;> rfl)
    (by intro value;cases value <;> rfl)

def naturalPair : VerifiedParser 15 0 1 2 (Nat×Nat) (Encoding.product Encoding.natural Encoding.natural) :=
  natural.product (by decide) (by decide) (by decide) natural

def incoming : VerifiedParser 15 0 1 2 (List (Nat×Nat)) (Encoding.list (Encoding.product Encoding.natural Encoding.natural)) :=
  listParser 0 innerRoles naturalPair (by decide) (by
    intro value
    simp only [Encoding.product,List.length_append,Encoding.natural_length]
    omega)

def nodeFields : VerifiedParser 15 0 1 2 Encoding.NodeFields Encoding.nodeFields :=
  natural.product (by decide) (by decide) (by decide)
    (optionalNatural.product (by decide) (by decide) (by decide)
      (boolean.product (by decide) (by decide) (by decide)
        (natural.product (by decide) (by decide) (by decide) incoming)))

def node : VerifiedParser 15 0 1 2 Executable.Node Encoding.node :=
  nodeFields.transport (β := Executable.Node) (fun n => (n.level,n.parent,n.leader,n.degree,n.incoming))
    (fun fields => ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,fields.2.2.2.2⟩)
    (by intro value;rfl)
    (by intro value;rcases value with ⟨a,b,c,d,e⟩;rfl)

def nodes : VerifiedParser 15 0 1 2 (List Executable.Node) (Encoding.list Encoding.node) :=
  listParser 0 outerRoles node (by decide) (by
    intro value
    rw [Encoding.node_length]
    unfold Encoding.nodeBits
    omega)

def vistaFields : VerifiedParser 15 0 1 2 (List Executable.Node×Nat)
    (Encoding.product (Encoding.list Encoding.node) Encoding.natural) :=
  nodes.product (by decide) (by decide) (by decide) natural

def vista : VerifiedParser 15 0 1 2 Executable.Vista Encoding.vista :=
  vistaFields.transport (β := Executable.Vista) (fun v => (v.nodes.toList,v.bottom))
    (fun fields => ⟨fields.1.toArray,fields.2⟩)
    (by intro value;cases value;simp)
    (by intro value;cases value;simp)

def naturals : VerifiedParser 15 0 1 2 (List Nat) (Encoding.list Encoding.natural) :=
  listParser 0 innerRoles natural (by decide) (by intro value;rw [Encoding.natural_length];omega)

def verifierInput : VerifiedParser 15 0 1 2 (Executable.Vista × List Nat × Nat × Nat) Encoding.verifierInput :=
  vista.product (by decide) (by decide) (by decide)
    (naturals.product (by decide) (by decide) (by decide)
      (natural.product (by decide) (by decide) (by decide) natural))

/-- Every raw input has a polynomially bounded execution; acceptance means
exactly a canonical encoded vista prefix, with no graph-validity inference. -/
theorem vista_accepts_iff (input : List Bool) :
    (vista.effect input).accepted=true ↔ ∃ value suffix, Encoding.vista.encode value++suffix=input :=
  vista.accepts_iff input

theorem vista_coefficient : vista.coefficient=3890 := rfl

theorem vista_exponent : vista.exponent=4 := rfl

end Counting.StackMachine.EncodingPrograms.DagParser
