import Counting.ExternalReductionChain

namespace Counting.External.Examples

def positive : CNF 1 := [[⟨0, true⟩]]
def negative : CNF 1 := [[⟨0, true⟩], [⟨0, false⟩]]
def emptyClause : CNF 0 := [[]]
def emptyFormula : CNF 0 := []
def repeatedClause : CNF 1 := [[⟨0, true⟩, ⟨0, false⟩, ⟨0, true⟩, ⟨0, false⟩]]

#guard decide (∃ assignment, positive.eval assignment = true)
#guard !(decide (∃ assignment, negative.eval assignment = true))
#guard !(decide (∃ assignment, emptyClause.eval assignment = true))
#guard decide (∃ assignment, emptyFormula.eval assignment = true)

#guard decide (∃ assignment, positive.toThreeSAT.Satisfies assignment)
#guard !(decide (∃ assignment, negative.toThreeSAT.Satisfies assignment))
#guard !(decide (∃ assignment, emptyClause.toThreeSAT.Satisfies assignment))
#guard decide (∃ assignment, emptyFormula.toThreeSAT.Satisfies assignment)
#guard decide (∃ assignment, repeatedClause.toThreeSAT.Satisfies assignment)

def oneClause : ThreeSAT 1 1 := ⟨fun _ _ => ⟨0, true⟩⟩

#guard (allowedIndices 8 oneClause.indexedArc).card ≤ 8 ^ 3
#guard oneClause.toThreeDM.toX3C.kept.card ≤ 8 ^ 3

end Counting.External.Examples
