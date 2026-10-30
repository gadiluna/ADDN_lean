import Counting.DagKeyOrder
import Counting.EncodingDag

namespace Counting.Executable

theorem sequence_key (node : Node) :
    Encoding.sequence Encoding.natural node.key=
      Encoding.natural.encode node.level++
      Encoding.natural.encode (if node.leader then 1 else 0)++
      Encoding.natural.encode ((node.parent.map (·+1)).getD 0)++
      Encoding.natural.encode node.degree++
      Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) node.incoming := by
  have edges (incoming : List (Nat×Nat)) :
      Encoding.sequence Encoding.natural (incoming.flatMap (fun edge=>[edge.1,edge.2]))=
        Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) incoming := by
    induction incoming with
    | nil => rfl
    | cons edge rest ih => simp [Encoding.sequence,Encoding.product,List.append_assoc,ih]
  simp only [Node.key,List.cons_append,List.nil_append,Encoding.sequence,edges]
  simp only [List.append_assoc]

end Counting.Executable
