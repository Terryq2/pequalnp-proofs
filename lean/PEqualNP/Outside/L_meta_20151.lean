import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20151_aux

open PEqualNP.CircuitLowerBounds

def joinGate (a b : ℕ) : Gate := ⟨.or, [a,b]⟩
def meetGate (a b : ℕ) : Gate := ⟨.and, [a,b]⟩

def witness : Circuit := ⟨[
  joinGate 0 7, joinGate 2 4, joinGate 3 5, joinGate 1 4,
  joinGate 5 19, joinGate 6 17, joinGate 1 2, joinGate 3 22,
  joinGate 0 1, joinGate 6 7,
  joinGate 9 14, joinGate 13 15, joinGate 8 10, joinGate 11 27,
  joinGate 14 15, joinGate 8 11, joinGate 13 26, joinGate 26 31,
  joinGate 9 12, joinGate 10 12,
  meetGate 18 32, meetGate 20 28, meetGate 16 33, meetGate 25 34,
  meetGate 23 35, meetGate 24 30, meetGate 21 29,
  joinGate 36 37, joinGate 38 43, joinGate 39 44,
  joinGate 40 45, joinGate 41 46, joinGate 42 47], 48⟩

lemma monotone : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness, List.forall_mem_cons, joinGate, meetGate]

end PEqualNP.Outside.L_meta_20151_aux

open PEqualNP.Outside.L_meta_20151_aux

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_20151 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6609709397838714315 : ℕ).testBit (8 * u.val + v.val)) 33) := by
  exact ⟨witness, monotone, by decide, by decide⟩
