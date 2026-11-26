import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18534

open PEqualNP.CircuitLowerBounds

def cycleCircuit : Circuit :=
  ⟨[⟨.or, [0, 5]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.and, [10, 15]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.and, [12, 17]⟩,
    ⟨.and, [13, 14]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.or, [20, 19]⟩], 21⟩

end PEqualNP.Outside.L_meta_18534

theorem PEqualNP.Outside.L_meta_18534 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide (v.val = (u.val + 1) % 5 ∨ u.val = (v.val + 1) % 5)) 12 := by
  let C := PEqualNP.Outside.L_meta_18534.cycleCircuit
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C,PEqualNP.Outside.L_meta_18534.cycleCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · decide +kernel
