import OddMath

/-! # Consumers of the spanning theorem for the quiver Hecke supercategory -/

noncomputable section
open OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples

/-- Mixed parities and three strands: the normal forms span every Hom space. -/
example :
    Submodule.span ℚ {f : (pres datum scalars).obj (ob datum [0, 1, 0]) ⟶
        (pres datum scalars).obj (ob datum [1, 0, 0]) |
      ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < [0, 1, 0].length) ∧
        ∃ w : Equiv.Perm (Fin [0, 1, 0].length),
          ∃ h, cl datum scalars [0, 1, 0] [1, 0, 0]
            (l.map PG.dot ++ cw (Categorification.TypeA.canWord [0, 1, 0].length w)) h = f} = ⊤ :=
  span_normalForms datum scalars [0, 1, 0] [1, 0, 0]

/-- A word with a dot above a crossing lies in the span of normal forms with one crossing. -/
example : Filt datum scalars [0, 1] [1, 0] 1 ≤ NF datum scalars [0, 1] [1, 0] 1 :=
  filt_le_nf datum scalars [0, 1] 1 [1, 0]

/-- The repeated crossing `ψ₀²` has, modulo (1.7), no crossings. -/
example (h : SChain [0, 1] (pl [0, 1] ([] ++ cw [0, 0] ++ [])) [0, 1]) :
    cl datum scalars [0, 1] [0, 1] _ h ∈ Filt datum scalars [0, 1] [0, 1] 0 :=
  cl_mem_filt_of_hasRepeat [] [] rfl (by intro x hx; simp at hx; simp [hx]) ⟨[], [], 0, rfl⟩ h

#print axioms OddMath.QuiverHecke.span_normalForms
#print axioms OddMath.QuiverHecke.filt_le_nf
