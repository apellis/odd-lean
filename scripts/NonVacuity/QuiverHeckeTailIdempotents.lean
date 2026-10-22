import OddMath

/-! # Idempotents of `Z ⊗ P(i^{(ε)})` modulo maps through longer tails (input to BE2 Theorem 11.3)

On the datum of `OddMath.QuiverHecke.AlgebraExamples` over `ℚ`, with `s = []`, `z = 1`, `ε = 1`
and `b = 1`: the hypotheses of `tail_idempotent_mem_tailJ` on `z` (its corner is local) and on
`b` (`b c b ∈ ℚ b` in degrees `≤ 0`) are proved from `corner_mem_span_one`.
-/

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples

/-- Degree `≤ 0` maps of a word of length `≤ 1` are scalars. -/
theorem nv_scalar {r : ℕ} (hr : r ≤ 1) {n : ℤ} {p : ZMod 2} (hn : n ≤ 0)
    {c : HEnd datum scalars symmetrizer homogeneous (List.replicate r 0)}
    (hc : c ∈ homPiece datum scalars symmetrizer homogeneous (List.replicate r 0)
      (List.replicate r 0) n p) :
    c ∈ ℚ ∙ 𝟙 _ :=
  corner_mem_span_one datum scalars symmetrizer 0 r homogeneous hr hn hc.1

/-- The local hypothesis for `z = 1` on the empty word. -/
theorem nv_local (a : HEnd datum scalars symmetrizer homogeneous [])
    (ha : a ∈ homPiece datum scalars symmetrizer homogeneous [] [] 0 0) (_ : 𝟙 _ ≫ a ≫ 𝟙 _ = a) :
    IsNilpotent (id a : End (hObj datum scalars symmetrizer homogeneous [])) ∨
      ∃ a' : HEnd datum scalars symmetrizer homogeneous [],
        a' ∈ homPiece datum scalars symmetrizer homogeneous [] [] 0 0 ∧ a ≫ a' = 𝟙 _ ∧
          a' ≫ a = 𝟙 _ := by
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.1 (nv_scalar (r := 0) (by omega) le_rfl ha)
  by_cases hμ : μ = 0
  · left; subst hμ; rw [zero_smul]; exact IsNilpotent.zero
  · right
    have h1 : 𝟙 (hObj datum scalars symmetrizer homogeneous []) ∈
        homPiece datum scalars symmetrizer homogeneous [] [] 0 0 :=
      ⟨GradedSupercategory.id_mem_degree _, Supercategory.id_mem _⟩
    refine ⟨μ⁻¹ • 𝟙 _, Submodule.smul_mem _ _ h1, ?_, ?_⟩
    · simp [Linear.comp_smul, smul_smul, hμ]
    · simp [smul_smul, hμ]

example :
    (0 : HEnd datum scalars symmetrizer homogeneous ([] ++ List.replicate 1 0)) ∈
        tailJ datum scalars symmetrizer homogeneous [] 0 1 ∨
      (0 : HEnd datum scalars symmetrizer homogeneous ([] ++ List.replicate 1 0)) ∈
        tailJ datum scalars symmetrizer homogeneous [] 0 1 :=
  tail_idempotent_mem_tailJ (Category.id_comp _)
    ⟨GradedSupercategory.id_mem_degree _, Supercategory.id_mem _⟩
    (fun hc hn => by simpa using nv_scalar (r := 1) le_rfl hn hc)
    ⟨GradedSupercategory.id_mem_degree _, Supercategory.id_mem _⟩ (Category.id_comp _)
    nv_local (zero_mem _) (zero_mem _) (by simp) (by simp) (by simp) (by simp) (by simp)

#print axioms OddMath.QuiverHecke.tail_idempotent_mem_tailJ
