import StringDiagrams.Super.Envelope

/-!
Parity coordinates for the two same-colour inversion matrices.

With the `EF` summand unshifted and the `FE` summand shifted by `p`, a dotted
cup of parity `j * p` needs source shift `(j + 1) * p`; a dotted cap needs
target shift `j * p`. These checks concern the existing Π-envelope, not the
construction of a factor action or the nondegeneracy conjecture.
-/

noncomputable section

open CategoryTheory StringDiagrams StringDiagrams.Supercategory

namespace NonVacuity.BlockInversionParity

variable {R C : Type*} [CommRing R] [Category C] [Preadditive C] [Linear R C]
  [Supercategory R C]

/-- The negative-weight cup columns are even with the extra target shift. -/
theorem cup_even {U Y : C} (p : ZMod 2) (j : ℕ) (u : U ⟶ Y)
    (hu : u ∈ parity (R := R) U Y ((j : ZMod 2) * p)) :
    Envelope.ofHom (X := (⟨((j : ZMod 2) + 1) * p, U⟩ : Envelope R C))
      (Y := ⟨p, Y⟩) u ∈ parity (R := R) _ _ 0 := by
  rw [Envelope.mem_parity_iff, Envelope.toHom_ofHom]
  simpa only [zero_add, add_mul, one_mul, add_assoc, zmod2_add_self, add_zero] using hu

/-- The positive-weight cap rows have the unmodified dot-count shift. -/
theorem cap_even {X U : C} (p : ZMod 2) (j : ℕ) (v : X ⟶ U)
    (hv : v ∈ parity (R := R) X U ((j : ZMod 2) * p)) :
    Envelope.ofHom (X := (⟨0, X⟩ : Envelope R C))
      (Y := ⟨(j : ZMod 2) * p, U⟩) v ∈ parity (R := R) _ _ 0 := by
  rw [Envelope.mem_parity_iff, Envelope.toHom_ofHom]
  simpa only [zero_add] using hv

/-- The crossing becomes even with the same target shift. -/
theorem crossing_even {X Y : C} (p : ZMod 2) (σ : X ⟶ Y)
    (hσ : σ ∈ parity (R := R) X Y p) :
    Envelope.ofHom (X := (⟨0, X⟩ : Envelope R C))
      (Y := ⟨p, Y⟩) σ ∈ parity (R := R) _ _ 0 := by
  rw [Envelope.mem_parity_iff, Envelope.toHom_ofHom]
  simpa only [zero_add] using hσ

/-- The old negative-weight source shift leaves the column at parity `p`. -/
example (p : ZMod 2) (j : ℕ) :
    (j : ZMod 2) * p + (j : ZMod 2) * p + p = p := by
  rw [zmod2_add_self, zero_add]

/-- The defect is nonzero for an odd colour, already at the undotted cup. -/
example : (0 + 0 + 1 : ZMod 2) ≠ 0 := by decide

omit [Supercategory R C] in
/-- Normalize the source slide by changing both the crossing and right dot. -/
theorem slide_normalized {X Y U : C} (q : R) (hq : q ^ 2 = 1)
    (x : X ⟶ X) (y : Y ⟶ Y) (σ : X ⟶ Y) (u : U ⟶ Y) (v : X ⟶ U)
    (h : σ ≫ y - q • (x ≫ σ) = v ≫ u) :
    x ≫ (-q • σ) + (-q • σ) ≫ (-q • y) = v ≫ u := by
  calc
    x ≫ (-q • σ) + (-q • σ) ≫ (-q • y) = -(q • (x ≫ σ)) + σ ≫ y := by
      rw [Linear.comp_smul, Linear.smul_comp, Linear.comp_smul, smul_smul, neg_mul_neg,
        ← pow_two, hq, one_smul, neg_smul]
    _ = v ≫ u := by simpa only [sub_eq_add_neg, add_comm] using h

#print axioms cup_even
#print axioms cap_even
#print axioms crossing_even
#print axioms slide_normalized

/-- The three parity-line contributions to the BB mate cancel. -/
theorem mate_line_parity : ∀ s p a v f b : ZMod 2,
    a + v + p = b + f → s * (v + f) + s * (a + b) + s * p = 0 := by
  decide

#print axioms mate_line_parity

end NonVacuity.BlockInversionParity
