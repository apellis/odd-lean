import OddMath.CoveringQuantum.PreF.Form

/-!
# The form on the radical quotient

The symmetric form on `'f` descends to `f = 'f / radical` and is nondegenerate there.
This is the radical-quotient definition of [CHW1] §1.4. It does not identify the radical
with the ideal of quantum Serre relations; that is a separate theorem.

The construction works for any symmetric bicharacter and normalization over a
commutative ring, without assuming that the normalization scalars are units.
-/

noncomputable section

namespace OddMath.CoveringQuantum.PreF

variable {k I : Type*} [CommRing k] [DecidableEq I] (χ : Bichar k I) (nm : I → k)

private theorem form_eq_of_rel {a b c d : PreF k I}
    (hab : (radical χ nm).ringCon a b) (hcd : (radical χ nm).ringCon c d) :
    form χ nm a c = form χ nm b d := by
  have hab' := (mem_radical_iff χ nm).mp (((radical χ nm).rel_iff a b).mp hab) c
  have hcd' := (mem_radical_iff' χ nm).mp (((radical χ nm).rel_iff c d).mp hcd) b
  simp only [map_sub, LinearMap.sub_apply, sub_eq_zero] at hab' hcd'
  exact hab'.trans hcd'

private def quotientPair (x y : Quotient χ nm) : k :=
  _root_.Quotient.liftOn₂ x y (fun a b ↦ form χ nm a b) fun _ _ _ _ h h' ↦ form_eq_of_rel χ nm h h'

@[simp] private theorem quotientPair_mk (x y : PreF k I) :
    quotientPair χ nm (toQuotient χ nm x) (toQuotient χ nm y) = form χ nm x y := rfl

/-- The symmetric form descended to the radical quotient. -/
def quotientForm : LinearMap.BilinForm k (Quotient χ nm) :=
  LinearMap.mk₂ k (quotientPair χ nm)
    (by
      intro x y z
      obtain ⟨a, rfl⟩ := toQuotient_surjective χ nm x
      obtain ⟨b, rfl⟩ := toQuotient_surjective χ nm y
      obtain ⟨c, rfl⟩ := toQuotient_surjective χ nm z
      rw [← map_add, quotientPair_mk, quotientPair_mk, quotientPair_mk]; simp)
    (by
      intro c x y
      obtain ⟨a, rfl⟩ := toQuotient_surjective χ nm x
      obtain ⟨b, rfl⟩ := toQuotient_surjective χ nm y
      rw [← map_smul, quotientPair_mk, quotientPair_mk]; simp)
    (by
      intro x y z
      obtain ⟨a, rfl⟩ := toQuotient_surjective χ nm x
      obtain ⟨b, rfl⟩ := toQuotient_surjective χ nm y
      obtain ⟨c, rfl⟩ := toQuotient_surjective χ nm z
      rw [← map_add, quotientPair_mk, quotientPair_mk, quotientPair_mk]; simp)
    (by
      intro c x y
      obtain ⟨a, rfl⟩ := toQuotient_surjective χ nm x
      obtain ⟨b, rfl⟩ := toQuotient_surjective χ nm y
      rw [← map_smul, quotientPair_mk, quotientPair_mk]; simp)

@[simp] theorem quotientForm_mk (x y : PreF k I) :
    quotientForm χ nm (toQuotient χ nm x) (toQuotient χ nm y) = form χ nm x y := rfl

/-- Symmetry survives passage to the quotient. -/
theorem quotientForm_comm (x y : Quotient χ nm) : quotientForm χ nm x y = quotientForm χ nm y x := by
  obtain ⟨a, rfl⟩ := toQuotient_surjective χ nm x
  obtain ⟨b, rfl⟩ := toQuotient_surjective χ nm y
  exact form_comm χ nm a b

/-- The quotient form has zero left radical. This follows from quotienting by precisely the radical. -/
theorem quotientForm_separatingLeft :
    ∀ x : Quotient χ nm, (∀ y, quotientForm χ nm x y = 0) → x = 0 := by
  intro x hx
  obtain ⟨a, rfl⟩ := toQuotient_surjective χ nm x
  apply (toQuotient_eq_zero_iff χ nm).mpr
  apply (mem_radical_iff χ nm).mpr
  intro b
  exact hx (toQuotient χ nm b)

/-- The quotient form has zero right radical. -/
theorem quotientForm_separatingRight :
    ∀ y : Quotient χ nm, (∀ x, quotientForm χ nm x y = 0) → y = 0 := by
  intro y hy
  exact quotientForm_separatingLeft χ nm y fun x ↦ by rw [quotientForm_comm]; exact hy x

/-- Nondegeneracy on the radical quotient, without any hypothesis on the Serre presentation. -/
theorem quotientForm_nondegenerate : (quotientForm χ nm).Nondegenerate :=
  ⟨quotientForm_separatingLeft χ nm, quotientForm_separatingRight χ nm⟩

/-- Descending the free form determines the quotient form uniquely. -/
theorem quotientForm_unique (B : LinearMap.BilinForm k (Quotient χ nm))
    (hB : ∀ x y, B (toQuotient χ nm x) (toQuotient χ nm y) = form χ nm x y) : B = quotientForm χ nm := by
  ext x y
  obtain ⟨a, rfl⟩ := toQuotient_surjective χ nm x
  obtain ⟨b, rfl⟩ := toQuotient_surjective χ nm y
  exact hB a b

end OddMath.CoveringQuantum.PreF
