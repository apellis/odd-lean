import OddMath

/-! Non-vacuity checks in `NonVacuity.SkmHomComponents`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.SkmHomComponents

open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous} {ν μ : UGr D Sc sy hc}

/-- Application on actual SKM Hom, with the codomain expanded rather than assumed. -/
def componentOfShifted (A B : ν ⟶ μ) (n : ℤ) (a : ZMod 2)
    (f : shiftedUnderlying n a A ⟶ shiftedUnderlying 0 0 B) :
    (degree (R := k) A B n ⊓ parity (R := k) A B a : Submodule k (A ⟶ B)) :=
  shiftedHomEquiv A B n a f

theorem roundTrip (A B : ν ⟶ μ) (n : ℤ) (a : ZMod 2)
    (f : homComponent A B n a) :
    shiftedHomEquiv A B n a ((shiftedHomEquiv A B n a).symm f) = f := by simp

theorem linearity (A B : ν ⟶ μ) (n : ℤ) (a : ZMod 2) (r : k)
    (f g : shiftedUnderlying n a A ⟶ shiftedUnderlying 0 0 B) :
    shiftedHomEquiv A B n a (r • f + g) =
      r • shiftedHomEquiv A B n a f + shiftedHomEquiv A B n a g := by simp

theorem zeroShiftIdentity (A : ν ⟶ μ) :
    (shiftedHomEquiv A A 0 0 (𝟙 (shiftedUnderlying 0 0 A))).1 = 𝟙 A := by simp

/-- The upward strand in the actual presented SKM category. -/
def strand (μ : X) (i : I) :
    (⟨(wt D μ [up i] : X)⟩ : UGr D Sc sy hc) ⟶ ⟨μ⟩ where
  obj := ob D μ [up i]
  start_eq := rfl
  wf := ok_wd D μ [up i]
  endR_eq := endR_wd D μ [up i]

/-- The class of a single dot, not a postulated homogeneous morphism. -/
def dot (μ : X) (i : I) :
    strand (Sc := Sc) μ i ⟶ strand μ i :=
  (pres D Sc).lin (dg D μ (dotsL [] i [] 1) (sChain_dotsL [] i [] 1))

/-- Both homogeneity proofs are obtained from the defining one-dot diagram. -/
def dotComponent (μ : X) (i : I) :
    homComponent (sy := sy) (hc := hc) (strand (Sc := Sc) μ i)
      (strand μ i) (2 * sy.d i) (D.parity i) := by
  refine ⟨dot μ i, ?_, ?_⟩
  · apply Presentation.lin_mem_homDeg
    apply dg_mem_gdeg
    simp
  · apply Presentation.lin_mem_homDeg
    apply dg_mem
    simp

/-- This generator has strictly positive degree, so this is not a zero-shift test. -/
theorem dotShift_positive (i : I) : 0 < 2 * sy.d i := mul_pos (by decide) (sy.pos i)

/-- The actual dot determines an even degree-zero arrow out of the shifted strand. -/
def shiftedDot (μ : X) (i : I) :
    shiftedUnderlying (sy := sy) (hc := hc) (2 * sy.d i) (D.parity i)
        (strand (Sc := Sc) μ i) ⟶
      shiftedUnderlying 0 0 (strand μ i) :=
  (shiftedHomEquiv _ _ _ _).symm (dotComponent μ i)

theorem shiftedDot_recovers (μ : X) (i : I) :
    (shiftedHomEquiv _ _ _ _ (shiftedDot (Sc := Sc) (sy := sy) (hc := hc) μ i)).1 =
      dot μ i := by
  simp [shiftedDot, dotComponent]

end NonVacuity.SkmHomComponents
