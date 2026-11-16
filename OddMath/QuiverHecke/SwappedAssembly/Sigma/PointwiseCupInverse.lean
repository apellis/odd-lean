/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseCapInverse

/-! # The rightward entries as a cup-window inverse at a probe-only sector

Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 1.5, (1.14), toward
the nonpositive-height bubble identities of §8 (research issue #345).

This is the negative-height counterpart of `Sigma.PointwiseCapInverse`. At a sector
`t` with no reservoir summand of `Eᵢ` and no probe summand of `Fᵢ` (for instance the
vacuum sector `(0, 0)`), the path families of the augmented map (1.14) have exactly
one source path, one target path and one window path. The five negative inverse
identities `NegInverseAt` then say precisely that the entries `(-lc, dc)` are an
entrywise inverse (`ProbeWindow.IsCupInverse`) of the cup window
`[σ, xⁿ η]_(n < -h)`. This file proves that statement in the path chart, in the
native factor chart, and after any additive evaluation in the zero-padded corner
chart. The inverse is the given data itself; no inverse is chosen.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM Classical

universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)
local instance cupInversePathFintype {w : List (Col I X)} {t s : Sector I} :
    Fintype (SPath w t s) :=
  Fintype.ofFinite _

/-- Cup-window inversion from the negative inverse identities, for arbitrary unique
source and target paths `p₀`, `q₀`. -/
theorem isCupInverse_of_negInverseAt_of_unique (c : P.CrossCoeff) (i : I) (ν : X)
    (t : Sector I) (Z : P.H t)
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (r : SPath (wd D ν []) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor r).obj Z)
    (H : P.NegInverseAt c i ν t t Z lc dc)
    (p₀ : SPath (wd D ν [up i, dn i]) t t) (q₀ : SPath (wd D ν [dn i, up i]) t t)
    (r₀ : SPath (wd D ν []) t t)
    (hp : ∀ p, p = p₀) (hq : ∀ q, q = q₀) (hr : ∀ r, r = r₀) :
    ProbeWindow.IsCupInverse (P.sigmaEntry c i i ν p₀ q₀ Z)
      (fun n : Fin (-D.h i ν).toNat => P.etaEntry c i n ν r₀ q₀ Z)
      (-lc q₀ p₀) (fun n => dc n q₀ r₀) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := H
  have sp : ∀ {M : Type _} [AddCommMonoid M]
      (f : SPath (wd D ν [up i, dn i]) t t → M), ∑ p, f p = f p₀ := fun f =>
    Finset.sum_eq_single p₀ (fun b _ hb => absurd (hp b) hb)
      (fun h => absurd (Finset.mem_univ _) h)
  have sq : ∀ {M : Type _} [AddCommMonoid M]
      (f : SPath (wd D ν [dn i, up i]) t t → M), ∑ q, f q = f q₀ := fun f =>
    Finset.sum_eq_single q₀ (fun b _ hb => absurd (hq b) hb)
      (fun h => absurd (Finset.mem_univ _) h)
  have sr : ∀ {M : Type _} [AddCommMonoid M]
      (f : SPath (wd D ν []) t t → M), ∑ r, f r = f r₀ := fun f =>
    Finset.sum_eq_single r₀ (fun b _ hb => absurd (hr b) hb)
      (fun h => absurd (Finset.mem_univ _) h)
  refine ⟨?_, fun n => ?_, fun m => ?_, fun m n => ?_, ?_⟩
  · have h := h₂ p₀ p₀
    rw [sq, famDelta_self] at h
    rw [Preadditive.comp_neg, h, neg_neg]
  · have h := h₄ n (Int.lt_toNat.mp n.2) p₀ r₀
    rwa [sq] at h
  · have h := h₃ m (Int.lt_toNat.mp m.2) r₀ p₀
    rw [sq] at h
    rw [Preadditive.comp_neg, h, neg_zero]
  · have h := h₅ m n (Int.lt_toNat.mp m.2) (Int.lt_toNat.mp n.2) r₀ r₀
    rw [sq, famDelta_self] at h
    rw [h]
    by_cases hmn : m = n
    · subst hmn; simp
    · have : (m : ℕ) ≠ n := fun e => hmn (Fin.ext e)
      simp [hmn, this]
  · have h := h₁ q₀ q₀
    rw [sp, famDelta_self,
      Finset.sum_range (fun n => ∑ r, dc n q₀ r ≫ P.etaEntry c i n ν r q₀ Z)] at h
    rw [Finset.sum_congr rfl (fun (n : Fin (-D.h i ν).toNat) _ =>
      sr (fun r => dc (n : ℕ) q₀ r ≫ P.etaEntry c i (n : ℕ) ν r q₀ Z))] at h
    rw [Preadditive.neg_comp, ← h]

/-- **The rightward entries invert the cup window in the path chart.** At a sector
without a reservoir summand of `Eᵢ` and without a probe summand of `Fᵢ`, the five
negative inverse identities say that `(-lc, dc)` is an entrywise inverse of the cup
window `[σ, xⁿ η]_(n < -h)` between the unique source, target and window paths. -/
theorem isCupInverse_of_negInverseAt (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t)
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (r : SPath (wd D ν []) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor r).obj Z)
    (H : P.NegInverseAt c i ν t t Z lc dc)
    (hu : ¬StepValid (up i) false t) (hd : ¬StepValid (dn i) true t) :
    ProbeWindow.IsCupInverse
      (P.sigmaEntry c i i ν (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)
        (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩) Z)
      (fun n : Fin (-D.h i ν).toNat => P.etaEntry c i n ν (.nil t)
        (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩) Z)
      (-lc (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
        (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩))
      (fun n => dc n (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩) (.nil t)) :=
  P.isCupInverse_of_negInverseAt_of_unique c i ν t Z lc dc H _ _ (.nil t)
    (SPath.eq_centralUpDn_true i ν t hu) (SPath.eq_centralDnUp_false i ν t hd)
    (SPath.eq_nil_of_wd ν t)

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- **The rightward entries invert the native cup window.** In the native factor
charts, the cup-window inverse of `isCupInverse_of_negInverseAt` inverts the probe-to-
reservoir bend `centralFactorSigma` with its native dotted cups. -/
theorem isCupInverse_centralFactor_of_negInverseAt (c : P.CrossCoeff) (i : I) (ν : X)
    (t : Sector I) (Z : P.H t)
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (r : SPath (wd D ν []) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor r).obj Z)
    (H : P.NegInverseAt c i ν t t Z lc dc)
    (hu : ¬StepValid (up i) false t) (hd : ¬StepValid (dn i) true t) :
    ProbeWindow.IsCupInverse
      (P.centralFactorSigma c i t Z ⟨true, trivial⟩ ⟨false, trivial⟩)
      (fun n : Fin (-D.h i ν).toNat => P.centralFactorUnit i t Z n ⟨false, trivial⟩)
      ((P.centralTargetFactorIso i ν t Z ⟨false, trivial⟩).hom ≫
        (-lc (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
          (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)) ≫
        (P.centralSourceFactorIso i ν t Z ⟨true, trivial⟩).inv)
      (fun n => (P.centralTargetFactorIso i ν t Z ⟨false, trivial⟩).hom ≫
        dc n (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩) (.nil t)) := by
  have h := (P.isCupInverse_of_negInverseAt c i ν t Z lc dc H hu hd).coordinates
    (P.centralSourceFactorIso i ν t Z ⟨true, trivial⟩)
    (P.centralTargetFactorIso i ν t Z ⟨false, trivial⟩)
  rw [P.sigmaEntry_centralFactor c i ν t Z ⟨true, trivial⟩ ⟨false, trivial⟩] at h
  simp only [P.etaEntry_centralFactor c i ν t Z ⟨false, trivial⟩, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] at h
  exact h

/-- **The rightward entries invert the padded cup window after evaluation.** After
any additive evaluation `E`, the native cup-window inverse becomes an inverse of the
padded probe-to-reservoir bend `centralPaddedSigma true false` and the padded units
`centralPaddedUnit false n`. -/
theorem isCupInverse_centralPadded_of_negInverseAt (c : P.CrossCoeff) (i : I) (ν : X)
    (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C) [E.Additive]
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (r : SPath (wd D ν []) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor r).obj Z)
    (H : P.NegInverseAt c i ν t t Z lc dc)
    (hu : ¬StepValid (up i) false t) (hd : ¬StepValid (dn i) true t) :
    ProbeWindow.IsCupInverse
      (P.centralPaddedSigma c i t Z E true false)
      (fun n : Fin (-D.h i ν).toNat => P.centralPaddedUnit i t Z E false n)
      ((P.centralTargetCornerIso i t Z E ⟨false, trivial⟩).hom ≫
        E.map ((P.centralTargetFactorIso i ν t Z ⟨false, trivial⟩).hom ≫
          (-lc (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
            (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)) ≫
          (P.centralSourceFactorIso i ν t Z ⟨true, trivial⟩).inv) ≫
        (P.centralSourceCornerIso i t Z E ⟨true, trivial⟩).inv)
      (fun n => (P.centralTargetCornerIso i t Z E ⟨false, trivial⟩).hom ≫
        E.map ((P.centralTargetFactorIso i ν t Z ⟨false, trivial⟩).hom ≫
          dc n (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩) (.nil t))) := by
  have h := ((P.isCupInverse_centralFactor_of_negInverseAt c i ν t Z lc dc H hu hd).map
    E).coordinates (P.centralSourceCornerIso i t Z E ⟨true, trivial⟩)
    (P.centralTargetCornerIso i t Z E ⟨false, trivial⟩)
  have hσ : P.centralPaddedSigma c i t Z E true false =
      (P.centralSourceCornerIso i t Z E ⟨true, trivial⟩).hom ≫
        E.map (P.centralFactorSigma c i t Z ⟨true, trivial⟩ ⟨false, trivial⟩) ≫
        (P.centralTargetCornerIso i t Z E ⟨false, trivial⟩).inv := by
    rw [centralPaddedSigma,
      dite_eq_left (show StepValid (up i) true t from trivial),
      dite_eq_left (show StepValid (dn i) false t from trivial)]
  have hunit : ∀ n : ℕ, P.centralPaddedUnit i t Z E false n =
      E.map (P.centralFactorUnit i t Z n ⟨false, trivial⟩) ≫
        (P.centralTargetCornerIso i t Z E ⟨false, trivial⟩).inv := by
    intro n
    rw [centralPaddedUnit,
      dite_eq_left (show StepValid (dn i) false t from trivial)]
  rw [hσ]
  simp only [hunit]
  exact h

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
