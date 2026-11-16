/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.PointwiseLeftwardInverse
import OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedSectorEntries
import OddMath.QuiverHecke.SwappedAssembly.Sigma.FactorWindowInverse

/-! # The leftward entries as a cap-window inverse at a probe-only sector

Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 1.5, (1.13), toward
the positive-height bubble identities of §8 (research issue #345).

At a sector `t` with no reservoir summand of `Eᵢ` and no probe summand of `Fᵢ`
(for instance the vacuum sector `(0, 0)`), the path families of the augmented
map (1.13) have exactly one source path, one target path and one window path.
The five positive inverse identities `PosInverseAt` then say precisely that the
leftward entries `(-lc, dc)` are an entrywise inverse (`ProbeWindow.IsCapInverse`)
of the cap window `[σ; ε xⁿ]_(n < h)`. This file proves that statement in the path
chart, in the native factor chart, and after any additive evaluation in the
zero-padded corner chart. The inverse is the given leftward data itself; no
inverse is chosen.
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

namespace SPath

/-- Without a reservoir summand of `Eᵢ`, the only source path of `EᵢFᵢ` is the pure
probe path. -/
theorem eq_centralUpDn_true (i : I) (ν : X) (t : Sector I)
    (h : ¬StepValid (up i) false t) (p : SPath (wd D ν [up i, dn i]) t t) :
    p = centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩ := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := (centralUpDnEquiv i (SKM.wt D ν [dn i]) ν t).symm.surjective p
  cases a
  · exact absurd ha h
  · rfl

/-- Without a probe summand of `Fᵢ`, the only target path of `FᵢEᵢ` is the pure
reservoir path. -/
theorem eq_centralDnUp_false (i : I) (ν : X) (t : Sector I)
    (h : ¬StepValid (dn i) true t) (q : SPath (wd D ν [dn i, up i]) t t) :
    q = centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩ := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := (centralDnUpEquiv i (SKM.wt D ν [up i]) ν t).symm.surjective q
  cases a
  · rfl
  · exact absurd ha h

/-- The empty word has exactly one path. -/
theorem eq_nil_of_wd (ν : X) (t : Sector I) (r : SPath (wd D ν []) t t) : r = .nil t := by
  cases r
  rfl

end SPath

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)
local instance capInversePathFintype {w : List (Col I X)} {t s : Sector I} :
    Fintype (SPath w t s) :=
  Fintype.ofFinite _

/-- Cap-window inversion from the positive inverse identities, for arbitrary unique
source and target paths `p₀`, `q₀`. -/
theorem isCapInverse_of_posInverseAt_of_unique (c : P.CrossCoeff) (i : I) (ν : X)
    (t : Sector I) (Z : P.H t)
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (wd D ν []) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _r).obj Z ⟶ (P.pathFunctor p).obj Z)
    (H : P.PosInverseAt c i ν t t Z lc dc)
    (p₀ : SPath (wd D ν [up i, dn i]) t t) (q₀ : SPath (wd D ν [dn i, up i]) t t)
    (r₀ : SPath (wd D ν []) t t)
    (hp : ∀ p, p = p₀) (hq : ∀ q, q = q₀) (hr : ∀ r, r = r₀) :
    ProbeWindow.IsCapInverse (P.sigmaEntry c i i ν p₀ q₀ Z)
      (fun n : Fin (D.h i ν).toNat => P.epsEntry c i n ν p₀ r₀ Z)
      (-lc q₀ p₀) (fun n => dc n r₀ p₀) := by
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
  refine ⟨?_, fun n => ?_, fun m => ?_, fun n m => ?_, ?_⟩
  · have h := h₂ q₀ q₀
    rw [sp, famDelta_self] at h
    rw [Preadditive.neg_comp, h, neg_neg]
  · have h := h₄ n (Int.lt_toNat.mp n.2) r₀ q₀
    rwa [sp] at h
  · have h := h₃ m (Int.lt_toNat.mp m.2) q₀ r₀
    rw [sp] at h
    rw [Preadditive.neg_comp, h, neg_zero]
  · have h := h₅ m n (Int.lt_toNat.mp m.2) (Int.lt_toNat.mp n.2) r₀ r₀
    rw [sp, famDelta_self] at h
    rw [h]
    by_cases hnm : n = m
    · subst hnm; simp
    · have : (m : ℕ) ≠ n := fun e => hnm (Fin.ext e.symm)
      simp [hnm, this]
  · have h := h₁ p₀ p₀
    rw [sq, famDelta_self, Finset.sum_range (fun n => ∑ r, P.epsEntry c i n ν p₀ r Z ≫ dc n r p₀)]
      at h
    rw [Finset.sum_congr rfl (fun (n : Fin (D.h i ν).toNat) _ =>
      sr (fun r => P.epsEntry c i (n : ℕ) ν p₀ r Z ≫ dc (n : ℕ) r p₀))] at h
    rw [Preadditive.comp_neg, ← h]

/-- **The leftward entries invert the cap window in the path chart.** At a sector
without a reservoir summand of `Eᵢ` and without a probe summand of `Fᵢ`, the five
positive inverse identities say that `(-lc, dc)` is an entrywise inverse of the cap
window `[σ; ε xⁿ]_(n < h)` between the unique source, target and window paths. -/
theorem isCapInverse_of_posInverseAt (c : P.CrossCoeff) (i : I) (ν : X) (t : Sector I)
    (Z : P.H t)
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (wd D ν []) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _r).obj Z ⟶ (P.pathFunctor p).obj Z)
    (H : P.PosInverseAt c i ν t t Z lc dc)
    (hu : ¬StepValid (up i) false t) (hd : ¬StepValid (dn i) true t) :
    ProbeWindow.IsCapInverse
      (P.sigmaEntry c i i ν (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)
        (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩) Z)
      (fun n : Fin (D.h i ν).toNat => P.epsEntry c i n ν
        (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩) (.nil t) Z)
      (-lc (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
        (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩))
      (fun n => dc n (.nil t) (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)) :=
  P.isCapInverse_of_posInverseAt_of_unique c i ν t Z lc dc H _ _ (.nil t)
    (SPath.eq_centralUpDn_true i ν t hu) (SPath.eq_centralDnUp_false i ν t hd)
    (SPath.eq_nil_of_wd ν t)

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- **The leftward entries invert the native cap window.** In the native factor
charts, the cap-window inverse of `isCapInverse_of_posInverseAt` inverts the probe-to-
reservoir bend `centralFactorSigma` with its native dotted caps. -/
theorem isCapInverse_centralFactor_of_posInverseAt (c : P.CrossCoeff) (i : I) (ν : X)
    (t : Sector I) (Z : P.H t)
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (wd D ν []) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _r).obj Z ⟶ (P.pathFunctor p).obj Z)
    (H : P.PosInverseAt c i ν t t Z lc dc)
    (hu : ¬StepValid (up i) false t) (hd : ¬StepValid (dn i) true t) :
    ProbeWindow.IsCapInverse
      (P.centralFactorSigma c i t Z ⟨true, trivial⟩ ⟨false, trivial⟩)
      (fun n : Fin (D.h i ν).toNat => P.centralFactorCap i t Z n ⟨true, trivial⟩)
      ((P.centralTargetFactorIso i ν t Z ⟨false, trivial⟩).hom ≫
        (-lc (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
          (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)) ≫
        (P.centralSourceFactorIso i ν t Z ⟨true, trivial⟩).inv)
      (fun n => dc n (.nil t) (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩) ≫
        (P.centralSourceFactorIso i ν t Z ⟨true, trivial⟩).inv) := by
  have h := (P.isCapInverse_of_posInverseAt c i ν t Z lc dc H hu hd).coordinates
    (P.centralSourceFactorIso i ν t Z ⟨true, trivial⟩)
    (P.centralTargetFactorIso i ν t Z ⟨false, trivial⟩)
  rw [P.sigmaEntry_centralFactor c i ν t Z ⟨true, trivial⟩ ⟨false, trivial⟩] at h
  simp only [P.epsEntry_centralFactor c i ν t Z ⟨true, trivial⟩, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] at h
  exact h

/-- **The leftward entries invert the padded cap window after evaluation.** After
any additive evaluation `E`, the native cap-window inverse becomes an inverse of the
padded probe-to-reservoir bend `centralPaddedSigma true false` and the padded caps
`centralPaddedCap true n`. -/
theorem isCapInverse_centralPadded_of_posInverseAt (c : P.CrossCoeff) (i : I) (ν : X)
    (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C) [E.Additive]
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (wd D ν []) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _r).obj Z ⟶ (P.pathFunctor p).obj Z)
    (H : P.PosInverseAt c i ν t t Z lc dc)
    (hu : ¬StepValid (up i) false t) (hd : ¬StepValid (dn i) true t) :
    ProbeWindow.IsCapInverse
      (P.centralPaddedSigma c i t Z E true false)
      (fun n : Fin (D.h i ν).toNat => P.centralPaddedCap i t Z E true n)
      ((P.centralTargetCornerIso i t Z E ⟨false, trivial⟩).hom ≫
        E.map ((P.centralTargetFactorIso i ν t Z ⟨false, trivial⟩).hom ≫
          (-lc (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
            (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)) ≫
          (P.centralSourceFactorIso i ν t Z ⟨true, trivial⟩).inv) ≫
        (P.centralSourceCornerIso i t Z E ⟨true, trivial⟩).inv)
      (fun n => E.map (dc n (.nil t)
          (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩) ≫
          (P.centralSourceFactorIso i ν t Z ⟨true, trivial⟩).inv) ≫
        (P.centralSourceCornerIso i t Z E ⟨true, trivial⟩).inv) := by
  have h := ((P.isCapInverse_centralFactor_of_posInverseAt c i ν t Z lc dc H hu hd).map
    E).coordinates (P.centralSourceCornerIso i t Z E ⟨true, trivial⟩)
    (P.centralTargetCornerIso i t Z E ⟨false, trivial⟩)
  have hσ : P.centralPaddedSigma c i t Z E true false =
      (P.centralSourceCornerIso i t Z E ⟨true, trivial⟩).hom ≫
        E.map (P.centralFactorSigma c i t Z ⟨true, trivial⟩ ⟨false, trivial⟩) ≫
        (P.centralTargetCornerIso i t Z E ⟨false, trivial⟩).inv := by
    rw [centralPaddedSigma,
      dite_eq_left (show StepValid (up i) true t from trivial),
      dite_eq_left (show StepValid (dn i) false t from trivial)]
  have hcap : ∀ n : ℕ, P.centralPaddedCap i t Z E true n =
      (P.centralSourceCornerIso i t Z E ⟨true, trivial⟩).hom ≫
        E.map (P.centralFactorCap i t Z n ⟨true, trivial⟩) := by
    intro n
    rw [centralPaddedCap,
      dite_eq_left (show StepValid (up i) true t from trivial)]
  rw [hσ]
  simp only [hcap]
  exact h

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
