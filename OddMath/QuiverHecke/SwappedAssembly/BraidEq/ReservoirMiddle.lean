/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidEq.Algebra
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.PureBlock
import OddMath.QuiverHecke.SwappedAssembly.CrossEntries
import OddMath.QuiverHecke.SwappedAssembly.QuadNe

/-! # The braid relation at `Eᵢ Eⱼ Eᵢ` on the path `PRP`

For the relation (1.9) of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, at `Eᵢ Eⱼ Eᵢ` with `i ≠ j`, the path `PRP` (probe summands on the two
`i`-letters, reservoir summand on the `j`-letter) is the only path to its endpoint, and so are
the paths `RPP` of `Eⱼ Eᵢ Eᵢ` and `PPR` of `Eᵢ Eᵢ Eⱼ` through which the two sides pass.

Write `ψ` for the probe crossing of the two `i`-letters of `PPR`, `G = Eᵢ ◁ J : PPR ≅ PRP` and
`J : PRP ≅ RPP` for the mixed interchanges. Both mixed interchanges carry `ψ` to the probe
crossing of `RPP` (`preCrossSame_mixedJ_pair_ne`), so the left side is `G⁻¹ ψ G Q`, and the
right side is `G⁻¹ Q' ψ G`, where `Q` and `Q'` are the parameter polynomials `Q_ij` of the
two mixed entries. Transported to `PPR`, `Q = Q_ij(x₁, y)` and `Q' = Q_ij(x₂, y)` with `x₁`,
`x₂` the probe dots of the two `i`-letters and `y` the reservoir dot of the `j`-letter, and
`comp_qExpr_sub` gives the correction terms of (1.9); conjugation by `G` turns the dots
`ε x₂`, `ε y`, `ε x₁` into the dots of `PRP` on the third, second and first strand.

## Main results

* `ProbeReservoir.prp_braidEq_diag`: (1.9) on the diagonal entry at `PRP`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (ν : X) (i j : I) (t : Sector I)
  (hR : StepValid (true, j) false (nextSector (true, i) true t))

/-- The endpoint of the path `PRP` of `Eᵢ Eⱼ Eᵢ`. -/
abbrev prpEnd : Sector I :=
  nextSector (true, i) true (nextSector (true, j) false (nextSector (true, i) true t))

/-- The path `PRP` of `Eᵢ Eⱼ Eᵢ`. -/
def prpPath : SPath (wd D ν [up i, up j, up i]) t (prpEnd i j t) :=
  .cons _ true t trivial (.cons _ false _ hR (.cons _ true _ trivial (.nil _)))

/-- The path `RPP` of `Eⱼ Eᵢ Eᵢ`. -/
def rppPath : SPath (wd D ν [up j, up i, up i]) t (prpEnd i j t) :=
  .cons _ false t hR (.cons _ true _ trivial (.cons _ true _ trivial (.nil _)))

/-- The path `PPR` of `Eᵢ Eᵢ Eⱼ`. -/
def pprPath : SPath (wd D ν [up i, up i, up j]) t (prpEnd i j t) :=
  .cons _ true t trivial (.cons _ true _ trivial (.cons _ false _ hR (.nil _)))

variable {i j}

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- `RPP` is the only path of `Eⱼ Eᵢ Eᵢ` to the endpoint of `PRP`. -/
theorem eq_rppPath (hij : i ≠ j) (p : SPath (wd D ν [up j, up i, up i]) t (prpEnd i j t)) :
    p = rppPath (D := D) ν i j t hR := by
  suffices h : ∀ (t' : Sector I) (p : SPath (wd D ν [up j, up i, up i]) t t')
      (h : t' = prpEnd i j t), h ▸ p = rppPath ν i j t hR from h _ p rfl
  intro t' p h
  cases p with
  | cons _ σ₁ _ hv₁ p =>
    cases p with
    | cons _ σ₂ _ hv₂ p =>
      cases p with
      | cons _ σ₃ _ hv₃ p =>
        cases p
        have h₁ := congrArg (fun x : Sector I => x.1 i) h
        have h₂ := congrArg (fun x : Sector I => x.1 j) h
        cases σ₁ <;> cases σ₂ <;> cases σ₃ <;>
          first
            | rfl
            | (exfalso; simp [nextSector, Finsupp.single_apply, hij, Ne.symm hij] at h₁ h₂)

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- `PPR` is the only path of `Eᵢ Eᵢ Eⱼ` to the endpoint of `PRP`. -/
theorem eq_pprPath (hij : i ≠ j) (p : SPath (wd D ν [up i, up i, up j]) t (prpEnd i j t)) :
    p = pprPath (D := D) ν i j t hR := by
  suffices h : ∀ (t' : Sector I) (p : SPath (wd D ν [up i, up i, up j]) t t')
      (h : t' = prpEnd i j t), h ▸ p = pprPath ν i j t hR from h _ p rfl
  intro t' p h
  cases p with
  | cons _ σ₁ _ hv₁ p =>
    cases p with
    | cons _ σ₂ _ hv₂ p =>
      cases p with
      | cons _ σ₃ _ hv₃ p =>
        cases p
        have h₁ := congrArg (fun x : Sector I => x.1 i) h
        have h₂ := congrArg (fun x : Sector I => x.1 j) h
        cases σ₁ <;> cases σ₂ <;> cases σ₃ <;>
          first
            | rfl
            | (exfalso; simp [nextSector, Finsupp.single_apply, hij, Ne.symm hij] at h₁ h₂)

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
