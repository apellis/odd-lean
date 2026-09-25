import OddMath.Diagrams.OddNilHecke.Relations
import StringDiagrams.Derivation
import StringDiagrams.Grading
import Mathlib.Data.ZMod.Basic

/-!
# The local differential on the diagrammatic odd nilHecke category

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*,
arXiv:1504.01712v2, §3.2, Proposition 3.3, with the conventions of §2.2 ((2.1)–(2.4)) and
§2.3.

Ellis–Qi equip the odd nilHecke algebra `ONH_n` with the differential determined by

  `d(x_i) = x_i²`,    `d(∂_i) = 1`,

extended by the super Leibniz rule (2.3) `d(ab) = d(a) b + (-1)^{p(a)} a d(b)`. The first
value is the local differential on skew polynomials (§3.1, Example 2.13); the second is the
value of `d` on a crossing forced in Proposition 3.3 (the identity of two strands).

This file builds that differential intrinsically on the presented diagrammatic category
`ONH R` of `OddMath.Diagrams.OddNilHecke.Basic`, over any commutative ring `R`, as the
differential induced by a local derivation (`StringDiagrams.LocalDerivation`):

* `ansatz R a b c`: the local derivation with `δ(dot) = dot ≫ dot` and
  `δ(crossing) = a·1 + b·(x₀ ∂) + c·(x₁ ∂)`, the ansatz (3.7) of Ellis–Qi (at `n = 2`)
  (in `End`, `x₀ ∂` is the crossing followed by a dot on the left strand at the top, and
  `x₁ ∂` the same with the dot on the right strand);
* `D R = ansatz R 1 0 0`, the local derivation `δ(dot) = x²`, `δ(crossing) = 1`
  (`D_δ_dot`, `D_δ_cross`);
* `compatible R`: `D R` is compatible with the presentation `pres R`: every defining relation
  (square, braid and the two mixed relations) is homogeneous and its derivative vanishes in the
  presented category. The super interchange law needs no check (the library's descent
  theorem handles it).
* `deriv R`, `d R n`: the induced differential on every Hom-space, and on `End (strands n)`,
  with `deriv_dot`, `deriv_cross` (values on the generators), `d_x` (`d(x_i) = x_i²`), `d_ψ`
  (`d(ψ_i) = 1`), the super Leibniz rule `d_mul` (Ellis–Qi (2.3)), `d_x_mul`, `d_ψ_mul`,
  `deriv_deriv` and `d_d` (`d² = 0`), for every width `n`;
* the parity grading `parityDeg` (every generator odd): `isHomogeneous_parity`,
  `deriv_mem_homDeg` (`d` is odd), `x_mem_endDeg`, `ψ_mem_endDeg`, and `d_mul_of_mem` (the
  Leibniz rule for homogeneous left factors of parity `k : ZMod 2`).

The obstruction formulas for the general ansatz (`lin_derivFree_square`,
`lin_derivFree_mixedRight`, `lin_derivFree_mixedLeft`) are recorded here over any `R`; the
resulting characterization over `ℤ` is in `OddMath.Diagrams.OddNilHecke.DifferentialAnsatz`.

## Conventions

Products in `End` are composition of operators, `f * g = g ≫ f` (`f` drawn above `g`); this is
the convention of Ellis–Qi §2.3, where `xy` places `x` above `y`. The derivation of the
free 2-category is `StringDiagrams.LocalDerivation.derivFree`, whose Leibniz rule
`d(f ≫ g) = (-1)^{|g|} d f ≫ g + f ≫ d g` is Ellis–Qi (2.3) in this convention
(`StringDiagrams.Presentation.deriv_mul`). Strands are numbered from `0`: `x R n i` and
`ψ R n i` are Ellis–Qi's `x_{i+1}` and `∂_{i+1}`.
-/

noncomputable section

namespace OddMath.Diagrams.OddNilHecke

open CategoryTheory StringDiagrams Diagram

variable (R : Type*) [CommRing R]

/-! ## The local derivations -/

/-- The crossing followed by a dot at the top of the left strand: `x₀ ∂` in `End (strands 2)`. -/
abbrev dotCrossLeft : strands 2 ⟶ strands 2 :=
  dlay (n := 2) (i := 0) (g := .cross) (by decide) ≫ dlay (n := 2) (i := 0) (g := .dot) (by decide)

/-- The crossing followed by a dot at the top of the right strand: `x₁ ∂` in
`End (strands 2)`. -/
abbrev dotCrossRight : strands 2 ⟶ strands 2 :=
  dlay (n := 2) (i := 0) (g := .cross) (by decide) ≫ dlay (n := 2) (i := 1) (g := .dot) (by decide)

/-- The values of the ansatz on the generators: `δ(dot) = dot ≫ dot` and
`δ(crossing) = a·1 + b·(x₀ ∂) + c·(x₁ ∂)`. -/
def ansatzδ (a b c : R) : (g : sig.Gen) → LinDiagram R (sig.genDom g) (sig.genCod g)
  | .dot => LinDiagram.of (ofGen (S := sig) Gen.dot ≫ ofGen (S := sig) Gen.dot)
  | .cross =>
      a • LinDiagram.of (𝟙 (strands 2)) + b • LinDiagram.of dotCrossLeft +
        c • LinDiagram.of dotCrossRight

theorem oddCount_dlay {n i : ℕ} {g : Gen} (h : i + g.arity ≤ n) : oddCount (dlay h) = 1 := rfl

theorem hasParity_ansatzδ (a b c : R) (g : sig.Gen) :
    (ansatzδ R a b c g).HasParity ((sig.odd g).toNat + 1) := by
  cases g with
  | dot =>
    apply LinDiagram.hasParity_of
    rw [oddCount_comp, oddCount_ofGen]; rfl
  | cross =>
    have h0 : oddCount (𝟙 (strands 2)) % 2 = ((sig.odd Gen.cross).toNat + 1) % 2 := rfl
    have hl : oddCount dotCrossLeft % 2 = ((sig.odd Gen.cross).toNat + 1) % 2 := by
      rw [oddCount_comp, oddCount_dlay, oddCount_dlay]; rfl
    have hr : oddCount dotCrossRight % 2 = ((sig.odd Gen.cross).toNat + 1) % 2 := by
      rw [oddCount_comp, oddCount_dlay, oddCount_dlay]; rfl
    exact (((LinDiagram.hasParity_of h0).smul a).add ((LinDiagram.hasParity_of hl).smul b)).add
      ((LinDiagram.hasParity_of hr).smul c)

/-- The local ansatz of Ellis–Qi (3.7) (at `n = 2`): `δ(dot) = x²` and
`δ(crossing) = a + b x₀ ∂ + c x₁ ∂`. Both values are even, as required of an odd derivation
on odd generators. -/
def ansatz (a b c : R) : LocalDerivation sig R where
  δ := ansatzδ R a b c
  hasParity := hasParity_ansatzδ R a b c

/-- The local derivation of Ellis–Qi Proposition 3.3: `δ(dot) = x²`, `δ(crossing) = 1`. -/
def D : LocalDerivation sig R := ansatz R 1 0 0

theorem D_δ_dot : (D R).δ .dot = LinDiagram.of (ofGen (S := sig) Gen.dot ≫ ofGen (S := sig) Gen.dot) :=
  rfl

theorem D_δ_cross : (D R).δ .cross = LinDiagram.of (𝟙 (sig.genDom Gen.cross)) := by
  show (1 : R) • _ + (0 : R) • _ + (0 : R) • _ = _
  rw [one_smul, zero_smul, zero_smul, add_zero, add_zero]
  rfl

/-! ## Values on layers -/

section Layers

variable {R} (a b c : R)

/-- The derivative of a dot layer is the double dot: `d(x_i) = x_i²`. -/
theorem lin_derivDiag_dot {n i : ℕ} (h : i + Gen.arity .dot ≤ n) :
    (pres R).lin ((ansatz R a b c).derivDiag (dlay (g := .dot) h)) = x R n i * x R n i := by
  rw [dlay, LocalDerivation.derivDiag_layer_of _ _ _ _ _
      (ofGen (S := sig) Gen.dot ≫ ofGen (S := sig) Gen.dot) rfl, Presentation.lin_of,
    x_def R (show i < n by simpa [Gen.arity] using h), End.mul_def, ← Presentation.diag_comp]
  apply Presentation.diag_eq_of_layers_eq
  simp [lay, Layer.whisker, Signature.genLayer]

/-- The derivative of a crossing layer: `d(ψ_i) = a + b x_i ψ_i + c x_{i+1} ψ_i`. -/
theorem lin_derivDiag_cross {n i : ℕ} (h : i + Gen.arity .cross ≤ n) :
    (pres R).lin ((ansatz R a b c).derivDiag (dlay (g := .cross) h)) =
      a • (1 : End ((pres R).obj (strands n))) + b • (x R n i * ψ R n i) +
        c • (x R n (i + 1) * ψ R n i) := by
  have hψ : i + 1 < n := by simp [Gen.arity] at h; omega
  rw [dlay, LocalDerivation.derivDiag_layer, LocalDerivation.layerDeriv]
  show (pres R).lin (LinDiagram.cast (LinDiagram.whisker (a • LinDiagram.of (𝟙 (strands 2)) +
      b • LinDiagram.of dotCrossLeft + c • LinDiagram.of dotCrossRight) _ _ _) _ _) = _
  rw [LinDiagram.whisker_add, LinDiagram.whisker_add, LinDiagram.whisker_smul,
    LinDiagram.whisker_smul, LinDiagram.whisker_smul, LinDiagram.whisker_of,
    LinDiagram.whisker_of, LinDiagram.whisker_of, LinDiagram.cast_add, LinDiagram.cast_add,
    LinDiagram.cast_smul, LinDiagram.cast_smul, LinDiagram.cast_smul, LinDiagram.cast_of,
    LinDiagram.cast_of, LinDiagram.cast_of, Presentation.lin_add, Presentation.lin_add,
    Presentation.lin_smul, Presentation.lin_smul, Presentation.lin_smul, Presentation.lin_of,
    Presentation.lin_of, Presentation.lin_of, x_def R (show i < n by omega), x_def R hψ,
    ψ_def R hψ, End.mul_def, End.mul_def, ← Presentation.diag_comp, ← Presentation.diag_comp,
    End.one_def, ← Presentation.diag_id]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;> refine congrArg _ ?_ <;>
    apply Presentation.diag_eq_of_layers_eq <;>
    simp [lay, Layer.whisker, Signature.genLayer, Gen.arity] <;> first | rfl | omega

end Layers

/-! ## Consequences of the relations -/

section Consequences

variable {n i : ℕ}

theorem ψ_mul_x_mul_ψ (h : i + 1 < n) : ψ R n i * x R n i * ψ R n i = ψ R n i := by
  have hl := ψ_mul_x_add_x_mul_ψ R h
  rw [← eq_sub_iff_add_eq] at hl
  rw [hl, sub_mul, one_mul, mul_assoc, ψ_mul_ψ, mul_zero, sub_zero]

theorem ψ_mul_x_succ_mul_ψ (h : i + 1 < n) : ψ R n i * x R n (i + 1) * ψ R n i = ψ R n i := by
  have hr := x_mul_ψ_add_ψ_mul_x R h
  rw [← eq_sub_iff_add_eq'] at hr
  rw [hr, sub_mul, one_mul, mul_assoc, ψ_mul_ψ, mul_zero, sub_zero]

/-- `x_i² ψ_i - ψ_i x_{i+1}² = x_i - x_{i+1}`. -/
theorem x_mul_x_mul_ψ_sub (h : i + 1 < n) :
    x R n i * (x R n i * ψ R n i) - ψ R n i * (x R n (i + 1) * x R n (i + 1)) =
      x R n i - x R n (i + 1) := by
  have hr := x_mul_ψ_add_ψ_mul_x R h
  have e : x R n i * ψ R n i = 1 - ψ R n i * x R n (i + 1) := eq_sub_of_add_eq hr
  rw [e, mul_sub, mul_one, ← mul_assoc, e]
  noncomm_ring

/-- `x_{i+1}² ψ_i - ψ_i x_i² = x_{i+1} - x_i`. -/
theorem x_succ_mul_x_succ_mul_ψ_sub (h : i + 1 < n) :
    x R n (i + 1) * (x R n (i + 1) * ψ R n i) - ψ R n i * (x R n i * x R n i) =
      x R n (i + 1) - x R n i := by
  have hl := ψ_mul_x_add_x_mul_ψ R h
  have e : x R n (i + 1) * ψ R n i = 1 - ψ R n i * x R n i := eq_sub_of_add_eq' hl
  rw [e, mul_sub, mul_one, ← mul_assoc, e]
  noncomm_ring

theorem x_mul_ψ_mul_x_succ (h : i + 1 < n) :
    x R n i * (ψ R n i * x R n (i + 1)) = x R n i - x R n i * (x R n i * ψ R n i) := by
  have hr := x_mul_ψ_add_ψ_mul_x R h
  rw [eq_sub_of_add_eq' hr, mul_sub, mul_one]

theorem x_succ_mul_ψ_mul_x_succ (h : i + 1 < n) :
    x R n (i + 1) * (ψ R n i * x R n (i + 1)) =
      x R n (i + 1) + x R n i * (x R n (i + 1) * ψ R n i) := by
  have hr := x_mul_ψ_add_ψ_mul_x R h
  have hxy := x_mul_x_add_x_mul_x R (n := n) (i := i) (j := i + 1) (by omega)
  rw [eq_sub_of_add_eq' hr, mul_sub, mul_one, ← mul_assoc, ← mul_assoc,
    eq_neg_of_add_eq_zero_right hxy]
  noncomm_ring

theorem x_succ_mul_ψ_mul_x (h : i + 1 < n) :
    x R n (i + 1) * (ψ R n i * x R n i) =
      x R n (i + 1) - x R n (i + 1) * (x R n (i + 1) * ψ R n i) := by
  have hl := ψ_mul_x_add_x_mul_ψ R h
  rw [eq_sub_of_add_eq hl, mul_sub, mul_one]

theorem x_mul_ψ_mul_x (h : i + 1 < n) :
    x R n i * (ψ R n i * x R n i) = x R n i + x R n (i + 1) * (x R n i * ψ R n i) := by
  have hl := ψ_mul_x_add_x_mul_ψ R h
  have hxy := x_mul_x_add_x_mul_x R (n := n) (i := i) (j := i + 1) (by omega)
  rw [eq_sub_of_add_eq hl, mul_sub, mul_one, ← mul_assoc, ← mul_assoc,
    eq_neg_of_add_eq_zero_left hxy]
  noncomm_ring

end Consequences

/-! ## The derivative of the defining relations -/

section Obstruction

variable {R} (a b c : R)

theorem lin_derivDiag_comp {n : ℕ} (f g : strands n ⟶ strands n) :
    (pres R).lin ((ansatz R a b c).derivDiag (f ≫ g)) =
      (-1 : R) ^ oddCount g • (End.of ((pres R).diag g) *
          End.of ((pres R).lin ((ansatz R a b c).derivDiag f))) +
        End.of ((pres R).lin ((ansatz R a b c).derivDiag g)) * End.of ((pres R).diag f) := by
  rw [LocalDerivation.derivDiag_comp, Presentation.lin_add, Presentation.lin_smul,
    Presentation.lin_comp, Presentation.lin_comp, Presentation.lin_of, Presentation.lin_of]
  rfl

/-- The derivative of the square relation `ψ² = 0` under the ansatz:
`d(ψ ψ) = -(b + c) ψ`. -/
theorem lin_derivFree_square :
    (pres R).lin ((ansatz R a b c).derivFree ((pres R).rel .square)) = -((b + c) • ψ R 2 0) := by
  show (pres R).lin ((ansatz R a b c).derivFree (LinDiagram.of
    (dlay (n := 2) (g := .cross) (i := 0) (by decide) ≫
      dlay (n := 2) (g := .cross) (i := 0) (by decide)))) = _
  rw [LocalDerivation.derivFree_of, lin_derivDiag_comp, lin_derivDiag_cross, oddCount_dlay,
    ← ψ_def R (show 0 + 1 < 2 by decide)]
  have h1 := ψ_mul_x_mul_ψ R (n := 2) (i := 0) (by decide)
  have h2 := ψ_mul_x_succ_mul_ψ R (n := 2) (i := 0) (by decide)
  have h3 := ψ_mul_ψ R 2 0
  have h4 : ∀ z, z * ψ R 2 0 * ψ R 2 0 = 0 := fun z => by rw [mul_assoc, h3, mul_zero]
  simp only [End.of, zero_add] at *
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, ← mul_assoc,
    h1, h2, h4, smul_zero, add_zero]
  module

/-- The derivative of the mixed relation `x₀ ψ + ψ x₁ = 1` under the ansatz:
`(1 - a + b) x₀ + (a - 1 + c) x₁ - 2 b x₀² ψ`. -/
theorem lin_derivFree_mixedRight :
    (pres R).lin ((ansatz R a b c).derivFree ((pres R).rel .mixedRight)) =
      (1 - a + b) • x R 2 0 + (a - 1 + c) • x R 2 1 - (2 * b) • (x R 2 0 * (x R 2 0 * ψ R 2 0)) := by
  show (pres R).lin ((ansatz R a b c).derivFree
    (LinDiagram.of (dlay (n := 2) (g := .cross) (i := 0) (by decide) ≫
        dlay (n := 2) (g := .dot) (i := 0) (by decide)) +
      LinDiagram.of (dlay (n := 2) (g := .dot) (i := 1) (by decide) ≫
        dlay (n := 2) (g := .cross) (i := 0) (by decide)) -
      LinDiagram.of (𝟙 (strands (Rel.width .mixedRight))))) = _
  have e0 : (ansatz R a b c).derivDiag (𝟙 (strands (Rel.width .mixedRight))) = 0 := LocalDerivation.derivDiag_id _ _
  rw [map_sub, map_add, LocalDerivation.derivFree_of, LocalDerivation.derivFree_of,
    LocalDerivation.derivFree_of, e0, Presentation.lin_sub,
    Presentation.lin_add, Presentation.lin_zero, sub_zero, lin_derivDiag_comp, lin_derivDiag_comp,
    lin_derivDiag_cross, lin_derivDiag_dot, lin_derivDiag_dot, oddCount_dlay, oddCount_dlay,
    ← ψ_def R (show 0 + 1 < 2 by decide), ← x_def R (show 0 < 2 by decide),
    ← x_def R (show 1 < 2 by decide)]
  have e1 := x_mul_x_mul_ψ_sub R (n := 2) (i := 0) (by decide)
  have e2 := x_mul_ψ_mul_x_succ R (n := 2) (i := 0) (by decide)
  have e3 := x_succ_mul_ψ_mul_x_succ R (n := 2) (i := 0) (by decide)
  simp only [End.of, zero_add, ← mul_assoc] at *
  rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add] at e1
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, ← mul_assoc,
    ← e1, e2, e3]
  module

/-- The derivative of the mixed relation `ψ x₀ + x₁ ψ = 1` under the ansatz:
`(a - 1 + b) x₀ + (1 - a + c) x₁ - 2 c x₁² ψ`. -/
theorem lin_derivFree_mixedLeft :
    (pres R).lin ((ansatz R a b c).derivFree ((pres R).rel .mixedLeft)) =
      (a - 1 + b) • x R 2 0 + (1 - a + c) • x R 2 1 - (2 * c) • (x R 2 1 * (x R 2 1 * ψ R 2 0)) := by
  show (pres R).lin ((ansatz R a b c).derivFree
    (LinDiagram.of (dlay (n := 2) (g := .dot) (i := 0) (by decide) ≫
        dlay (n := 2) (g := .cross) (i := 0) (by decide)) +
      LinDiagram.of (dlay (n := 2) (g := .cross) (i := 0) (by decide) ≫
        dlay (n := 2) (g := .dot) (i := 1) (by decide)) -
      LinDiagram.of (𝟙 (strands (Rel.width .mixedLeft))))) = _
  have e0 : (ansatz R a b c).derivDiag (𝟙 (strands (Rel.width .mixedLeft))) = 0 := LocalDerivation.derivDiag_id _ _
  rw [map_sub, map_add, LocalDerivation.derivFree_of, LocalDerivation.derivFree_of,
    LocalDerivation.derivFree_of, e0, Presentation.lin_sub,
    Presentation.lin_add, Presentation.lin_zero, sub_zero, lin_derivDiag_comp, lin_derivDiag_comp,
    lin_derivDiag_cross, lin_derivDiag_dot, lin_derivDiag_dot, oddCount_dlay, oddCount_dlay,
    ← ψ_def R (show 0 + 1 < 2 by decide), ← x_def R (show 0 < 2 by decide),
    ← x_def R (show 1 < 2 by decide)]
  have e1 := x_succ_mul_x_succ_mul_ψ_sub R (n := 2) (i := 0) (by decide)
  have e2 := x_mul_ψ_mul_x R (n := 2) (i := 0) (by decide)
  have e3 := x_succ_mul_ψ_mul_x R (n := 2) (i := 0) (by decide)
  have e4 : x R 2 1 * x R 2 0 = -(x R 2 0 * x R 2 1) :=
    eq_neg_of_add_eq_zero_left (x_mul_x_add_x_mul_x R (n := 2) (i := 1) (j := 0) (by decide))
  simp only [End.of, zero_add, ← mul_assoc] at *
  rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add] at e1
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, ← mul_assoc,
    ← e1, e2, e3, e4, neg_mul]
  module

end Obstruction

/-! ## Compatibility with the odd nilHecke relations -/

/-- The defining relations are homogeneous: the square relation has two odd generators, the
braid relation three in each term, and each mixed relation an even number in each term. -/
theorem relation_hasParity (r : Rel) : ∃ p, ((pres R).rel r).HasParity p := by
  classical
  cases r with
  | square => exact ⟨2, LinDiagram.hasParity_of rfl⟩
  | braid =>
    refine ⟨3, fun d hd => ?_⟩
    rcases Finset.mem_union.mp (Finsupp.support_sub hd) with h | h <;>
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)] <;> rfl
  | mixedRight =>
    refine ⟨0, fun d hd => ?_⟩
    rcases Finset.mem_union.mp (Finsupp.support_sub hd) with h | h
    · rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h <;>
        rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)] <;> simp [oddCount_comp, oddCount_dlay]
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; rfl
  | mixedLeft =>
    refine ⟨0, fun d hd => ?_⟩
    rcases Finset.mem_union.mp (Finsupp.support_sub hd) with h | h
    · rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h <;>
        rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)] <;> simp [oddCount_comp, oddCount_dlay]
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; rfl

theorem endOf_comp {X : ONH R} (f g : X ⟶ X) : End.of (f ≫ g) = End.of g * End.of f := rfl

/-- The derivative of the braid relation vanishes for `δ(crossing) = 1`: both sides have
derivative `ψ₁ ψ₀ + ψ₀ ψ₁` modulo `ψ_i² = 0`. -/
theorem lin_derivFree_braid :
    (pres R).lin ((D R).derivFree ((pres R).rel .braid)) = 0 := by
  show (pres R).lin ((ansatz R 1 0 0).derivFree
    (LinDiagram.of (dlay (n := 3) (g := .cross) (i := 0) (by decide) ≫
        dlay (n := 3) (g := .cross) (i := 1) (by decide) ≫
        dlay (n := 3) (g := .cross) (i := 0) (by decide)) -
      LinDiagram.of (dlay (n := 3) (g := .cross) (i := 1) (by decide) ≫
        dlay (n := 3) (g := .cross) (i := 0) (by decide) ≫
        dlay (n := 3) (g := .cross) (i := 1) (by decide)))) = 0
  rw [map_sub, LocalDerivation.derivFree_of, LocalDerivation.derivFree_of, Presentation.lin_sub,
    lin_derivDiag_comp, lin_derivDiag_comp, lin_derivDiag_comp, lin_derivDiag_comp,
    lin_derivDiag_cross, lin_derivDiag_cross, Presentation.diag_comp, Presentation.diag_comp,
    endOf_comp, endOf_comp,
    ← ψ_def R (show 0 + 1 < 3 by decide), ← ψ_def R (show 1 + 1 < 3 by decide)]
  have h0 := ψ_mul_ψ R 3 0
  have h1 := ψ_mul_ψ R 3 1
  simp only [oddCount_comp, oddCount_dlay, End.of, one_smul, zero_smul, add_zero, mul_one,
    one_mul, pow_one, show (1 + 1 : ℕ) = 2 from rfl, neg_one_sq, neg_one_smul, add_mul, neg_mul,
    h0, h1]
  abel

/-- **The local differential of Ellis–Qi Proposition 3.3 is compatible with the odd nilHecke
relations**: `δ(dot) = x²`, `δ(crossing) = 1` descends to the presented category `ONH R`, for
every commutative ring `R`. -/
theorem compatible : (D R).Compatible (pres R) where
  hasParity := relation_hasParity R
  rel r := by
    cases r with
    | square =>
      rw [D, lin_derivFree_square, add_zero, zero_smul, neg_zero]
    | braid => exact lin_derivFree_braid R
    | mixedRight =>
      rw [D, lin_derivFree_mixedRight]
      simp
    | mixedLeft =>
      rw [D, lin_derivFree_mixedLeft]
      simp

/-! ## The differential -/

/-- The differential of Ellis–Qi Proposition 3.3 on the presented category `ONH R`, induced by
the compatible local derivation `D R`. -/
abbrev deriv {a b : Obj sig} : ((pres R).obj a ⟶ (pres R).obj b) →ₗ[R] ((pres R).obj a ⟶ (pres R).obj b) :=
  (pres R).deriv (compatible R)

/-- The differential on the endomorphism algebra of `n` strands. -/
abbrev d (n : ℕ) : End ((pres R).obj (strands n)) →ₗ[R] End ((pres R).obj (strands n)) :=
  (pres R).derivEnd (compatible R) (strands n)

/-- The value on the dot generator: `d(dot) = dot ≫ dot`. -/
theorem deriv_dot :
    deriv R ((pres R).diag (ofGen (S := sig) Gen.dot)) =
      (pres R).diag (ofGen (S := sig) Gen.dot) ≫ (pres R).diag (ofGen (S := sig) Gen.dot) := by
  rw [Presentation.deriv_ofGen, D_δ_dot, Presentation.lin_of, Presentation.diag_comp]

/-- The value on the crossing generator: `d(crossing) = 1`, the identity of two strands
(Ellis–Qi, Proposition 3.3). -/
theorem deriv_cross :
    deriv R ((pres R).diag (ofGen (S := sig) Gen.cross)) = 𝟙 ((pres R).obj (sig.genDom Gen.cross)) := by
  rw [Presentation.deriv_ofGen, D_δ_cross, Presentation.lin_of, Presentation.diag_id]

/-- `d(x_i) = x_i²` (Ellis–Qi (3.1)). -/
theorem d_x (n i : ℕ) : d R n (x R n i) = x R n i * x R n i := by
  by_cases h : i < n
  · rw [x_def R h, Presentation.derivEnd_apply, Presentation.deriv_diag, ← x_def R h]
    exact lin_derivDiag_dot 1 0 0 (n := n) (i := i) (by simpa [Gen.arity] using h)
  · rw [x, dif_neg h, map_zero, mul_zero]

/-- `d(ψ_i) = 1` (Ellis–Qi, Proposition 3.3: `d(∂_i) = 1`). -/
theorem d_ψ {n i : ℕ} (h : i + 1 < n) : d R n (ψ R n i) = 1 := by
  rw [ψ_def R h, Presentation.derivEnd_apply, Presentation.deriv_diag]
  refine (lin_derivDiag_cross 1 0 0 (n := n) (i := i) (by simpa [Gen.arity] using h)).trans ?_
  simp

theorem x_eq_lin {n i : ℕ} (h : i < n) :
    (pres R).lin (LinDiagram.of (dlay (g := .dot) (n := n) (i := i) (by simpa [Gen.arity] using h))) =
      x R n i :=
  (x_def R h).symm

theorem ψ_eq_lin {n i : ℕ} (h : i + 1 < n) :
    (pres R).lin (LinDiagram.of (dlay (g := .cross) (n := n) (i := i) (by simpa [Gen.arity] using h))) =
      ψ R n i :=
  (ψ_def R h).symm

/-- The super Leibniz rule, Ellis–Qi (2.3): `d(f g) = d(f) g + (-1)^p f d(g)` for `f`
homogeneous of parity `p`. -/
theorem d_mul {n : ℕ} (f g : End ((pres R).obj (strands n))) {F : LinDiagram R (strands n) (strands n)}
    {p : ℕ} (hF : F.HasParity p) (hf : (pres R).lin F = f) :
    d R n (f * g) = d R n f * g + (-1 : R) ^ p • (f * d R n g) :=
  (pres R).deriv_mul (compatible R) f g hF hf

/-- `d(x_i g) = x_i² g - x_i d(g)`. -/
theorem d_x_mul (n i : ℕ) (g : End ((pres R).obj (strands n))) :
    d R n (x R n i * g) = x R n i * x R n i * g - x R n i * d R n g := by
  by_cases h : i < n
  · rw [d_mul R _ g (LinDiagram.hasParity_of (p := 1) (by rw [oddCount_dlay])) (x_eq_lin R h), d_x,
      pow_one, neg_one_smul, sub_eq_add_neg]
  · simp [x, dif_neg h]

/-- `d(ψ_i g) = g - ψ_i d(g)`. -/
theorem d_ψ_mul {n i : ℕ} (h : i + 1 < n) (g : End ((pres R).obj (strands n))) :
    d R n (ψ R n i * g) = g - ψ R n i * d R n g := by
  rw [d_mul R _ g (LinDiagram.hasParity_of (p := 1) (by rw [oddCount_dlay])) (ψ_eq_lin R h), d_ψ R h,
    pow_one, neg_one_smul, one_mul, sub_eq_add_neg]

/-- **`d² = 0`** on every Hom-space of `ONH R`, checked on the generators:
`d(d(dot)) = d(x²) = x² x - x x² = 0` and `d(d(crossing)) = d(1) = 0`. -/
theorem deriv_deriv {a b : Obj sig} (f : (pres R).obj a ⟶ (pres R).obj b) :
    deriv R (deriv R f) = 0 := by
  refine Presentation.deriv_deriv_eq_zero _ _ (fun g => ?_) f
  cases g with
  | dot =>
    rw [deriv_dot, Presentation.deriv_comp_diag]
    erw [deriv_dot]
    rw [oddCount_ofGen]
    show ((-1 : R) ^ 1) • _ + _ = 0
    rw [pow_one, neg_one_smul, Category.assoc, neg_add_cancel]
  | cross =>
    rw [deriv_cross, ← Presentation.diag_id, Presentation.deriv_diag]
    exact Presentation.lin_zero _

/-- `d² = 0` on the endomorphism algebra of `n` strands. -/
theorem d_d (n : ℕ) (f : End ((pres R).obj (strands n))) : d R n (d R n f) = 0 :=
  deriv_deriv R f

/-! ## The parity grading; `d` is odd -/

/-- The parity grading: every generator is odd. -/
def parityDeg : sig.Gen → ZMod 2 := fun _ => 1

theorem sum_map_parityDeg (ls : List (Layer sig)) :
    (ls.map fun L => parityDeg L.gen).sum = (oddCountList ls : ZMod 2) := by
  induction ls with
  | nil => rfl
  | cons L ls ih =>
    rw [List.map_cons, List.sum_cons, ih, oddCountList_cons, oddCountList_singleton]
    simp [parityDeg, sig, add_comm]

/-- The parity degree of a diagram is its number of odd generators modulo `2`. -/
theorem degree_parityDeg {a b : Obj sig} (f : a ⟶ b) :
    Diagram.degree parityDeg f = (oddCount f : ZMod 2) :=
  sum_map_parityDeg _

/-- A linear combination of diagrams of parity degree `k` is homogeneous of parity `k.val` in
the sense of `LinDiagram.HasParity`. -/
theorem hasParity_of_mem_homDeg {a b : Obj sig} {F : LinDiagram R a b} {k : ZMod 2}
    (hF : F ∈ LinDiagram.homDeg R parityDeg a b k) : F.HasParity k.val := by
  intro g hg
  have h := (LinDiagram.mem_homDeg_iff.mp hF) g (Finsupp.mem_support_iff.mp hg)
  rw [degree_parityDeg] at h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast] at this
  rw [this, Nat.mod_eq_of_lt (ZMod.val_lt k)]

/-- The odd nilHecke presentation is homogeneous for the parity grading. -/
theorem isHomogeneous_parity : (pres R).IsHomogeneous parityDeg := by
  intro r
  classical
  cases r with
  | square => exact ⟨_, LinDiagram.of_mem_homDeg _⟩
  | braid =>
    refine ⟨1, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.of_mem_homDeg' ?_)⟩ <;>
      rw [degree_parityDeg, oddCount_comp, oddCount_comp, oddCount_dlay, oddCount_dlay] <;> rfl
  | mixedRight =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (LinDiagram.of_mem_homDeg' ?_)
      (LinDiagram.of_mem_homDeg' ?_)) (LinDiagram.of_mem_homDeg' ?_)⟩
    · rw [degree_parityDeg, oddCount_comp, oddCount_dlay, oddCount_dlay]; rfl
    · rw [degree_parityDeg, oddCount_comp, oddCount_dlay, oddCount_dlay]; rfl
    · rw [degree_parityDeg]; rfl
  | mixedLeft =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (LinDiagram.of_mem_homDeg' ?_)
      (LinDiagram.of_mem_homDeg' ?_)) (LinDiagram.of_mem_homDeg' ?_)⟩
    · rw [degree_parityDeg, oddCount_comp, oddCount_dlay, oddCount_dlay]; rfl
    · rw [degree_parityDeg, oddCount_comp, oddCount_dlay, oddCount_dlay]; rfl
    · rw [degree_parityDeg]; rfl

section Odd

variable {R} (a b c : R)

theorem ansatzδ_mem_homDeg (g : sig.Gen) :
    (ansatz R a b c).δ g ∈ LinDiagram.homDeg R parityDeg (sig.genDom g) (sig.genCod g) 0 := by
  cases g with
  | dot =>
    exact LinDiagram.of_mem_homDeg' (by rw [degree_parityDeg, oddCount_comp, oddCount_ofGen]; rfl)
  | cross =>
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)
    · exact LinDiagram.of_mem_homDeg' (by rw [degree_parityDeg]; rfl)
    · exact LinDiagram.of_mem_homDeg'
        (by rw [degree_parityDeg, oddCount_comp, oddCount_dlay, oddCount_dlay]; rfl)
    · exact LinDiagram.of_mem_homDeg'
        (by rw [degree_parityDeg, oddCount_comp, oddCount_dlay, oddCount_dlay]; rfl)

theorem derivList_mem_homDeg (ls : List (Layer sig)) {X Y : Obj sig} (h : Chain X ls Y) :
    (ansatz R a b c).derivList X ls Y h ∈
      LinDiagram.homDeg R parityDeg X Y ((oddCountList ls : ZMod 2) + 1) := by
  induction ls generalizing X with
  | nil =>
    rw [LocalDerivation.derivList]
    exact Submodule.zero_mem _
  | cons L ls ih =>
    rw [LocalDerivation.derivList]
    apply LinDiagram.cast_mem_homDeg
    have hL : oddCountList (L :: ls) = 1 + oddCountList ls := by
      rw [oddCountList_cons, oddCountList_singleton]; rfl
    have hδ : (ansatz R a b c).layerDeriv L h.1 ∈ LinDiagram.homDeg R parityDeg _ _ 0 :=
      LinDiagram.whisker_mem_homDeg (ansatzδ_mem_homDeg a b c L.gen) _ _ _
    have hmk : LinDiagram.of (Diagram.mk ls h.2.2) ∈
        LinDiagram.homDeg R parityDeg _ _ (oddCountList ls : ZMod 2) :=
      LinDiagram.of_mem_homDeg' (by rw [degree_parityDeg]; rfl)
    have hlay : LinDiagram.of (Diagram.ofLayer L h.1) ∈
        LinDiagram.homDeg R parityDeg _ _ (1 : ZMod 2) :=
      LinDiagram.of_mem_homDeg' (by rw [Diagram.degree_ofLayer]; rfl)
    have e : ∀ t : ZMod 2, 0 + t = (1 + t) + 1 ∧ 1 + (t + 1) = (1 + t) + 1 := by decide
    rw [hL, Nat.cast_add, Nat.cast_one]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ?_
    · exact (e _).1 ▸ LinDiagram.comp_mem_homDeg hδ hmk
    · exact (e _).2 ▸ LinDiagram.comp_mem_homDeg hlay (ih _)

/-- The derivative of a diagram has the opposite parity. -/
theorem derivDiag_mem_homDeg {a' b' : Obj sig} (f : a' ⟶ b') :
    (ansatz R a b c).derivDiag f ∈
      LinDiagram.homDeg R parityDeg a' b' (Diagram.degree parityDeg f + 1) := by
  rw [degree_parityDeg]
  exact derivList_mem_homDeg a b c _ _

end Odd

/-- **The differential is odd**: it maps morphisms of parity `k` to morphisms of parity
`k + 1`. -/
theorem deriv_mem_homDeg {X Y : Obj sig} {f : (pres R).obj X ⟶ (pres R).obj Y} {k : ZMod 2}
    (hf : f ∈ (pres R).homDeg parityDeg X Y k) :
    deriv R f ∈ (pres R).homDeg parityDeg X Y (k + 1) := by
  obtain ⟨F, hF, rfl⟩ := Presentation.mem_homDeg_iff.mp hf
  rw [deriv, Presentation.deriv_lin]
  refine Presentation.lin_mem_homDeg ?_
  clear hf
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hF
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    rw [LocalDerivation.derivFree_single, one_smul]
    exact (show Diagram.degree parityDeg g = k from hg) ▸ derivDiag_mem_homDeg 1 0 0 g
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy

theorem x_mem_endDeg (n i : ℕ) : x R n i ∈ (pres R).endDeg parityDeg (strands n) 1 := by
  by_cases h : i < n
  · rw [x_def R h]
    exact Presentation.diag_mem_homDeg' (by rw [degree_parityDeg, oddCount_dlay]; rfl)
  · rw [x, dif_neg h]; exact Submodule.zero_mem _

theorem ψ_mem_endDeg (n i : ℕ) : ψ R n i ∈ (pres R).endDeg parityDeg (strands n) 1 := by
  by_cases h : i + 1 < n
  · rw [ψ_def R h]
    exact Presentation.diag_mem_homDeg' (by rw [degree_parityDeg, oddCount_dlay]; rfl)
  · rw [ψ, dif_neg h]; exact Submodule.zero_mem _

/-- The super Leibniz rule, Ellis–Qi (2.3), for `f` of parity `k` in the parity grading
`(pres R).endDeg parityDeg`: `d(f g) = d(f) g + (-1)^k f d(g)`. -/
theorem d_mul_of_mem {n : ℕ} {f : End ((pres R).obj (strands n))} {k : ZMod 2}
    (hf : f ∈ (pres R).endDeg parityDeg (strands n) k) (g : End ((pres R).obj (strands n))) :
    d R n (f * g) = d R n f * g + (-1 : R) ^ k.val • (f * d R n g) := by
  obtain ⟨F, hF, rfl⟩ := Presentation.mem_homDeg_iff.mp hf
  exact d_mul R _ g (hasParity_of_mem_homDeg R hF) rfl

end OddMath.Diagrams.OddNilHecke

end
