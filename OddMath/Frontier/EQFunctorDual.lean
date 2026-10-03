import OddMath.Frontier.EQFunctorRing
import OddMath.Frontier.EQFunctorRightDual

/-!
# The dual bimodule `Z_{a,b}^∨` as a dg `(OΛ_{a+b}, OΛ_a ⊗ OΛ_b)`-bimodule

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, Definition 4.6, (4.24)–(4.25), Corollary 4.11, and §4.4, Definition 4.14 (printed
numbering).

Ellis–Qi define `Z_{a,b}^∨ = HOM_{OΛ_{a+b}}(Z_{a,b}, OΛ_{a+b})` (Definition 4.14, (4.25)), a dg
bimodule over `(OΛ_{a+b}, OΛ_{a,b})`, `OΛ_{a,b} = OΛ_a ⊗ OΛ_b`. Here `Z_{a,b}` is the right dg
`OΛ_{a+b}`-module `OddMath.Frontier.EQFix.Zab a b` (the model of `EQZabModule`: the element
`f(x) g(y) ∈ OΛ_a ⊠ OΛ_b` stands for `(f ⊗ g) · z`, with differential `dZ` and right action of
`h ∈ OΛ_{a+b}` by right multiplication with `φ(h)`).

* `Zab.instDGModuleAB`, `Zab.instDGBimodule` (**Definition 4.6**): `Z_{a,b}` is a left dg module
  over `OΛ_{a,b}` (`EQFunctor.osymABDG a b`), acting by left multiplication, and a dg
  `(OΛ_{a,b}, OΛ_{a+b})`-bimodule in the sense of the `DG` library.
* `zabRightBasis`: the basis `{s̃_μ(y) z : μ ∈ Par(b,a)}` of the right `OΛ_{a+b}`-module `Z_{a,b}`
  ((4.21), Corollary 4.8), `s̃_μ(y) z` of degree `|μ|`, with `d(s̃_μ(y) z)` in the span of the
  `s̃_ν(y) z`, `|ν| = |μ| + 1` (Lemma 4.7; `zabRightBasis_key`).
* `ZDual a b`: `Z_{a,b}^∨`, the graded dual `EQFunctor.RightDual` of the right dg
  `OΛ_{a+b}`-module `Z_{a,b}`: the right `OΛ_{a+b}`-linear maps `Z_{a,b} → OΛ_{a+b}` with the
  Hom-complex differential, the left action `(c f)(F) = c f(F)` of `OΛ_{a+b}` and the right action
  `(f g)(F) = f(g F)` of `OΛ_{a,b}`. It is a dg `(OΛ_{a+b}, OΛ_{a,b})`-bimodule in the sense of the
  `DG` library (`ZDual.instDGBimodule`).
* **Corollary 4.11** (`zdualTriangular`, `zdualFiniteCellFiltration`, `zdual_isKProjective`,
  `zdual_hasLiftingProperty`): the dual basis `{δ_μ}`, `δ_μ` of degree `-|μ|`, is a homogeneous
  basis of the left `OΛ_{a+b}`-module `Z_{a,b}^∨`, triangular for the differential when ordered by
  increasing `|μ|`; so `Z_{a,b}^∨` is a finite-cell left dg `OΛ_{a+b}`-module with
  `binom(a+b, a)` cells `OΛ_{a+b}⟦|μ|⟧`, `μ ∈ Par(b,a)` (`zdualFiniteCellFiltration_length`,
  `zdualFiniteCellFiltration_e`), hence K-projective and cofibrant. Its class in `K₀(OΛ_{a+b})` is
  `EQFunctor.K0_zdual` (in `EQFunctorDerived`).

All gradings are those of the `DG` library on `OPol_{a+b}` (half the Ellis–Qi `q`-degree); in
`q`-degrees the cell of `δ_μ` is `OΛ_{a+b}` with its generator in degree `-2|μ|`, in accordance with
the graded rank `[a+b choose a]_q` of Corollary 4.11 up to the overall normalization of the
generator `z^∨`.
-/

universe w

namespace OddMath.Frontier.EQFunctor

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (osymAB inclX inclY dZ phiAB)
open OddMath.Frontier.EQFix (Zab ParIdx zabB zabB_mem zabC zabC_spec zab_coeff_unique
  zabFreeBasis zab_key toSkew toSkew_mem ofOsym ofOsym_toSkew unopO opO)
open DG MulOpposite

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) functorDualNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))
local instance (priority := high) functorDualNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

theorem sk_one_mul {m : ℕ} (x : SkewPolynomial m) : 1 * x = x := by
  let := OddMath.PbwL3.instSemiring m
  exact one_mul x

variable {a b : ℕ}

/-! ## `Z_{a,b}` as a dg `(OΛ_a ⊗ OΛ_b, OΛ_{a+b})`-bimodule -/

/-- An element of the dg ring `OΛ_{a,b}` as an odd polynomial. -/
def skg (g : osymABDG a b) : SkewPolynomial (a+b) := (OPol.equiv (a+b)).symm (g : OPol (a+b))

theorem skg_mem (g : osymABDG a b) : skg g ∈ osymAB a b := mem_osymABDG.mp g.2

theorem skg_mul (g g' : osymABDG a b) : skg (g * g') = skg g * skg g' := rfl
theorem skg_one : skg (1 : osymABDG a b) = 1 := rfl
theorem skg_add (g g' : osymABDG a b) : skg (g + g') = skg g + skg g' := rfl
theorem skg_zero : skg (0 : osymABDG a b) = 0 := rfl

theorem skg_mem_grading {i : ℤ} {g : osymABDG a b} (hg : g ∈ DG.grading i) :
    skg g ∈ grading (a+b) i := hg

theorem skg_d (g : osymABDG a b) : skg (DG.d g) = d (a+b) (skg g) := rfl

namespace Zab

/-- Left multiplication by `g ∈ OΛ_a ⊠ OΛ_b` on `Z_{a,b}`. -/
def lsmul (g : osymABDG a b) (F : Zab a b) : Zab a b :=
  Zab.mk (skg g * F.val) (mul_mem (skg_mem g) F.mem)

@[simp] theorem val_lsmul (g : osymABDG a b) (F : Zab a b) : (lsmul g F).val = skg g * F.val :=
  rfl

/-- The left `OΛ_a ⊗ OΛ_b`-module structure of `Z_{a,b}`: `(f ⊗ g) · F z = f(x) g(y) F z`. -/
instance instModuleAB : Module (osymABDG a b) (Zab a b) where
  smul := lsmul
  one_smul F := Zab.ext (by
    change skg (1 : osymABDG a b) * F.val = F.val
    rw [skg_one, sk_one_mul])
  mul_smul g g' F := Zab.ext (by
    change skg (g * g') * F.val = skg g * (skg g' * F.val)
    rw [skg_mul]; exact EQFix.sp_mul_assoc _ _ _)
  smul_zero g := Zab.ext (by
    change skg g * (0 : SkewPolynomial (a+b)) = 0
    exact EQFix.sp_mul_zero _)
  smul_add g F G := Zab.ext (by
    change skg g * (F.val + G.val) = skg g * F.val + skg g * G.val
    rw [mul_add])
  add_smul g g' F := Zab.ext (by
    change skg (g + g') * F.val = skg g * F.val + skg g' * F.val
    rw [skg_add, add_mul])
  zero_smul F := Zab.ext (by
    change skg (0 : osymABDG a b) * F.val = 0
    rw [skg_zero]; exact EQFix.sp_zero_mul _)

theorem val_smul (g : osymABDG a b) (F : Zab a b) : (g • F).val = skg g * F.val := rfl

/-- **Ellis–Qi, Definition 4.6**: `Z_{a,b}` is a left dg module over `OΛ_a ⊗ OΛ_b`. -/
instance instDGModuleAB : DGModule (osymABDG a b) (Zab a b) where
  smul_mem i j g F hg hF := by
    rw [vadd_eq_add, Zab.mem_grading_iff, val_smul]
    exact mul_mem_grading' (skg_mem_grading hg) (Zab.mem_grading_iff.mp hF)
  d_smul' {n g} hg F := by
    apply Zab.ext
    simp only [Zab.val_d, val_smul, Zab.val_add, Units.smul_def, Zab.val_zsmul]
    rw [EQZab.dZ_mul, skg_d, parityInv_of_mem (skg_mem_grading hg), smul_mul_assoc]

instance instSMulCommClassAB :
    SMulCommClass (osymABDG a b) (osymDG (a+b))ᵐᵒᵖ (Zab a b) where
  smul_comm g c F := Zab.ext (by
    change skg g * (F.val * phiAB a b (toSkew (unop c))) =
      skg g * F.val * phiAB a b (toSkew (unop c))
    exact (EQFix.sp_mul_assoc _ _ _).symm)

/-- **Ellis–Qi, Definition 4.6**: `Z_{a,b}` is a dg `(OΛ_a ⊗ OΛ_b, OΛ_{a+b})`-bimodule. -/
instance instDGBimodule : DGBimodule (osymABDG a b) (osymDG (a+b)) (Zab a b) :=
  DGBimodule.mk'

end Zab

/-! ## The basis of `Z_{a,b}` as a right `OΛ_{a+b}`-module -/

/-- **(4.21), Corollary 4.8**: the `s̃_μ(y) z`, `μ ∈ Par(b,a)`, of degree `|μ|`, form a homogeneous
basis of the right `OΛ_{a+b}`-module `Z_{a,b}`. -/
def zabRightBasis (a b : ℕ) : RightBasis (osymDG (a+b)) (Zab a b) (ParIdx a b) where
  b := zabB
  deg μ := totalDeg μ.1
  b_mem := zabB_mem
  coeff F μ := ofOsym (zabC F μ)
  sum_coeff F := by
    apply Zab.ext
    rw [Zab.val_sum, zabC_spec F]
    rfl
  coeff_sum x := by
    have hy : (∑ μ, op (x μ) • zabB μ : Zab a b).val =
        ∑ μ : ParIdx a b, inclY a b (EQSchur.untwisted b μ.1) *
          phiAB a b ((⟨toSkew (x μ), toSkew_mem _⟩ : osym (a+b)) : SkewPolynomial (a+b)) := by
      rw [Zab.val_sum]
      rfl
    have hc := zab_coeff_unique _ _ ((zabC_spec _).symm.trans hy)
    funext μ
    rw [hc]
    rfl

@[simp] theorem zabRightBasis_deg (μ : ParIdx a b) :
    (zabRightBasis a b).deg μ = totalDeg μ.1 := rfl

/-- **Lemma 4.7**: `d(s̃_μ(y) z)` only involves the `s̃_ν(y) z` with `|ν| = |μ| + 1`. -/
theorem zabRightBasis_key (μ ν : ParIdx a b)
    (h : (zabRightBasis a b).coeff (DG.d ((zabRightBasis a b).b μ)) ν ≠ 0) :
    -totalDeg ν.1 < -totalDeg μ.1 := by
  refine zab_key μ ν fun h0 => h ?_
  have h1 := congrArg (fun x => Shift.twist (osymDG (a+b)) (totalDeg ν.1) (unopO (a+b) x)) h0
  change Shift.twist (osymDG (a+b)) (totalDeg ν.1) (unopO (a+b) (opO (a+b)
    (Shift.twist (osymDG (a+b)) (totalDeg ν.1) (ofOsym (zabC (DG.d (zabB μ)) ν))))) =
    Shift.twist (osymDG (a+b)) (totalDeg ν.1) (unopO (a+b) 0) at h1
  rw [GradedOpposite.unop_op, Shift.twist_twist_self, map_zero, map_zero] at h1
  exact h1

/-! ## The dual bimodule -/

/-- **`Z_{a,b}^∨ = HOM_{OΛ_{a+b}}(Z_{a,b}, OΛ_{a+b})`** (Ellis–Qi (4.25), Definition 4.14): the
graded dual of the right dg `OΛ_{a+b}`-module `Z_{a,b}`. -/
abbrev ZDual (a b : ℕ) : Type := RightDual (osymDG (a+b)) (Zab a b)

namespace ZDual

/-- **`Z_{a,b}^∨` is a dg `(OΛ_{a+b}, OΛ_a ⊗ OΛ_b)`-bimodule** (Ellis–Qi, Definition 4.14):
`(c f)(F) = c f(F)` for `c ∈ OΛ_{a+b}` and `(f g)(F) = f(g F)` for `g ∈ OΛ_a ⊗ OΛ_b`. -/
instance instDGBimodule : DGBimodule (osymDG (a+b)) (osymABDG a b) (ZDual a b) :=
  RightDual.instDGBimodule

end ZDual

/-- **Ellis–Qi, Corollary 4.11** (basis): the dual basis `δ_μ` (`δ_μ(s̃_ν(y) z) = δ_{μν}`), of
degree `-|μ|`, ordered by increasing `|μ|`, is a triangular basis of the left dg
`OΛ_{a+b}`-module `Z_{a,b}^∨`. -/
def zdualTriangular (a b : ℕ) : EQFix.TriangularBasis (osymDG (a+b)) (ZDual a b) :=
  (zabRightBasis a b).dualTriangular (fun μ => -totalDeg μ.1) fun l i h =>
    zabRightBasis_key l i h

/-- **Ellis–Qi, Corollary 4.11**: `Z_{a,b}^∨` is a finite-cell left dg module over `OΛ_{a+b}`,
for all `a, b`. -/
def zdualFiniteCellFiltration (a b : ℕ) : FiniteCellFiltration (osymDG (a+b)) (ZDual a b) :=
  (zdualTriangular a b).finiteCellFiltration

/-- The filtration of Corollary 4.11 has `binom(a+b, a)` cells. -/
theorem zdualFiniteCellFiltration_length :
    (zdualFiniteCellFiltration a b).length = (b + a).choose b := by
  change Fintype.card (ParIdx a b) = _
  rw [Fintype.card_coe, BoxPartitionCount.card_box]

/-- The cells of the filtration of Corollary 4.11 are the regular module `OΛ_{a+b}`. -/
theorem zdualFiniteCellFiltration_e (j : Fin (zdualFiniteCellFiltration a b).length) :
    (zdualFiniteCellFiltration a b).e j = EQFix.oneIdempotent (osymDG (a+b)) := rfl

/-- **Ellis–Qi, Corollary 4.11** ("cofibrant"): `Z_{a,b}^∨` is K-projective as a left dg
`OΛ_{a+b}`-module. -/
theorem zdual_isKProjective : IsKProjective.{w} (osymDG (a+b)) (ZDual a b) :=
  (zdualTriangular a b).isKProjective

/-- **Ellis–Qi, Corollary 4.11**: `Z_{a,b}^∨` is cofibrant as a left dg `OΛ_{a+b}`-module (lifting
property against surjective quasi-isomorphisms). -/
theorem zdual_hasLiftingProperty : HasLiftingProperty.{w} (osymDG (a+b)) (ZDual a b) :=
  (zdualTriangular a b).hasLiftingProperty

end

end OddMath.Frontier.EQFunctor
