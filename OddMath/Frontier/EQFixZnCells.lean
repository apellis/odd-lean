import OddMath.Frontier.EQFixFiniteCell
import OddMath.Frontier.EQZnFiniteCell
import OddMath.Frontier.EQDGStructures
import DG.Module.Opposite

/-!
# `Z_n` is a finite-cell right dg `OΛ_n`-module (Proposition 3.16 (1), `DG` form)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.2.2, Example 2.4, and §3.4, (3.37), (3.38), Proposition 3.16 (1).

`Z_n = OPol_n(0,1,0,1,…)` is a right dg module over the dg algebra `OΛ_n` (`osymDG n`) via
`g 1_z · c = g (θ ∘ w₀)(c) 1_z` (`EQSkewDifferential.Zn.dgRightModuleOsym`). Following the `DG`
library, a right dg `OΛ_n`-module is a left dg module over the (Koszul-signed) opposite dg algebra
`OΛ_nᵒᵖ` (`OsymOp n`), with `op c • m = (-1)^{|c||m|} m · c` (`DG.DGRightModule.opModule`).

* `znFreeBasis`: the reversed staircase monomials `x^A 1_z`, `A_i ≤ i` (0-indexed; Ellis–Qi's
  `B'_n`, with the corrected range of ERRATA [EQ] 1), form a homogeneous basis of `Z_n` over
  `OΛ_nᵒᵖ` (from `EQZn.zn_right_basis`), with `x^A 1_z` of degree `|A|`.
* `d(x^A 1_z)` lies in the `ℤ`-span of the `x^B 1_z` with `|B| = |A| + 1` (3.37)
  (`EQZn.dAlpha_monomial_mem_revSpan`), so ordering the basis by decreasing `|A|` gives a
  triangular basis (`znTriangular`).
* **Proposition 3.16 (1)** (`znFiniteCellFiltration`): a `DG.FiniteCellFiltration` of `Z_n` over
  `OΛ_nᵒᵖ` with `n!` cells `OΛ_nᵒᵖ⟦-|A|⟧`, one for each `A ∈ B'_n`
  (`znFiniteCellFiltration_length`).
* Consequently `Z_n` is K-projective and cofibrant (lifting property against surjective
  quasi-isomorphisms) as a right dg `OΛ_n`-module: `zn_isKProjective_osym`,
  `zn_hasLiftingProperty_osym` (Ellis–Qi §2.2, Example 2.4: "finite-cell, thus cofibrant").

All `DG` gradings are half the `q`-degree (see `EQDGStructures`).
-/

universe w

namespace OddMath.Frontier.EQFix

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open EQSkewDifferential (OPol OPolAlpha Zn osym osymDG mem_osymDG twistRev zAlpha dAlpha
  indicator oddStrands totalDeg)
open EQZn (RevStair)
open DG

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) eqFixZnCNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) eqFixZnCNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {n : ℕ}

/-- The opposite dg algebra `OΛ_nᵒᵖ` (product `op a * op b = (-1)^{|a||b|} op (b a)`). -/
abbrev OsymOp (n : ℕ) : Type := GradedOpposite (DGAlgebra.gradingSubmodule ℤ (osymDG n))

/-- `op` and `unop` for `OΛ_nᵒᵖ`. -/
abbrev opO (n : ℕ) := GradedOpposite.op (DGAlgebra.gradingSubmodule ℤ (osymDG n))
abbrev unopO (n : ℕ) := GradedOpposite.unop (DGAlgebra.gradingSubmodule ℤ (osymDG n))

/-- The left `OΛ_nᵒᵖ`-module structure of the right dg `OΛ_n`-module `Z_n`:
`op c • m = (-1)^{|c||m|} m · c`. -/
abbrev znOpModule (n : ℕ) : Module (OsymOp n) (Zn n) := DGRightModule.opModule ℤ

attribute [local instance] znOpModule

/-- `Z_n` is a left dg `OΛ_nᵒᵖ`-module, i.e. a right dg `OΛ_n`-module (Ellis–Qi, Definition 3.8). -/
theorem znOpDGModule (n : ℕ) : DGModule (OsymOp n) (Zn n) :=
  DGRightModule.dgModule_opModule ℤ

attribute [local instance] znOpDGModule

/-- `OΛ_n` as a subring of the skew-polynomial model. -/
def toSkew (a : osymDG n) : SkewPolynomial n := (OPol.equiv n).symm (a : OPol n)

theorem toSkew_mem (a : osymDG n) : toSkew a ∈ osym n := mem_osymDG.mp a.2

/-- An element of `OΛ_n ⊆ OPol_n` as an element of the dg subring `osymDG n`. -/
def ofOsym (c : osym n) : osymDG n :=
  ⟨OPol.equiv n c, mem_osymDG.mpr (by rw [RingEquiv.symm_apply_apply]; exact c.2)⟩

theorem ofOsym_toSkew (a : osymDG n) : ofOsym ⟨toSkew a, toSkew_mem a⟩ = a := rfl

theorem toSkew_ofOsym (c : osym n) : toSkew (ofOsym c) = c := rfl

/-- The skew-polynomial model of `Z_n`. -/
abbrev zE (n : ℕ) : SkewPolynomial n ≃+ Zn n := OPolAlpha.equiv n (oddStrands n)

/-- The right action of `OΛ_n` in the skew-polynomial model: `g 1_z · c = g (θ ∘ w₀)(c) 1_z`. -/
theorem symm_op_smul_osym (a : osymDG n) (g : Zn n) :
    (zE n).symm (MulOpposite.op a • g) = (zE n).symm g * twistRev n (toSkew a) :=
  rfl

/-- The action of `OΛ_nᵒᵖ` on a homogeneous element `m` of degree `k`:
`x • m = m · ι^k(unop x)`, where `ι^k = Shift.twist _ k` is `c ↦ (-1)^{k|c|} c`. -/
theorem op_smul_of_mem {k : ℤ} {m : Zn n} (hm : m ∈ grading k) (x : OsymOp n) :
    x • m = MulOpposite.op (Shift.twist (osymDG n) k (unopO n x)) • m := by
  induction x using DG.induction_on with
  | h_zero => rw [zero_smul, map_zero, map_zero, MulOpposite.op_zero, zero_smul]
  | h_homogeneous x =>
    rename_i i
    have hx : unopO n x ∈ grading (M := osymDG n) i :=
      (GradedOpposite.mem_dgGrading_iff (R := ℤ)).mp x.2
    have h := DGRightModule.opModule_op_smul_of_mem ℤ (M := Zn n) hx hm
    rw [GradedOpposite.op_unop] at h
    rw [h, Shift.twist_of_mem hx, mul_comm, Units.smul_def, Units.smul_def, MulOpposite.op_smul,
      smul_assoc]
  | h_add x y hx hy => rw [add_smul, hx, hy, map_add, map_add, MulOpposite.op_add, add_smul]

/-- The basis element `x^A 1_z` of `Z_n`. -/
def zb (A : RevStair n) : Zn n := zE n (monomial A.val 1)

theorem zb_mem (A : RevStair n) : zb A ∈ grading (M := Zn n) (totalDeg A.val) :=
  EQSkewDifferential.single_mem_grading A.val 1

/-- The unique coefficients `c_A ∈ OΛ_n` of `f 1_z = Σ_A x^A 1_z · c_A` (`EQZn.zn_right_basis`). -/
def zc (x : Zn n) : RevStair n → osym n :=
  (EQZn.zn_right_basis ((zE n).symm x)).choose

theorem zc_spec (x : Zn n) :
    (zE n).symm x = ∑ A, monomial A.val 1 * twistRev n (zc x A) :=
  (EQZn.zn_right_basis ((zE n).symm x)).choose_spec.1

theorem zc_unique (x : Zn n) (c : RevStair n → osym n)
    (hc : (zE n).symm x = ∑ A, monomial A.val 1 * twistRev n (c A)) : c = zc x :=
  (EQZn.zn_right_basis ((zE n).symm x)).choose_spec.2 c hc

/-- The coefficient of `x^A 1_z` for the action of `OΛ_nᵒᵖ`: `op (ι^{|A|}(c_A))`. -/
def zcoeff (x : Zn n) (A : RevStair n) : OsymOp n :=
  opO n (Shift.twist (osymDG n) (totalDeg A.val) (ofOsym (zc x A)))

theorem zcoeff_smul_zb (x : Zn n) (A : RevStair n) :
    zcoeff x A • zb A = MulOpposite.op (ofOsym (zc x A)) • zb A := by
  rw [op_smul_of_mem (zb_mem A), zcoeff, GradedOpposite.unop_op, Shift.twist_twist_self]

theorem symm_smul_zb (a : OsymOp n) (A : RevStair n) :
    (zE n).symm (a • zb A) = monomial A.val 1 *
      twistRev n (toSkew (Shift.twist (osymDG n) (totalDeg A.val) (unopO n a))) := by
  rw [op_smul_of_mem (zb_mem A), symm_op_smul_osym]
  rfl

/-- **Ellis–Qi, (3.38) / Proposition 3.16 (1)**: the reversed staircase monomials `x^A 1_z`
(`A_i ≤ i`, degree `|A|`) form a homogeneous basis of `Z_n` over `OΛ_nᵒᵖ`. -/
def znFreeBasis (n : ℕ) : FreeBasis (OsymOp n) (Zn n) (RevStair n) where
  b := zb
  deg A := totalDeg A.val
  b_mem := zb_mem
  coeff := zcoeff
  sum_coeff x := by
    apply (zE n).symm.injective
    rw [map_sum, zc_spec x]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [zcoeff_smul_zb, symm_op_smul_osym]
    rfl
  coeff_sum a := by
    set y := ∑ A, a A • zb A
    have hy : (zE n).symm y = ∑ A, monomial A.val 1 *
        twistRev n ((⟨toSkew (Shift.twist (osymDG n) (totalDeg A.val) (unopO n (a A))),
          toSkew_mem _⟩ : osym n) : SkewPolynomial n) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun A _ => symm_smul_zb (a A) A
    have hc := zc_unique y _ hy
    funext A
    rw [zcoeff, ← hc, ofOsym_toSkew, Shift.twist_twist_self, GradedOpposite.op_unop]

theorem totalDeg_eq_sum (B : Fin n → ℕ) : totalDeg B = ((∑ i, B i : ℕ) : ℤ) := by
  rw [totalDeg, Nat.cast_sum]

/-- Coefficients of elements of `span_ℤ {x^B 1_z : B ∈ B'_n, |B| = m}` vanish off `|B| = m`. -/
theorem zcoeff_revSpan {m : ℕ} {y : SkewPolynomial n} (hy : y ∈ EQZn.revSpan n m)
    (B : RevStair n) (hB : ∑ i, B.val i ≠ m) : (znFreeBasis n).coeff (zE n y) B = 0 := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨B', hB', hsum, rfl⟩ := hx
    have h1 : zE n (monomial B' 1) = (1 : OsymOp n) • (znFreeBasis n).b ⟨B', hB'⟩ := by
      rw [one_smul]; rfl
    rw [h1, FreeBasis.coeff_basis, Pi.single_eq_of_ne]
    rintro rfl
    exact hB hsum
  | zero => rw [map_zero, FreeBasis.coeff_zero, Pi.zero_apply]
  | add x y _ _ hx hy => rw [map_add, FreeBasis.coeff_add, Pi.add_apply, hx, hy, add_zero]
  | smul k x _ hx => rw [map_zsmul, FreeBasis.coeff_zsmul, Pi.smul_apply, hx, smul_zero]

/-- (3.37): `d(x^A 1_z)` only involves `x^B 1_z` with `|B| = |A| + 1`; so the key `-|A|` strictly
decreases along the differential. -/
theorem zn_key (A B : RevStair n)
    (h : (znFreeBasis n).coeff (d ((znFreeBasis n).b A)) B ≠ 0) :
    -totalDeg B.val < -totalDeg A.val := by
  by_contra hlt
  apply h
  have hd : d ((znFreeBasis n).b A) = zE n (dAlpha (zAlpha n) (monomial A.val 1)) := by
    change d (zE n (monomial A.val 1)) = _
    rw [OPolAlpha.d_equiv, EQSkewDifferential.indicator_oddStrands]
  rw [hd]
  refine zcoeff_revSpan (EQZn.dAlpha_monomial_mem_revSpan A) B fun hsum => hlt ?_
  rw [totalDeg_eq_sum, totalDeg_eq_sum, hsum]
  push_cast
  omega

/-- The triangular basis of `Z_n` over `OΛ_nᵒᵖ`: the `x^A 1_z` ordered by decreasing `|A|`. -/
def znTriangular (n : ℕ) : TriangularBasis (OsymOp n) (Zn n) :=
  (znFreeBasis n).toTriangular (fun A => -totalDeg A.val) zn_key

/-- **Ellis–Qi, Proposition 3.16 (1)**: `Z_n` is a finite-cell right dg module over `OΛ_n`
(a finite-cell left dg module over `OΛ_nᵒᵖ`), for every `n`. The cells are
`OΛ_nᵒᵖ⟦-|A|⟧`, one for each reversed staircase exponent `A` (`A_i ≤ i`), attached in order of
decreasing `|A|`. -/
def znFiniteCellFiltration (n : ℕ) : FiniteCellFiltration (OsymOp n) (Zn n) :=
  (znTriangular n).finiteCellFiltration

/-- The filtration of Proposition 3.16 (1) has one cell for each `A ∈ B'_n` (`n!` cells). -/
theorem znFiniteCellFiltration_length :
    (znFiniteCellFiltration n).length = Fintype.card (RevStair n) := rfl

/-- **Ellis–Qi, Proposition 3.16 (1)** and Example 2.4: `Z_n` is K-projective as a right dg
`OΛ_n`-module (left dg `OΛ_nᵒᵖ`-module), for every `n`. -/
theorem zn_isKProjective_osym : IsKProjective.{w} (OsymOp n) (Zn n) :=
  (znTriangular n).isKProjective

/-- **Ellis–Qi, Proposition 3.16 (1)** and Example 2.4: `Z_n` is cofibrant as a right dg
`OΛ_n`-module (lifting property against surjective quasi-isomorphisms), for every `n`. -/
theorem zn_hasLiftingProperty_osym : HasLiftingProperty.{w} (OsymOp n) (Zn n) :=
  (znTriangular n).hasLiftingProperty

end

end OddMath.Frontier.EQFix
