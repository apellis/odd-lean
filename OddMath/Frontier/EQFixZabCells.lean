import OddMath.Frontier.EQFixZnCells
import OddMath.Frontier.EQZabFiltration
import OddMath.Frontier.EQZabSchur
import OddMath.Frontier.LongestFactor

/-!
# `Z_{a,b}` is a finite-cell right dg `OΛ_{a+b}`-module (Corollary 4.8, `DG` form)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.2.2, Example 2.4, and §4.3.2, Definition 4.6, Lemma 4.7, Corollary 4.8.

Model of `EQZabModule` (strands numbered from `0`): `Z_{a,b} = OΛ_a ⊠ OΛ_b ⊆ OPol_{a+b}`
(`EQZab.osymAB`), the element `f(x) g(y)` standing for `(f ⊗ g) · z`, with differential
`dZ = d_α` (`α_i = {a}` on the `y`-variables, `0` on the `x`-variables) and right action of
`h ∈ OΛ_{a+b}` by right multiplication with `φ(h)` (`EQZab.phiAB`); `EQZab.tauAB` identifies this
model with Ellis–Qi's twisted one (`z · h = (θ ∘ w₀)(h) z`).

* `Zab a b`: `Z_{a,b}` as a dg abelian group (`DG` grading = half the `q`-degree), a sub-dg-group of
  `OPol_{a+b}(α)`; `Zab.instDGRightModule`: a right dg `OΛ_{a+b}`-module (Definition 4.6,
  `EQZab.dZ_mul_phiAB`), hence a left dg `OΛ_{a+b}ᵒᵖ`-module (`DG.DGRightModule.opModule`).
* `untwisted_mem_grading`: the untwisted odd Schur polynomial `s_λ` is homogeneous of degree `|λ|`.
* `zabFreeBasis`: the `s̃_μ(y) z` (`μ ∈ Par(b,a)`, degree `|μ|`) form a homogeneous basis of
  `Z_{a,b}` over `OΛ_{a+b}ᵒᵖ` (`EQZab.zab_span`, `EQZab.zab_indep`).
* By Lemma 4.7 (`EQZab.lemma_4_7_box`), `d(s̃_μ(y) z)` is a `ℤ`-combination of the `s̃_ν(y) z` with
  `|ν| = |μ| + 1`, so the basis ordered by decreasing `|μ|` is triangular.
* **Corollary 4.8** (`zabFiniteCellFiltration`): a `DG.FiniteCellFiltration` of `Z_{a,b}` over
  `OΛ_{a+b}ᵒᵖ` with `binom(a+b, a)` cells (`zabFiniteCellFiltration_length`); hence `Z_{a,b}` is
  K-projective and cofibrant as a right dg `OΛ_{a+b}`-module (`zab_isKProjective`,
  `zab_hasLiftingProperty`), for all `a, b`.
-/

universe w

open DirectSum

namespace OddMath.Frontier.EQFix

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential (OPol OPolAlpha osym osymDG mem_osymDG twistRev dAlpha indicator totalDeg
  grading parityInv theta longestPerm elementary)
open EQZab (osymAB inclX inclY dZ phiAB alphaAB)
open DG

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) eqFixZabCNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) eqFixZabCNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-- Associativity of the skew product (the pointwise `Finsupp` product is not used). -/
theorem sp_mul_assoc {m : ℕ} (x y z : SkewPolynomial m) : x * y * z = x * (y * z) :=
  @mul_assoc _ (@SemigroupWithZero.toSemigroup _ (@NonUnitalSemiring.toSemigroupWithZero _
    (@Semiring.toNonUnitalSemiring _ (OddMath.PbwL3.instSemiring m)))) x y z

theorem sp_zero_mul {m : ℕ} (x : SkewPolynomial m) : 0 * x = 0 :=
  @zero_mul _ (@MulZeroOneClass.toMulZeroClass _ (@MonoidWithZero.toMulZeroOneClass _
    (@Semiring.toMonoidWithZero _ (OddMath.PbwL3.instSemiring m)))) x

theorem sp_mul_zero {m : ℕ} (x : SkewPolynomial m) : x * 0 = 0 :=
  @mul_zero _ (@MulZeroOneClass.toMulZeroClass _ (@MonoidWithZero.toMulZeroOneClass _
    (@Semiring.toMonoidWithZero _ (OddMath.PbwL3.instSemiring m)))) x

/-! ## Homogeneity -/

section Grading

/-- A ring map `OPol_m → OPol_N` sending each generator to a homogeneous element of degree `1`
preserves the grading. -/
theorem ringHom_mem_grading' {m N : ℕ} (φ : SkewPolynomial m →+* SkewPolynomial N)
    (hφ : ∀ j, φ (generator j) ∈ grading N 1) {k : ℤ} {f : SkewPolynomial m}
    (hf : f ∈ grading m k) : φ f ∈ grading N k := by
  classical
  have hpow : ∀ (j : Fin m) (e : ℕ), φ (generator j ^ e) ∈ grading N e := by
    intro j e
    induction e with
    | zero => simpa using EQSkewDifferential.one_mem_grading'
    | succ e ih =>
      rw [pow_succ, map_mul]
      simpa using EQSkewDifferential.mul_mem_grading' ih (hφ j)
  have hprod : ∀ {r : ℕ} (v : Fin r → SkewPolynomial m) (e : Fin r → ℤ),
      (∀ i, φ (v i) ∈ grading N (e i)) → φ (List.ofFn v).prod ∈ grading N (∑ i, e i) := by
    intro r
    induction r with
    | zero => intro v e _; simpa using EQSkewDifferential.one_mem_grading'
    | succ r ih =>
      intro v e h
      rw [List.ofFn_succ, List.prod_cons, map_mul, Fin.sum_univ_succ]
      exact EQSkewDifferential.mul_mem_grading' (h 0) (ih _ _ fun i => h _)
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine AddSubgroup.sum_mem _ fun a ha => ?_
  have h := OddMath.Frontier.MonomialReversal.monomial_eq_smul_prod a (f a)
  change Finsupp.single a (f a) = _ at h
  rw [h, map_zsmul, ← hf a ha]
  exact AddSubgroup.zsmul_mem _ (hprod _ (fun j => (a j : ℤ)) fun j => hpow j (a j)) _

theorem pdegree_eq {N : ℕ} (a : Fin N → ℕ) : NilHeckeGradedEnd.pdegree a = 2 * totalDeg a := by
  rw [totalDeg_eq_sum]

/-- The grading by half the `q`-degree versus EKL's `q`-degree pieces. -/
theorem mem_grading_iff_piece {N : ℕ} {k : ℤ} {f : SkewPolynomial N} :
    f ∈ grading N k ↔ f ∈ NilHeckeGradedEnd.polynomialPiece N (2 * k) := by
  constructor
  · intro hf a ha
    by_contra h0
    have := hf a (Finsupp.mem_support_iff.mpr h0)
    rw [pdegree_eq, this] at ha
    exact ha rfl
  · intro hf a ha
    by_contra hne
    have := hf a (by rw [pdegree_eq]; omega)
    exact Finsupp.mem_support_iff.mp ha this

theorem theta_mem_grading {N : ℕ} {k : ℤ} {f : SkewPolynomial N} (hf : f ∈ grading N k) :
    theta N f ∈ grading N k :=
  EQSkewDifferential.ringHom_mem_grading (theta N) (fun j => by
    rw [EQSkewDifferential.theta_generator]
    exact AddSubgroup.zsmul_mem _ (EQSkewDifferential.generator_mem_grading j) _) hf

theorem longestPerm_mem_grading {N : ℕ} {k : ℤ} {f : SkewPolynomial N} (hf : f ∈ grading N k) :
    longestPerm N f ∈ grading N k :=
  EQSkewDifferential.ringHom_mem_grading (longestPerm N) (fun j => by
    rw [EQSkewDifferential.longestPerm_generator]
    exact EQSkewDifferential.generator_mem_grading _) hf

/-- The untwisted odd Schur polynomial `s_λ` (Ellis–Qi (3.24)) is homogeneous of degree `|λ|`
(`q`-degree `2|λ|`). -/
theorem untwisted_mem_grading (N : ℕ) (μ : Fin N → ℕ) :
    EQSchur.untwisted N μ ∈ grading N (totalDeg μ) := by
  have hst : LongestDivided.staircase N ∈ grading N (N.choose 2 : ℤ) :=
    mem_grading_iff_piece.mpr (NilHeckeGradedEnd.staircase_mem N)
  have hprod := EQSkewDifferential.mul_mem_grading' (theta_mem_grading hst)
    (theta_mem_grading (EQSkewDifferential.single_mem_grading μ 1))
  have hD := LongestFactor.D_mem N (mem_grading_iff_piece.mp hprod)
  rw [show 2 * ((N.choose 2 : ℤ) + totalDeg μ) - 2 * (N.choose 2 : ℤ) = 2 * totalDeg μ by ring]
    at hD
  exact longestPerm_mem_grading (theta_mem_grading (mem_grading_iff_piece.mpr hD))

variable {a b : ℕ}

theorem inclX_mem_grading {k : ℤ} {f : SkewPolynomial a} (hf : f ∈ grading a k) :
    inclX a b f ∈ grading (a+b) k :=
  ringHom_mem_grading' (inclX a b) (fun j => by
    rw [EQZab.inclX_generator]; exact EQSkewDifferential.generator_mem_grading _) hf

theorem inclY_mem_grading {k : ℤ} {f : SkewPolynomial b} (hf : f ∈ grading b k) :
    inclY a b f ∈ grading (a+b) k :=
  ringHom_mem_grading' (inclY a b) (fun j => by
    rw [EQZab.inclY_generator]; exact EQSkewDifferential.generator_mem_grading _) hf

theorem phiAB_mem_grading {k : ℤ} {f : SkewPolynomial (a+b)} (hf : f ∈ grading (a+b) k) :
    phiAB a b f ∈ grading (a+b) k := by
  unfold phiAB
  rw [RingHom.comp_apply]
  refine EQSkewDifferential.ringHom_mem_grading (EQZab.epsAB a b) (fun j => ?_)
    (longestPerm_mem_grading hf)
  rw [EQZab.epsAB, EQZab.diagHom]
  simp only [EQSkewDifferential.skewLift_generator]
  exact AddSubgroup.zsmul_mem _ (EQSkewDifferential.generator_mem_grading _) _

/-- `OΛ_a ⊠ OΛ_b` inside `OPol_{a+b}` (the dg ring). -/
def osymABOPol (a b : ℕ) : Subring (OPol (a+b)) :=
  (osymAB a b).map (OPol.equiv (a+b) : SkewPolynomial (a+b) →+* OPol (a+b))

theorem osymABOPol_isHomogeneous :
    SetLike.IsHomogeneous (DG.grading (M := OPol (a+b))) (osymABOPol a b) := by
  have h : osymABOPol a b = Subring.closure
      ((Set.range fun k => OPol.equiv (a+b) (inclX a b (elementary a k))) ∪
        Set.range fun k => OPol.equiv (a+b) (inclY a b (elementary b k))) := by
    rw [osymABOPol, EQZab.osymAB, RingHom.map_closure, Set.image_union, ← Set.range_comp,
      ← Set.range_comp]
    rfl
  rw [h]
  refine EQSkewDifferential.isHomogeneous_subringClosure _ ?_
  rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact ⟨k, inclX_mem_grading (EQSkewDifferential.elementary_mem_grading k)⟩
  · exact ⟨k, inclY_mem_grading (EQSkewDifferential.elementary_mem_grading k)⟩

end Grading

/-! ## `Z_{a,b}` as a right dg `OΛ_{a+b}`-module -/

variable {a b : ℕ}

/-- The set `S` with `𝟙_S = α` for the differential of `Z_{a,b}`: the `y`-strands if `a` is odd,
empty if `a` is even. -/
def sAB (a b : ℕ) : Finset (Fin (a+b)) :=
  if a % 2 = 1 then Finset.univ.filter fun i => a ≤ i.val else ∅

theorem indicator_sAB : indicator (sAB a b) = alphaAB a b := by
  funext i
  simp only [indicator, sAB, alphaAB, EQZab.par]
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · simp [h]
  · simp only [h, ite_true, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> simp

/-- `Z_{a,b} = OΛ_a ⊠ OΛ_b · z`. -/
def Zab (a b : ℕ) : Type := osymAB a b

namespace Zab

instance instAddCommGroup : AddCommGroup (Zab a b) := inferInstanceAs (AddCommGroup (osymAB a b))

/-- The underlying element of `OPol_{a+b}`. -/
def val (F : Zab a b) : SkewPolynomial (a+b) := Subtype.val (p := (· ∈ osymAB a b)) F

theorem mem (F : Zab a b) : F.val ∈ osymAB a b := Subtype.property (p := (· ∈ osymAB a b)) F

/-- An element of `OΛ_a ⊠ OΛ_b` as an element of `Z_{a,b}`. -/
def mk (f : SkewPolynomial (a+b)) (hf : f ∈ osymAB a b) : Zab a b := ⟨f, hf⟩

@[simp] theorem val_mk (f : SkewPolynomial (a+b)) (hf : f ∈ osymAB a b) : (mk f hf).val = f := rfl

@[ext] theorem ext {F G : Zab a b} (h : F.val = G.val) : F = G := Subtype.ext h

@[simp] theorem val_add (F G : Zab a b) : (F + G).val = F.val + G.val := rfl
@[simp] theorem val_zero : (0 : Zab a b).val = 0 := rfl
@[simp] theorem val_zsmul (k : ℤ) (F : Zab a b) : (k • F).val = k • F.val := rfl
@[simp] theorem val_sum {ι : Type*} (s : Finset ι) (F : ι → Zab a b) :
    (∑ i ∈ s, F i).val = ∑ i ∈ s, (F i).val :=
  map_sum (AddSubmonoidClass.subtype (osymAB a b)) F s

/-- The embedding into `OPol_{a+b}(α)`. -/
def ι (a b : ℕ) : Zab a b →+ OPolAlpha (a+b) (sAB a b) where
  toFun F := OPolAlpha.equiv _ _ F.val
  map_zero' := rfl
  map_add' _ _ := rfl

theorem ι_injective : Function.Injective (ι a b) := fun _ _ h => Subtype.ext h

/-- The differential `dZ` of `Z_{a,b}`. -/
def dHom (a b : ℕ) : Zab a b →+ Zab a b where
  toFun F := mk (dZ a b F.val) (EQZab.dZ_mem F.mem)
  map_zero' := by apply ext; exact map_zero (dZ a b)
  map_add' F G := by apply ext; exact map_add (dZ a b) F.val G.val

theorem ι_dHom (F : Zab a b) : ι a b (dHom a b F) = DG.d (ι a b F) := by
  change OPolAlpha.equiv _ _ (dZ a b F.val) = DG.d (OPolAlpha.equiv _ _ F.val)
  rw [OPolAlpha.d_equiv, indicator_sAB]

theorem ι_decompose (n : ℤ) (F : Zab a b) :
    (decompose (DG.grading (M := OPolAlpha (a+b) (sAB a b))) (ι a b F) n :
      OPolAlpha (a+b) (sAB a b)) ∈ (ι a b).range := by
  have h := osymABOPol_isHomogeneous (a := a) (b := b) n
    (show OPol.equiv (a+b) F.val ∈ osymABOPol a b from ⟨F.val, F.mem, rfl⟩)
  obtain ⟨f, hf, hfe⟩ := h
  exact ⟨mk f hf, hfe⟩

/-- `Z_{a,b}` as a dg abelian group: graded by half the `q`-degree, with differential `dZ`. -/
noncomputable instance instDGAddCommGroup : DGAddCommGroup (Zab a b) :=
  DGAddCommGroup.ofInjective (ι a b) ι_injective (dHom a b) ι_dHom ι_decompose

theorem mem_grading_iff {k : ℤ} {F : Zab a b} : F ∈ DG.grading k ↔ F.val ∈ grading (a+b) k :=
  DG.mem_gradingComap (ι a b)

theorem val_d (F : Zab a b) : (DG.d F).val = dZ a b F.val := rfl

/-- The right action of `OΛ_{a+b}`: `F z · h = F φ(h) z`. -/
def rsmul (c : osymDG (a+b)) (F : Zab a b) : Zab a b :=
  mk (F.val * phiAB a b (toSkew c)) (mul_mem F.mem (EQZab.phiAB_mem (toSkew_mem c)))

@[simp] theorem val_rsmul (c : osymDG (a+b)) (F : Zab a b) :
    (rsmul c F).val = F.val * phiAB a b (toSkew c) := rfl

theorem toSkew_mul (c c' : osymDG (a+b)) : toSkew (c * c') = toSkew c * toSkew c' := rfl
theorem toSkew_one : toSkew (1 : osymDG (a+b)) = 1 := rfl
theorem toSkew_add (c c' : osymDG (a+b)) : toSkew (c + c') = toSkew c + toSkew c' := rfl
theorem toSkew_zero : toSkew (0 : osymDG (a+b)) = 0 := rfl

instance instModuleOp : Module (osymDG (a+b))ᵐᵒᵖ (Zab a b) where
  smul c F := rsmul c.unop F
  one_smul F := by
    apply ext; change F.val * phiAB a b (toSkew 1) = F.val
    rw [toSkew_one, map_one, mul_one]
  mul_smul c c' F := by
    apply ext; change F.val * phiAB a b (toSkew (c * c').unop) =
      F.val * phiAB a b (toSkew c'.unop) * phiAB a b (toSkew c.unop)
    rw [MulOpposite.unop_mul, toSkew_mul, map_mul]; exact (sp_mul_assoc _ _ _).symm
  smul_zero c := by apply ext; change (0 : SkewPolynomial (a+b)) * _ = 0; exact sp_zero_mul _
  smul_add c F G := by apply ext; change (F.val + G.val) * _ = F.val * _ + G.val * _; rw [add_mul]
  add_smul c c' F := by
    apply ext; change F.val * phiAB a b (toSkew (c + c').unop) =
      F.val * phiAB a b (toSkew c.unop) + F.val * phiAB a b (toSkew c'.unop)
    rw [MulOpposite.unop_add, toSkew_add, map_add, mul_add]
  zero_smul F := by
    apply ext; change F.val * phiAB a b (toSkew (0 : (osymDG (a+b))ᵐᵒᵖ).unop) = 0
    rw [MulOpposite.unop_zero, toSkew_zero, map_zero]; exact sp_mul_zero _

theorem val_op_smul (c : osymDG (a+b)) (F : Zab a b) :
    (MulOpposite.op c • F).val = F.val * phiAB a b (toSkew c) := rfl

theorem toSkew_mem_grading {i : ℤ} {c : osymDG (a+b)} (hc : c ∈ DG.grading i) :
    toSkew c ∈ grading (a+b) i := hc

theorem toSkew_d (c : osymDG (a+b)) : toSkew (DG.d c) = EQSkewDifferential.d (a+b) (toSkew c) :=
  rfl

/-- **Ellis–Qi, Definition 4.6**: `Z_{a,b}` is a right dg `OΛ_{a+b}`-module. -/
instance instDGRightModule : DGRightModule (osymDG (a+b)) (Zab a b) where
  op_smul_mem' {i j c m} hc hm := by
    rw [mem_grading_iff, val_op_smul]
    exact EQSkewDifferential.mul_mem_grading' (mem_grading_iff.mp hm)
      (phiAB_mem_grading (toSkew_mem_grading hc))
  d_op_smul' {j m} hm c := by
    apply ext
    simp only [val_d, val_op_smul, val_add, Units.smul_def, val_zsmul]
    rw [EQZab.dZ_mul_phiAB, EQSkewDifferential.parityInv_of_mem (mem_grading_iff.mp hm), toSkew_d,
      smul_mul_assoc]

end Zab

/-! ## The finite-cell filtration (Corollary 4.8) -/

/-- The left `OΛ_{a+b}ᵒᵖ`-module structure of the right dg `OΛ_{a+b}`-module `Z_{a,b}`. -/
abbrev zabOpModule (a b : ℕ) : Module (OsymOp (a+b)) (Zab a b) := DGRightModule.opModule ℤ

attribute [local instance] zabOpModule

/-- `Z_{a,b}` is a left dg `OΛ_{a+b}ᵒᵖ`-module. -/
theorem zabOpDGModule (a b : ℕ) : DGModule (OsymOp (a+b)) (Zab a b) :=
  DGRightModule.dgModule_opModule ℤ

attribute [local instance] zabOpDGModule

theorem zab_op_smul_of_mem {k : ℤ} {m : Zab a b} (hm : m ∈ DG.grading k) (x : OsymOp (a+b)) :
    x • m = MulOpposite.op (Shift.twist (osymDG (a+b)) k (unopO (a+b) x)) • m := by
  induction x using DG.induction_on with
  | h_zero => rw [zero_smul, map_zero, map_zero, MulOpposite.op_zero, zero_smul]
  | h_homogeneous x =>
    rename_i i
    have hx : unopO (a+b) x ∈ DG.grading (M := osymDG (a+b)) i :=
      (GradedOpposite.mem_dgGrading_iff (R := ℤ)).mp x.2
    have h := DGRightModule.opModule_op_smul_of_mem ℤ (M := Zab a b) hx hm
    rw [GradedOpposite.op_unop] at h
    rw [h, Shift.twist_of_mem hx, mul_comm, Units.smul_def, Units.smul_def, MulOpposite.op_smul,
      smul_assoc]
  | h_add x y hx hy => rw [add_smul, hx, hy, map_add, map_add, MulOpposite.op_add, add_smul]

/-- The index set `Par(b,a)` of the cells. -/
abbrev ParIdx (a b : ℕ) : Type := ↥(BoxPartitionCount.box b a)

/-- The basis element `s̃_μ(y) z` (represented by `s_μ(y)`). -/
def zabB (μ : ParIdx a b) : Zab a b :=
  Zab.mk (inclY a b (EQSchur.untwisted b μ.1))
    (EQZab.inclY_mem (EQZab.untwisted_mem_osym μ.1))

theorem zabB_mem (μ : ParIdx a b) : zabB μ ∈ DG.grading (M := Zab a b) (totalDeg μ.1) :=
  Zab.mem_grading_iff.mpr (inclY_mem_grading (untwisted_mem_grading b μ.1))

/-- Uniqueness of coefficients in the basis `{s̃_μ(y) z}` (`EQZab.zab_indep`). -/
theorem zab_coeff_unique (c₁ c₂ : ParIdx a b → osym (a+b))
    (h : ∑ μ, inclY a b (EQSchur.untwisted b μ.1) * phiAB a b (c₁ μ) =
      ∑ μ, inclY a b (EQSchur.untwisted b μ.1) * phiAB a b (c₂ μ)) : c₁ = c₂ := by
  classical
  let g : (Fin b → ℕ) → SkewPolynomial (a+b) := fun μ =>
    if hμ : μ ∈ BoxPartitionCount.box b a then
      (c₁ ⟨μ, hμ⟩ : SkewPolynomial (a+b)) - c₂ ⟨μ, hμ⟩ else 0
  have hg : ∀ μ, g μ ∈ osym (a+b) := fun μ => by
    simp only [g]
    split_ifs
    · exact sub_mem (c₁ _).2 (c₂ _).2
    · exact zero_mem _
  have h0 : ∑ μ ∈ BoxPartitionCount.box b a,
      inclY a b (EQSchur.untwisted b μ) * phiAB a b (g μ) = 0 := by
    rw [← Finset.sum_coe_sort]
    simp only [g, Finset.coe_mem, dite_true, map_sub, mul_sub, Finset.sum_sub_distrib]
    rw [h, sub_self]
  have hz := EQZab.zab_indep g hg h0
  funext μ
  have := hz μ.1 μ.2
  simp only [g, μ.2, dite_true, sub_eq_zero] at this
  exact Subtype.ext this

/-- The coefficients `c_μ ∈ OΛ_{a+b}` of `F = Σ_μ s̃_μ(y) z · c_μ` (`EQZab.zab_span`). -/
def zabC (F : Zab a b) : ParIdx a b → osym (a+b) :=
  fun μ => ⟨(EQZab.zab_span F.mem).choose μ.1, (EQZab.zab_span F.mem).choose_spec.1 μ.1⟩

theorem zabC_spec (F : Zab a b) :
    F.val = ∑ μ, inclY a b (EQSchur.untwisted b μ.1) * phiAB a b (zabC F μ) := by
  rw [(EQZab.zab_span F.mem).choose_spec.2, ← Finset.sum_coe_sort]
  rfl

/-- The coefficient of `s̃_μ(y) z` for the action of `OΛ_{a+b}ᵒᵖ`: `op (ι^{|μ|}(c_μ))`. -/
def zabCoeff (F : Zab a b) (μ : ParIdx a b) : OsymOp (a+b) :=
  opO (a+b) (Shift.twist (osymDG (a+b)) (totalDeg μ.1) (ofOsym (zabC F μ)))

theorem val_smul_zabB (x : OsymOp (a+b)) (μ : ParIdx a b) :
    (x • zabB μ).val = inclY a b (EQSchur.untwisted b μ.1) *
      phiAB a b (toSkew (Shift.twist (osymDG (a+b)) (totalDeg μ.1) (unopO (a+b) x))) := by
  rw [zab_op_smul_of_mem (zabB_mem μ), Zab.val_op_smul]
  rfl

/-- **Ellis–Qi, Corollary 4.8** (basis): the `s̃_μ(y) z`, `μ ∈ Par(b,a)`, of degree `|μ|`, form a
homogeneous basis of `Z_{a,b}` over `OΛ_{a+b}ᵒᵖ`. -/
def zabFreeBasis (a b : ℕ) : FreeBasis (OsymOp (a+b)) (Zab a b) (ParIdx a b) where
  b := zabB
  deg μ := totalDeg μ.1
  b_mem := zabB_mem
  coeff := zabCoeff
  sum_coeff F := by
    apply Zab.ext
    rw [Zab.val_sum, zabC_spec F]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [val_smul_zabB, zabCoeff, GradedOpposite.unop_op, Shift.twist_twist_self]
    rfl
  coeff_sum x := by
    set y := ∑ μ, x μ • zabB μ
    have hy : y.val = ∑ μ, inclY a b (EQSchur.untwisted b μ.1) *
        phiAB a b ((⟨toSkew (Shift.twist (osymDG (a+b)) (totalDeg μ.1) (unopO (a+b) (x μ))),
          toSkew_mem _⟩ : osym (a+b)) : SkewPolynomial (a+b)) := by
      rw [Zab.val_sum]
      exact Finset.sum_congr rfl fun μ _ => val_smul_zabB (x μ) μ
    have hc := zab_coeff_unique _ _ ((zabC_spec y).symm.trans hy)
    funext μ
    rw [zabCoeff, hc, ofOsym_toSkew, Shift.twist_twist_self, GradedOpposite.op_unop]

/-- `span_ℤ {s̃_ν(y) z : ν ∈ Par(b,a), |ν| = m}`. -/
def levelSpan (a b m : ℕ) : Submodule ℤ (SkewPolynomial (a+b)) :=
  Submodule.span ℤ {F | ∃ ν ∈ BoxPartitionCount.box b a, EQZab.weight ν = m ∧
    F = inclY a b (EQSchur.untwisted b ν)}

theorem levelSpan_le_osymAB (m : ℕ) {F : SkewPolynomial (a+b)} (hF : F ∈ levelSpan a b m) :
    F ∈ osymAB a b := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, _, _, rfl⟩ := hx
    exact EQZab.inclY_mem (EQZab.untwisted_mem_osym ν)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul k x _ hx => exact Subring.zsmul_mem _ hx k

/-- Coefficients of elements of `levelSpan a b m` vanish off `|ν| = m`. -/
theorem coeff_levelSpan {m : ℕ} {F : SkewPolynomial (a+b)} (hF : F ∈ levelSpan a b m)
    (ν : ParIdx a b) (hν : EQZab.weight ν.1 ≠ m) :
    (zabFreeBasis a b).coeff (Zab.mk F (levelSpan_le_osymAB m hF)) ν = 0 := by
  classical
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν', hν', hw, rfl⟩ := hx
    have h1 : Zab.mk (inclY a b (EQSchur.untwisted b ν')) (levelSpan_le_osymAB m
        (Submodule.subset_span ⟨ν', hν', hw, rfl⟩)) = (1 : OsymOp (a+b)) •
        (zabFreeBasis a b).b ⟨ν', hν'⟩ := by
      rw [one_smul]; rfl
    rw [h1, FreeBasis.coeff_basis, Pi.single_eq_of_ne]
    rintro rfl
    exact hν hw
  | zero =>
    have h0 : Zab.mk (0 : SkewPolynomial (a+b)) (levelSpan_le_osymAB m (zero_mem _)) = 0 := rfl
    rw [h0, FreeBasis.coeff_zero, Pi.zero_apply]
  | add x y hx' hy' hx hy =>
    have h0 : Zab.mk (x + y) (levelSpan_le_osymAB m (add_mem hx' hy')) =
        Zab.mk x (levelSpan_le_osymAB m hx') + Zab.mk y (levelSpan_le_osymAB m hy') := rfl
    rw [h0, FreeBasis.coeff_add, Pi.add_apply, hx, hy, add_zero]
  | smul k x hx' hx =>
    have h0 : Zab.mk (k • x) (levelSpan_le_osymAB m (Submodule.smul_mem _ k hx')) =
        k • Zab.mk x (levelSpan_le_osymAB m hx') := rfl
    rw [h0, FreeBasis.coeff_zsmul, Pi.smul_apply, hx, smul_zero]

/-- **Ellis–Qi, Lemma 4.7**: `d(s̃_μ(y) z)` is a `ℤ`-combination of the `s̃_ν(y) z`, `ν ∈ Par(b,a)`,
with `|ν| = |μ| + 1`. -/
theorem dZ_mem_levelSpan (μ : ParIdx a b) :
    dZ a b (inclY a b (EQSchur.untwisted b μ.1)) ∈ levelSpan a b (EQZab.weight μ.1 + 1) := by
  classical
  have hμ := BoxPartitionCount.mem_box.mp μ.2
  rw [EQZab.lemma_4_7_box μ.1 hμ.1 hμ.2]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ.1 + expSingle i,
      BoxPartitionCount.mem_box.mpr ⟨h.1, EQZab.add_box_mem hμ.2 h⟩,
      EQZab.weight_add_expSingle μ.1 i, rfl⟩)
  · exact Submodule.zero_mem _

/-- The key `-|μ|` strictly decreases along the differential. -/
theorem zab_key (μ ν : ParIdx a b)
    (h : (zabFreeBasis a b).coeff (DG.d ((zabFreeBasis a b).b μ)) ν ≠ 0) :
    -totalDeg ν.1 < -totalDeg μ.1 := by
  by_contra hlt
  apply h
  have hd : DG.d ((zabFreeBasis a b).b μ) =
      Zab.mk (dZ a b (inclY a b (EQSchur.untwisted b μ.1)))
        (levelSpan_le_osymAB _ (dZ_mem_levelSpan μ)) := rfl
  rw [hd]
  refine coeff_levelSpan (dZ_mem_levelSpan μ) ν fun hw => hlt ?_
  rw [totalDeg_eq_sum, totalDeg_eq_sum]
  have hw' : ∑ i, ν.1 i = ∑ i, μ.1 i + 1 := hw
  rw [hw']
  push_cast
  omega

/-- The triangular basis of `Z_{a,b}`: the `s̃_μ(y) z` ordered by decreasing `|μ|`. -/
def zabTriangular (a b : ℕ) : TriangularBasis (OsymOp (a+b)) (Zab a b) :=
  (zabFreeBasis a b).toTriangular (fun μ => -totalDeg μ.1) zab_key

/-- **Ellis–Qi, Corollary 4.8**: `Z_{a,b}` is a finite-cell right dg module over `OΛ_{a+b}`
(a finite-cell left dg `OΛ_{a+b}ᵒᵖ`-module), for all `a, b`, with cells `OΛ_{a+b}ᵒᵖ⟦-|μ|⟧`,
`μ ∈ Par(b,a)`, attached in order of decreasing `|μ|`. -/
def zabFiniteCellFiltration (a b : ℕ) : FiniteCellFiltration (OsymOp (a+b)) (Zab a b) :=
  (zabTriangular a b).finiteCellFiltration

/-- The filtration of Corollary 4.8 has `binom(a+b, a)` cells. -/
theorem zabFiniteCellFiltration_length :
    (zabFiniteCellFiltration a b).length = (b + a).choose b := by
  change Fintype.card (ParIdx a b) = _
  rw [Fintype.card_coe, BoxPartitionCount.card_box]

/-- **Ellis–Qi, Corollary 4.8** ("finite-cell, and thus cofibrant"): `Z_{a,b}` is K-projective
as a right dg `OΛ_{a+b}`-module. -/
theorem zab_isKProjective : IsKProjective.{w} (OsymOp (a+b)) (Zab a b) :=
  (zabTriangular a b).isKProjective

/-- **Ellis–Qi, Corollary 4.8**: `Z_{a,b}` is cofibrant as a right dg `OΛ_{a+b}`-module (lifting
property against surjective quasi-isomorphisms). -/
theorem zab_hasLiftingProperty : HasLiftingProperty.{w} (OsymOp (a+b)) (Zab a b) :=
  (zabTriangular a b).hasLiftingProperty

end

end OddMath.Frontier.EQFix
