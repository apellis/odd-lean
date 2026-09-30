import OddMath.Frontier.EQOddDerivatives
import DG.Module.Right
import DG.Algebra.Constructions

/-!
# `OPol_n`, `OΛ_n`, `OPol_n(α)` and `Z_n` as dg objects

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.2 (conventions (2.3)–(2.5)), §3.1–§3.2 (Proposition 3.1, Lemma 3.2, Proposition 3.7,
Definition 3.8).

This file packages the constructions of `OddMath.Frontier.EQSkewDifferential` with the dg
structures of the `DG` library (`DG.DGAddCommGroup`, `DG.DGRing`, `DG.DGModule`,
`DG.DGRightModule`, `DG.DGBimodule`, `DG.DGSubring`).

## Gradings

Ellis–Qi grade `OPol_n` by `q`-degree (`deg x_i = 2`) and parity (`x_i` odd), with `d` of
bidegree `(2, 1̄)`. On all objects of this file the parity is the `q`-degree divided by `2`, taken
mod `2`. The `DG` library uses cohomological `ℤ`-gradings with `d` of degree `+1` and the Koszul
sign `(-1)^{deg}`; the grading used here is therefore **half the `q`-degree**: `x_i` has degree
`1`, and the Koszul sign of a homogeneous element is its Ellis–Qi parity sign
(`parityInv_of_mem`: `ι` acts on the degree-`k` part by `(-1)^k`).

## Contents

* `grading n k`: the homogeneous polynomials of total degree `k`, an internal direct sum
  decomposition of `SkewPolynomial n` (`decomposition`) preserved by `d` (`d_mem_grading`), `ι`
  and `θ ∘ w₀`;
* `OPol n`: `OPol_n` (a type synonym of `SkewPolynomial n`, identified with it by the ring
  isomorphism `OPol.equiv`), with `d(x_i) = x_i²`: a dg ring (`DG.DGRing`), hence a dg
  `ℤ`-algebra (`OPol.dgAlgebra_int`);
* `osymDG n`: `OΛ_n` as a dg subring (Lemma 3.2);
* `OPolAlpha n S`: for `S ⊆ {0, …, n-1}`, the left dg `OPol_n`-module `OPol_n(α)` with
  `α = 𝟙_S ∈ {0,1}ⁿ` (Proposition 3.1);
* `Zn n`: the dg `(OPol_n, OPol_n)`-bimodule `Z_n = OPol_n(0,1,0,1,…)` with the right action
  `1_z f = (θ ∘ w₀)(f) 1_z` (Proposition 3.7, Definition 3.8); its underlying left dg module is
  `OPolAlpha n (oddStrands n)` and `indicator (oddStrands n) = zAlpha n`. Ellis–Qi's `Z_n` is its
  restriction to `OΛ_n` on the right (`Zn.dgBimoduleOsym`).
-/

namespace OddMath.Frontier.EQSkewDifferential

open OddMath.SkewPolynomial (SkewPolynomial generator)
open DG (DGAddCommGroup DGRing DGAlgebra DGModule DGRightModule DGBimodule DGSubring koszulSign)
open DirectSum
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) opolNUNASemiring'' (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) opolNUNARing'' (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {n : ℕ}

/-! ## The grading by total degree -/

/-- The total degree `Σ a_i` of an exponent vector. -/
def totalDeg (a : Fin n → ℕ) : ℤ := ∑ i, (a i : ℤ)

theorem totalDeg_add (a b : Fin n → ℕ) : totalDeg (a + b) = totalDeg a + totalDeg b := by
  simp [totalDeg, Finset.sum_add_distrib]

/-- The homogeneous polynomials of total degree `k` (half the Ellis–Qi `q`-degree). -/
def grading (n : ℕ) (k : ℤ) : AddSubgroup (SkewPolynomial n) where
  carrier := {f | ∀ a ∈ f.support, totalDeg a = k}
  zero_mem' := by simp
  add_mem' {f g} hf hg a ha := by
    classical
    rcases Finset.mem_union.mp (Finsupp.support_add ha) with h | h
    · exact hf a h
    · exact hg a h
  neg_mem' {f} hf a ha := hf a (by simpa using ha)

theorem mem_grading {k : ℤ} {f : SkewPolynomial n} :
    f ∈ grading n k ↔ ∀ a ∈ f.support, totalDeg a = k := Iff.rfl

theorem single_mem_grading (a : Fin n → ℕ) (c : ℤ) :
    Finsupp.single a c ∈ grading n (totalDeg a) := by
  classical
  intro b hb
  rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hb
  split_ifs at hb with h
  · rw [h]
  · exact absurd rfl hb

/-- The homogeneous component map of a single term. -/
def singleHom (a : Fin n → ℕ) : ℤ →+ grading n (totalDeg a) where
  toFun c := ⟨Finsupp.single a c, single_mem_grading a c⟩
  map_zero' := by ext1; simp
  map_add' c c' := by ext1; simp

/-- The decomposition of `OPol_n` by total degree. -/
def decomposeHom (n : ℕ) : SkewPolynomial n →+ ⨁ k, grading n k :=
  Finsupp.liftAddHom fun a => (DirectSum.of (fun k => grading n k) (totalDeg a)).comp (singleHom a)

theorem decomposeHom_single (a : Fin n → ℕ) (c : ℤ) :
    decomposeHom n (Finsupp.single a c) =
      DirectSum.of (fun k => grading n k) (totalDeg a) ⟨Finsupp.single a c, single_mem_grading a c⟩ := by
  rw [decomposeHom, Finsupp.liftAddHom_apply_single]
  rfl

theorem decomposeHom_single_of_eq {k : ℤ} (a : Fin n → ℕ) (c : ℤ) (h : totalDeg a = k) :
    decomposeHom n (Finsupp.single a c) =
      DirectSum.of (fun k => grading n k) k ⟨Finsupp.single a c, h ▸ single_mem_grading a c⟩ := by
  subst h
  exact decomposeHom_single a c

theorem decomposeHom_eq_of {k : ℤ} (f : SkewPolynomial n) (hf : f ∈ grading n k) :
    decomposeHom n f = DirectSum.of (fun k => grading n k) k ⟨f, hf⟩ := by
  classical
  induction f using Finsupp.induction with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | single_add a b f ha hb ih =>
    have hsupp := Finsupp.support_single_add ha hb
    have h1 : totalDeg a = k := hf a (by rw [hsupp]; exact Finset.mem_cons_self a _)
    have h2 : f ∈ grading n k := fun c hc => hf c (by rw [hsupp]; exact Finset.mem_cons_of_mem hc)
    rw [map_add, ih h2, decomposeHom_single_of_eq a b h1, ← map_add]
    rfl

instance decomposition (n : ℕ) : Decomposition (grading n) where
  decompose' := decomposeHom n
  left_inv f := by
    induction f using Finsupp.induction_linear with
    | zero => rw [map_zero, map_zero]
    | add f g hf hg => rw [map_add, map_add, hf, hg]
    | single a c => rw [decomposeHom_single, coeAddMonoidHom_of]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of k y => rw [coeAddMonoidHom_of, decomposeHom_eq_of y.1 y.2]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ## Homogeneity of the operations -/

/-- The skew product of homogeneous polynomials is homogeneous. -/
theorem mul_mem_grading' {i j : ℤ} {f g : SkewPolynomial n} (hf : f ∈ grading n i)
    (hg : g ∈ grading n j) : f * g ∈ grading n (i + j) := by
  show OddMath.SkewPolynomial.mul f g ∈ grading n (i + j)
  simp only [OddMath.SkewPolynomial.mul, Finsupp.sum]
  refine AddSubgroup.sum_mem _ fun a ha => AddSubgroup.sum_mem _ fun b hb => ?_
  have := single_mem_grading (a + b) (f a * g b * OddMath.skewSign a b)
  rwa [totalDeg_add, hf a ha, hg b hb] at this

theorem one_mem_grading' : (1 : SkewPolynomial n) ∈ grading n 0 := by
  have h := single_mem_grading (0 : Fin n → ℕ) 1
  have h0 : totalDeg (0 : Fin n → ℕ) = 0 := by simp [totalDeg]
  rw [h0] at h
  exact h

theorem generator_mem_grading (j : Fin n) : generator j ∈ grading n 1 := by
  have h := single_mem_grading (OddMath.SkewPolynomial.expSingle j) 1
  have h1 : totalDeg (OddMath.SkewPolynomial.expSingle j) = 1 := by
    simp [totalDeg, OddMath.SkewPolynomial.expSingle]
  rw [h1] at h
  exact h

/-- A homogeneous polynomial of degree `k` whose differential is homogeneous of degree `k + 1`
and on which `ι` acts by `(-1)^k`. -/
def IsDHom (f : SkewPolynomial n) (k : ℤ) : Prop :=
  f ∈ grading n k ∧ d n f ∈ grading n (k + 1) ∧ parityInv n f = (koszulSign k : ℤ) • f

theorem isDHom_zero (k : ℤ) : IsDHom (0 : SkewPolynomial n) k :=
  ⟨zero_mem _, by simp, by simp⟩

theorem isDHom_one : IsDHom (1 : SkewPolynomial n) 0 :=
  ⟨one_mem_grading', by simp, by simp⟩

theorem isDHom_generator (j : Fin n) : IsDHom (generator j) 1 := by
  refine ⟨generator_mem_grading j, ?_, ?_⟩
  · rw [d_generator]; exact mul_mem_grading' (generator_mem_grading j) (generator_mem_grading j)
  · rw [parityInv_generator, DG.koszulSign_odd odd_one]; simp

theorem IsDHom.add {f g : SkewPolynomial n} {k : ℤ} (hf : IsDHom f k) (hg : IsDHom g k) :
    IsDHom (f + g) k :=
  ⟨add_mem hf.1 hg.1, by rw [map_add]; exact add_mem hf.2.1 hg.2.1,
    by rw [map_add, hf.2.2, hg.2.2, smul_add]⟩

theorem IsDHom.zsmul {f : SkewPolynomial n} {k : ℤ} (hf : IsDHom f k) (c : ℤ) :
    IsDHom (c • f) k :=
  ⟨AddSubgroup.zsmul_mem _ hf.1 c, by rw [map_zsmul]; exact AddSubgroup.zsmul_mem _ hf.2.1 c,
    by rw [map_zsmul, hf.2.2, smul_comm]⟩

theorem IsDHom.mul {f g : SkewPolynomial n} {i j : ℤ} (hf : IsDHom f i) (hg : IsDHom g j) :
    IsDHom (f * g) (i + j) := by
  refine ⟨mul_mem_grading' hf.1 hg.1, ?_, ?_⟩
  · rw [d_mul, hf.2.2]
    refine add_mem ?_ ?_
    · have := mul_mem_grading' hf.2.1 hg.1
      rwa [show i + 1 + j = i + j + 1 by ring] at this
    · rw [smul_mul_assoc]
      refine AddSubgroup.zsmul_mem _ ?_ _
      have := mul_mem_grading' hf.1 hg.2.1
      rwa [← add_assoc] at this
  · rw [map_mul, hf.2.2, hg.2.2, smul_mul_assoc, mul_smul_comm, smul_smul, DG.koszulSign_add,
      Units.val_mul, mul_comm]

theorem isDHom_pow (j : Fin n) : ∀ m : ℕ, IsDHom (generator j ^ m) (m : ℤ)
  | 0 => by simpa using isDHom_one
  | m + 1 => by
    rw [pow_succ]
    have := (isDHom_pow j m).mul (isDHom_generator j)
    simpa using this

theorem isDHom_ofFn_prod : ∀ {m : ℕ} (v : Fin m → SkewPolynomial n) (e : Fin m → ℤ),
    (∀ i, IsDHom (v i) (e i)) → IsDHom (List.ofFn v).prod (∑ i, e i)
  | 0, v, e, _ => by simpa using isDHom_one
  | m + 1, v, e, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact (h 0).mul (isDHom_ofFn_prod (fun i => v i.succ) (fun i => e i.succ) fun i => h _)

theorem isDHom_single (a : Fin n → ℕ) (c : ℤ) : IsDHom (Finsupp.single a c) (totalDeg a) := by
  have h := OddMath.Frontier.MonomialReversal.monomial_eq_smul_prod a c
  change Finsupp.single a c = _ at h
  rw [h]
  exact (isDHom_ofFn_prod _ (fun j => (a j : ℤ)) fun j => isDHom_pow j (a j)).zsmul c

theorem isDHom_of_mem {k : ℤ} {f : SkewPolynomial n} (hf : f ∈ grading n k) : IsDHom f k := by
  classical
  rw [← Finsupp.sum_single f, Finsupp.sum]
  refine Finset.sum_induction _ (fun g => IsDHom g k) (fun _ _ h h' => h.add h')
    (isDHom_zero k) fun a ha => ?_
  have := isDHom_single a (f a)
  rwa [hf a ha] at this

/-- `d` has degree `+1`: it maps `q`-degree `2k` to `q`-degree `2k + 2`. -/
theorem d_mem_grading {k : ℤ} {f : SkewPolynomial n} (hf : f ∈ grading n k) :
    d n f ∈ grading n (k + 1) :=
  (isDHom_of_mem hf).2.1

/-- The parity involution `ι` acts on the degree-`k` part by the Koszul sign `(-1)^k`: the
parity of Ellis–Qi is half the `q`-degree mod `2`. -/
theorem parityInv_of_mem {k : ℤ} {f : SkewPolynomial n} (hf : f ∈ grading n k) :
    parityInv n f = (koszulSign k : ℤ) • f :=
  (isDHom_of_mem hf).2.2

/-- A ring endomorphism sending each generator to a homogeneous element of degree `1` preserves
the grading. -/
theorem ringHom_mem_grading (φ : SkewPolynomial n →+* SkewPolynomial n)
    (hφ : ∀ j, φ (generator j) ∈ grading n 1) {k : ℤ} {f : SkewPolynomial n}
    (hf : f ∈ grading n k) : φ f ∈ grading n k := by
  classical
  have hpow : ∀ (j : Fin n) (m : ℕ), φ (generator j ^ m) ∈ grading n m := by
    intro j m
    induction m with
    | zero => simpa using one_mem_grading'
    | succ m ih =>
      rw [pow_succ, map_mul]
      simpa using mul_mem_grading' ih (hφ j)
  have hprod : ∀ {m : ℕ} (v : Fin m → SkewPolynomial n) (e : Fin m → ℤ),
      (∀ i, φ (v i) ∈ grading n (e i)) → φ (List.ofFn v).prod ∈ grading n (∑ i, e i) := by
    intro m
    induction m with
    | zero => intro v e _; simpa using one_mem_grading'
    | succ m ih =>
      intro v e h
      rw [List.ofFn_succ, List.prod_cons, map_mul, Fin.sum_univ_succ]
      exact mul_mem_grading' (h 0) (ih _ _ fun i => h _)
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine AddSubgroup.sum_mem _ fun a ha => ?_
  have h := OddMath.Frontier.MonomialReversal.monomial_eq_smul_prod a (f a)
  change Finsupp.single a (f a) = _ at h
  rw [h, map_zsmul, ← hf a ha]
  exact AddSubgroup.zsmul_mem _ (hprod _ (fun j => (a j : ℤ)) fun j => hpow j (a j)) _

theorem twistRev_mem_grading {k : ℤ} {f : SkewPolynomial n} (hf : f ∈ grading n k) :
    twistRev n f ∈ grading n k :=
  ringHom_mem_grading (twistRev n)
    (fun j => by rw [twistRev_generator]; exact AddSubgroup.zsmul_mem _ (generator_mem_grading _) _)
    hf

theorem parityInv_mem_grading {k : ℤ} {f : SkewPolynomial n} (hf : f ∈ grading n k) :
    parityInv n f ∈ grading n k := by
  rw [parityInv_of_mem hf]
  exact AddSubgroup.zsmul_mem _ hf _

/-! ## `OPol_n` as a dg ring -/

/-- `OPol_n` as a dg ring: graded by total degree (half the `q`-degree), with `d(x_i) = x_i²`.
It is a type synonym of `SkewPolynomial n`, carrying only the skew ring structure. -/
def OPol (n : ℕ) : Type := SkewPolynomial n

namespace OPol

instance instRing : Ring (OPol n) := OddMath.PbwL3.instRing n

/-- The identification of `OPol n` with the skew-polynomial model. -/
def equiv (n : ℕ) : SkewPolynomial n ≃+* OPol n := RingEquiv.refl _

/-- The generator `x_i` of `OPol_n`. -/
def x (i : Fin n) : OPol n := equiv n (generator i)

instance instDGAddCommGroup : DGAddCommGroup (OPol n) where
  grading := grading n
  decomposition := decomposition n
  d := d n
  d_mem' hm := d_mem_grading hm
  d_d' := d_d

theorem mem_grading_iff {k : ℤ} {f : OPol n} :
    f ∈ DG.grading k ↔ (equiv n).symm f ∈ grading n k := Iff.rfl

theorem equiv_mem_grading_iff {k : ℤ} {f : SkewPolynomial n} :
    equiv n f ∈ DG.grading k ↔ f ∈ grading n k := Iff.rfl

theorem symm_d (f : OPol n) : (equiv n).symm (DG.d f) = d n ((equiv n).symm f) := rfl

theorem d_equiv (f : SkewPolynomial n) : DG.d (equiv n f) = equiv n (d n f) := rfl

instance instDGRing : DGRing (OPol n) where
  one_mem := one_mem_grading'
  mul_mem _ _ _ _ ha hb := mul_mem_grading' ha hb
  d_mul' {k} a ha b := by
    apply (equiv n).symm.injective
    simp only [map_add, map_mul, Units.smul_def, map_zsmul, symm_d]
    rw [d_mul, parityInv_of_mem (mem_grading_iff.mp ha), smul_mul_assoc]

/-- `OPol_n` is a dg `ℤ`-algebra. -/
theorem dgAlgebra_int : DGAlgebra ℤ (OPol n) := inferInstance

theorem x_mem_grading (i : Fin n) : x i ∈ DG.grading (M := OPol n) 1 :=
  generator_mem_grading i

/-- **Ellis–Qi §3.1**: `d(x_i) = x_i²`. -/
theorem d_x (i : Fin n) : DG.d (x i) = x i * x i := by
  rw [x, d_equiv, d_generator, map_mul]

end OPol

/-! ## `OΛ_n` as a dg subring (Lemma 3.2) -/

theorem elementary_mem_grading (k : ℕ) : elementary n k ∈ grading n k := by
  classical
  rw [elementary, FiniteCompleteElementary.FiniteWords.strictSum]
  refine AddSubgroup.sum_mem _ fun f _ => ?_
  rw [FiniteCompleteElementary.FiniteWords.word]
  have := isDHom_ofFn_prod (fun i => generator (f.val i)) (fun _ => (1 : ℤ))
    fun i => isDHom_generator _
  simpa using this.1

/-- In a `ℤ`-graded ring, the subring generated by homogeneous elements is homogeneous. -/
theorem isHomogeneous_subringClosure {A : Type*} [Ring A] (𝒜 : ℤ → AddSubgroup A)
    [GradedRing 𝒜] {s : Set A} (hs : ∀ x ∈ s, ∃ i, x ∈ 𝒜 i) :
    SetLike.IsHomogeneous 𝒜 (Subring.closure s) := by
  classical
  intro i x hx
  induction hx using Subring.closure_induction generalizing i with
  | mem x hx =>
    obtain ⟨j, hj⟩ := hs x hx
    obtain rfl | h := eq_or_ne i j
    · rw [decompose_of_mem_same _ hj]
      exact Subring.subset_closure hx
    · rw [decompose_of_mem_ne _ hj (Ne.symm h)]
      exact zero_mem _
  | zero => simp
  | one =>
    rw [decompose_one, one_def]
    obtain rfl | h := eq_or_ne i 0 <;> simp [of_eq_of_ne, *]
  | add _ _ _ _ h₁ h₂ => simpa using add_mem (h₁ i) (h₂ i)
  | neg _ _ h =>
    rw [decompose_neg, DFinsupp.neg_apply, NegMemClass.coe_neg]
    exact neg_mem (h i)
  | mul x y _ _ h₁ h₂ =>
    rw [decompose_mul, DirectSum.mul_eq_dfinsuppSum]
    rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finsetSum]
    refine sum_mem fun j _ => ?_
    rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finsetSum]
    refine sum_mem fun k _ => ?_
    obtain rfl | h := eq_or_ne i (j + k) <;> simp [of_eq_of_ne, mul_mem, *]

/-- `OΛ_n` as a subring of `OPol n`. -/
def osymOPol (n : ℕ) : Subring (OPol n) :=
  (osym n).map (OPol.equiv n : SkewPolynomial n →+* OPol n)

theorem mem_osymOPol {f : OPol n} : f ∈ osymOPol n ↔ (OPol.equiv n).symm f ∈ osym n :=
  Subring.mem_map_equiv

theorem osymOPol_eq_closure :
    osymOPol n = Subring.closure (Set.range fun k => OPol.equiv n (elementary n k)) := by
  rw [osymOPol, osym, RingHom.map_closure, ← Set.range_comp]
  rfl

/-- The homogeneous components of an element of `OΛ_n` lie in `OΛ_n`. -/
theorem osymOPol_isHomogeneous :
    SetLike.IsHomogeneous (DG.grading (M := OPol n)) (osymOPol n) := by
  rw [osymOPol_eq_closure]
  refine isHomogeneous_subringClosure _ ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨k, elementary_mem_grading k⟩

/-- **Ellis–Qi, Lemma 3.2**: `OΛ_n` is a dg subring of `OPol_n`. -/
def osymDG (n : ℕ) : DGSubring (OPol n) where
  toSubring := osymOPol n
  isHomogeneous' := osymOPol_isHomogeneous
  d_mem' ha := mem_osymOPol.mpr (d_mem_osym (mem_osymOPol.mp ha))

theorem mem_osymDG {f : OPol n} : f ∈ osymDG n ↔ (OPol.equiv n).symm f ∈ osym n :=
  mem_osymOPol

theorem elementary_mem_osymDG (k : ℕ) : OPol.equiv n (elementary n k) ∈ osymDG n :=
  mem_osymDG.mpr (by
    rw [RingEquiv.symm_apply_apply]
    exact Subring.subset_closure ⟨k, rfl⟩)

/-! ## `OPol_n(α)` (Proposition 3.1) -/

/-- The indicator vector `α = 𝟙_S ∈ {0,1}ⁿ`. -/
def indicator (S : Finset (Fin n)) : Fin n → ℤ := fun i => if i ∈ S then 1 else 0

theorem indicator_mem (S : Finset (Fin n)) (i : Fin n) :
    indicator S i = 0 ∨ indicator S i = 1 := by
  unfold indicator; split_ifs <;> simp

theorem sAlpha_mem_grading (α : Fin n → ℤ) : sAlpha α ∈ grading n 1 :=
  AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (generator_mem_grading i) _

/-- `d_α` has degree `+1`. -/
theorem dAlpha_mem_grading (α : Fin n → ℤ) {k : ℤ} {f : SkewPolynomial n}
    (hf : f ∈ grading n k) : dAlpha α f ∈ grading n (k + 1) := by
  rw [dAlpha_apply]
  exact add_mem (d_mem_grading hf) (mul_mem_grading' (parityInv_mem_grading hf)
    (sAlpha_mem_grading α))

/-- The rank-one free left dg `OPol_n`-module `OPol_n(α)`, `α = 𝟙_S`, with cyclic vector `1_α`
in degree `0` (Ellis–Qi (3.2)–(3.3), Proposition 3.1). -/
def OPolAlpha (n : ℕ) (_S : Finset (Fin n)) : Type := SkewPolynomial n

namespace OPolAlpha

variable {S : Finset (Fin n)}

instance instAddCommGroup : AddCommGroup (OPolAlpha n S) :=
  inferInstanceAs (AddCommGroup (OPol n))

instance instModule : Module (OPol n) (OPolAlpha n S) :=
  inferInstanceAs (Module (OPol n) (OPol n))

variable (n S) in
/-- The identification of `OPol_n(α)` with the skew-polynomial model, `f ↦ f 1_α`. -/
def equiv : SkewPolynomial n ≃+ OPolAlpha n S := AddEquiv.refl _

theorem symm_smul (a : OPol n) (f : OPolAlpha n S) :
    (equiv n S).symm (a • f) = (OPol.equiv n).symm a * (equiv n S).symm f := rfl

theorem smul_equiv (a : OPol n) (f : SkewPolynomial n) :
    a • equiv n S f = equiv n S ((OPol.equiv n).symm a * f) := rfl

variable (n S) in
/-- The generator `1_α`. -/
def one : OPolAlpha n S := equiv n S 1

instance instDGAddCommGroup : DGAddCommGroup (OPolAlpha n S) where
  grading := grading n
  decomposition := decomposition n
  d := dAlpha (indicator S)
  d_mem' hm := dAlpha_mem_grading (indicator S) hm
  d_d' := (prop_3_1_left (indicator S)).mpr (indicator_mem S)

theorem mem_grading_iff {k : ℤ} {f : OPolAlpha n S} :
    f ∈ DG.grading k ↔ (equiv n S).symm f ∈ grading n k := Iff.rfl

theorem symm_d (f : OPolAlpha n S) :
    (equiv n S).symm (DG.d f) = dAlpha (indicator S) ((equiv n S).symm f) := rfl

theorem d_equiv (f : SkewPolynomial n) :
    DG.d (equiv n S f) = equiv n S (dAlpha (indicator S) f) := rfl

theorem one_mem_grading : one n S ∈ DG.grading 0 := one_mem_grading'

/-- `d(1_α) = (Σ α_i x_i) 1_α` (Ellis–Qi (3.2)). -/
theorem d_one : DG.d (one n S) = OPol.equiv n (sAlpha (indicator S)) • one n S := by
  apply (equiv n S).symm.injective
  rw [symm_d, symm_smul, one, AddEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, dAlpha_apply,
    EQSkewDifferential.d_one, map_one, one_mul, zero_add, mul_one]

/-- **Ellis–Qi, Proposition 3.1**: `OPol_n(α)` is a left dg module over `OPol_n` for every
`α ∈ {0,1}ⁿ`. -/
instance instDGModule : DGModule (OPol n) (OPolAlpha n S) where
  smul_mem _ _ _ _ ha hb := mul_mem_grading' ha hb
  d_smul' {k} a ha m := by
    apply (equiv n S).symm.injective
    simp only [map_add, Units.smul_def, map_zsmul, symm_smul, symm_d, OPol.symm_d]
    rw [dAlpha_mul, parityInv_of_mem (OPol.mem_grading_iff.mp ha), smul_mul_assoc]

end OPolAlpha

/-! ## The bimodule `Z_n` (Proposition 3.7, Definition 3.8) -/

/-- The set of odd strands `{1, 3, 5, …}` (0-indexed), so that `𝟙_S = (0,1,0,1,…)`. -/
def oddStrands (n : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => i.val % 2 = 1

theorem indicator_oddStrands : indicator (oddStrands n) = zAlpha n := by
  funext i
  simp only [indicator, oddStrands, Finset.mem_filter, Finset.mem_univ, true_and, zAlpha]
  rcases Nat.mod_two_eq_zero_or_one i.val with h | h <;> simp [h]

/-- `Z_n = OPol_n(0,1,0,1,…)`, a dg `(OPol_n, OPol_n)`-bimodule with the right action
`g 1_z · f = g (θ ∘ w₀)(f) 1_z` (Ellis–Qi (3.18)–(3.20)). -/
abbrev Zn (n : ℕ) : Type := OPolAlpha n (oddStrands n)

namespace Zn

/-- The right action `g 1_z · f = g (θ ∘ w₀)(f) 1_z`. -/
def rsmul (f : OPol n) (g : Zn n) : Zn n :=
  OPolAlpha.equiv n _
    ((OPolAlpha.equiv n _).symm g * twistRev n ((OPol.equiv n).symm f))

theorem symm_rsmul (f : OPol n) (g : Zn n) :
    (OPolAlpha.equiv n _).symm (rsmul f g) =
      (OPolAlpha.equiv n _).symm g * twistRev n ((OPol.equiv n).symm f) := rfl

instance instModuleOp : Module (OPol n)ᵐᵒᵖ (Zn n) where
  smul f g := rsmul f.unop g
  one_smul g := by
    show rsmul (MulOpposite.unop 1) g = g
    apply (OPolAlpha.equiv n _).symm.injective
    rw [symm_rsmul, MulOpposite.unop_one, map_one, map_one, mul_one]
  mul_smul f f' g := by
    show rsmul (MulOpposite.unop (f * f')) g = rsmul f.unop (rsmul f'.unop g)
    apply (OPolAlpha.equiv n _).symm.injective
    rw [symm_rsmul, symm_rsmul, symm_rsmul, MulOpposite.unop_mul, map_mul, map_mul, mul_assoc]
  smul_zero f := by
    show rsmul f.unop 0 = 0
    apply (OPolAlpha.equiv n _).symm.injective
    rw [symm_rsmul, map_zero, zero_mul]
  smul_add f g g' := by
    show rsmul f.unop (g + g') = rsmul f.unop g + rsmul f.unop g'
    apply (OPolAlpha.equiv n _).symm.injective
    rw [map_add, symm_rsmul, symm_rsmul, symm_rsmul, map_add, add_mul]
  add_smul f f' g := by
    show rsmul (MulOpposite.unop (f + f')) g = rsmul f.unop g + rsmul f'.unop g
    apply (OPolAlpha.equiv n _).symm.injective
    rw [map_add, symm_rsmul, symm_rsmul, symm_rsmul, MulOpposite.unop_add, map_add, map_add,
      mul_add]
  zero_smul g := by
    show rsmul (MulOpposite.unop 0) g = 0
    apply (OPolAlpha.equiv n _).symm.injective
    rw [symm_rsmul, MulOpposite.unop_zero, map_zero, map_zero, mul_zero, map_zero]

theorem op_smul_def (f : OPol n) (g : Zn n) : MulOpposite.op f • g = rsmul f g := rfl

theorem symm_op_smul (f : OPol n) (g : Zn n) :
    (OPolAlpha.equiv n _).symm (MulOpposite.op f • g) =
      (OPolAlpha.equiv n _).symm g * twistRev n ((OPol.equiv n).symm f) := rfl

/-- The right action on the generator: `1_z · f = (θ ∘ w₀)(f) 1_z`. -/
theorem op_smul_one (f : OPol n) :
    MulOpposite.op f • OPolAlpha.one n (oddStrands n) =
      OPol.equiv n (twistRev n ((OPol.equiv n).symm f)) • OPolAlpha.one n (oddStrands n) := by
  apply (OPolAlpha.equiv n _).symm.injective
  rw [symm_op_smul, OPolAlpha.symm_smul, OPolAlpha.one, AddEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply, one_mul, mul_one]

/-- **Ellis–Qi, Proposition 3.7 / Definition 3.8**: the right action is compatible with the
differential, for all of `OPol_n`. -/
instance instDGRightModule : DGRightModule (OPol n) (Zn n) where
  op_smul_mem' {i j a m} ha hm := by
    rw [OPolAlpha.mem_grading_iff, symm_op_smul]
    exact mul_mem_grading' (OPolAlpha.mem_grading_iff.mp hm)
      (twistRev_mem_grading (OPol.mem_grading_iff.mp ha))
  d_op_smul' {j m} hm a := by
    apply (OPolAlpha.equiv n _).symm.injective
    simp only [map_add, Units.smul_def, map_zsmul, symm_op_smul, OPolAlpha.symm_d, OPol.symm_d]
    rw [indicator_oddStrands, dAlpha_mul_twistRev, parityInv_of_mem (OPolAlpha.mem_grading_iff.mp hm),
      smul_mul_assoc]

instance instSMulCommClass : SMulCommClass (OPol n) (OPol n)ᵐᵒᵖ (Zn n) where
  smul_comm a f g := by
    show a • rsmul f.unop g = rsmul f.unop (a • g)
    apply (OPolAlpha.equiv n _).symm.injective
    rw [OPolAlpha.symm_smul, symm_rsmul, symm_rsmul, OPolAlpha.symm_smul, mul_assoc]

/-- `Z_n` is a dg `(OPol_n, OPol_n)`-bimodule. -/
instance instDGBimodule : DGBimodule (OPol n) (OPol n) (Zn n) := DGBimodule.mk'

/-- The right action of `OΛ_n` on `Z_n`, by restriction. -/
instance instModuleOsymOp : Module (osymDG n)ᵐᵒᵖ (Zn n) :=
  Module.compHom (Zn n) ((DGSubring.subtype (osymDG n)).toRingHom.op)

theorem op_smul_osym (f : osymDG n) (g : Zn n) :
    MulOpposite.op f • g = MulOpposite.op (f : OPol n) • g := rfl

instance dgRightModuleOsym : DGRightModule (osymDG n) (Zn n) where
  op_smul_mem' ha hm := DG.op_smul_mem_grading (A := OPol n) ha hm
  d_op_smul' hm a := DG.d_op_smul (A := OPol n) hm (a : OPol n)

instance instSMulCommClassOsym : SMulCommClass (OPol n) (osymDG n)ᵐᵒᵖ (Zn n) where
  smul_comm a f g := smul_comm a (MulOpposite.op (f.unop : OPol n)) g

/-- **Ellis–Qi, Definition 3.8**: `Z_n` is a dg `(OPol_n, OΛ_n)`-bimodule. -/
instance dgBimoduleOsym : DGBimodule (OPol n) (osymDG n) (Zn n) := DGBimodule.mk'

end Zn

end

end OddMath.Frontier.EQSkewDifferential
