import OddMath.Frontier.EQOnhDGRing
import OddMath.Frontier.OnhPolynomial
import OddMath.Frontier.EQDGStructures

/-!
# The dots `OPol_{n+2} → ONH_{n+2}` as a morphism of dg rings

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.1–§3.2: the differential of `ONH_n` restricts on the polynomial subalgebra of dots to the
differential `d(x_i) = x_i²` of `OPol_n`.

* `ringHom_mem_grading`, `ringHom_d`: a ring homomorphism from `OPol_m` to a dg ring sending
  each `x_j` to an element of degree `1` whose differential is its square is a morphism of dg
  rings.
* `ONH.polyHom n : OPol (n + 2) →ᵈᵍ+* ONH n`, `x_j ↦ x_j`, the inclusion of dots
  (`ONH.polyHom_injective`), compatible with `EQSkewDifferential.d` (`ONH.polyHom_d`).
-/

noncomputable section

namespace OddMath.Frontier.EQOnhDG

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential (OPol totalDeg)
open NilHeckeAction

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) onhPolyNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) onhPolyNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

section RingHom

variable {m : ℕ} {B : Type*} [Ring B] [DG.DGAddCommGroup B] [DG.DGRing B]
  (φ : SkewPolynomial m →+* B)

/-- A ring homomorphism out of `OPol_m` sending each `x_j` to an element of degree `1` preserves
the grading. -/
theorem ringHom_mem_grading (hφ : ∀ j, φ (generator j) ∈ DG.grading (M := B) 1) {k : ℤ}
    {f : SkewPolynomial m} (hf : f ∈ EQSkewDifferential.grading m k) :
    φ f ∈ DG.grading (M := B) k := by
  classical
  have hpow : ∀ (j : Fin m) (e : ℕ), φ (generator j ^ e) ∈ DG.grading (M := B) e := by
    intro j e
    induction e with
    | zero => simpa using DG.one_mem_grading (A := B)
    | succ e ih =>
      rw [pow_succ, map_mul]
      simpa using DG.mul_mem_grading ih (hφ j)
  have hprod : ∀ {l : ℕ} (v : Fin l → SkewPolynomial m) (e : Fin l → ℤ),
      (∀ i, φ (v i) ∈ DG.grading (M := B) (e i)) →
        φ (List.ofFn v).prod ∈ DG.grading (M := B) (∑ i, e i) := by
    intro l
    induction l with
    | zero => intro v e _; simpa using DG.one_mem_grading (A := B)
    | succ l ih =>
      intro v e h
      rw [List.ofFn_succ, List.prod_cons, map_mul, Fin.sum_univ_succ]
      exact DG.mul_mem_grading (h 0) (ih _ _ fun i => h _)
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine AddSubgroup.sum_mem _ fun a ha => ?_
  have h := OddMath.Frontier.MonomialReversal.monomial_eq_smul_prod a (f a)
  change Finsupp.single a (f a) = _ at h
  rw [h, map_zsmul, ← hf a ha]
  exact AddSubgroup.zsmul_mem _ (hprod _ (fun j => (a j : ℤ)) fun j => hpow j (a j)) _

variable (hφ : ∀ j, φ (generator j) ∈ DG.grading (M := B) 1)
  (hd : ∀ j, DG.d (φ (generator j)) = φ (generator j) * φ (generator j))

include hφ hd

/-- The compatibility with the differentials, for a homogeneous element. -/
def CommD (f : SkewPolynomial m) (k : ℤ) : Prop :=
  f ∈ EQSkewDifferential.grading m k ∧ φ (EQSkewDifferential.d m f) = DG.d (φ f)

omit hd in
theorem commD_mul {f g : SkewPolynomial m} {i j : ℤ} (hf : CommD φ f i) (hg : CommD φ g j) :
    CommD φ (f * g) (i + j) := by
  refine ⟨EQSkewDifferential.mul_mem_grading' hf.1 hg.1, ?_⟩
  rw [EQSkewDifferential.d_mul, EQSkewDifferential.parityInv_of_mem hf.1]
  simp only [map_add, map_mul]
  rw [hf.2, hg.2, DG.d_mul (ringHom_mem_grading φ hφ hf.1), map_zsmul, Units.smul_def,
    smul_mul_assoc]

omit [DG.DGRing B] hφ in
theorem commD_generator (j : Fin m) : CommD φ (generator j) 1 :=
  ⟨EQSkewDifferential.generator_mem_grading j, by
    rw [EQSkewDifferential.d_generator, map_mul, hd]⟩

omit hφ hd in
theorem commD_one : CommD φ 1 0 :=
  ⟨EQSkewDifferential.one_mem_grading', by rw [EQSkewDifferential.d_one, map_zero, map_one, DG.d_one]⟩

theorem commD_pow (j : Fin m) : ∀ e : ℕ, CommD φ (generator j ^ e) (e : ℤ)
  | 0 => by simpa using commD_one φ
  | e + 1 => by
    rw [pow_succ]
    have := commD_mul φ hφ (commD_pow j e) (commD_generator φ hd j)
    simpa using this

omit hd in
theorem commD_ofFn_prod : ∀ {l : ℕ} (v : Fin l → SkewPolynomial m) (e : Fin l → ℤ),
    (∀ i, CommD φ (v i) (e i)) → CommD φ (List.ofFn v).prod (∑ i, e i)
  | 0, v, e, _ => by simpa using commD_one φ
  | l + 1, v, e, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact commD_mul φ hφ (h 0) (commD_ofFn_prod (fun i => v i.succ) (fun i => e i.succ) fun i => h _)

/-- A ring homomorphism out of `OPol_m` sending each `x_j` to an element `y_j` of degree `1`
with `d(y_j) = y_j²` commutes with the differentials. -/
theorem ringHom_d (f : SkewPolynomial m) :
    φ (EQSkewDifferential.d m f) = DG.d (φ f) := by
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, DG.d_add]
  | single a c =>
    have h := OddMath.Frontier.MonomialReversal.monomial_eq_smul_prod a c
    change Finsupp.single a c = _ at h
    rw [h, map_zsmul, map_zsmul, map_zsmul, DG.d_zsmul,
      (commD_ofFn_prod φ hφ _ (fun j => (a j : ℤ)) fun j => commD_pow φ hφ hd j (a j)).2]

end RingHom

namespace ONH

variable {n : ℕ}

/-- The dots `OPol_{n+2} → ONH_{n+2}` as a ring homomorphism on the skew-polynomial model. -/
def polyRingHom (n : ℕ) : SkewPolynomial (n + 2) →+* ONH n :=
  (equiv n).toRingHom.comp (OnhPolynomial.polyElem n)

theorem polyRingHom_generator (j : Fin (n + 2)) : polyRingHom n (generator j) = x j := by
  simp [polyRingHom, OnhPolynomial.polyElem_generator, x]

/-- **The inclusion of dots `OPol_{n+2} → ONH_{n+2}`** (`x_j ↦ x_j`) is a morphism of dg rings:
it has degree `0` and intertwines `d(x_i) = x_i²` on `OPol_{n+2}` with the differential of
`ONH_{n+2}` (Ellis–Qi §3.1–§3.2). -/
def polyHom (n : ℕ) : OPol (n + 2) →ᵈᵍ+* ONH n where
  toRingHom := (polyRingHom n).comp (OPol.equiv (n + 2)).symm.toRingHom
  map_mem' {k a} ha :=
    ringHom_mem_grading (polyRingHom n)
      (fun j => by rw [polyRingHom_generator]; exact x_mem_grading j)
      (OPol.mem_grading_iff.mp ha)
  map_d' a :=
    ringHom_d (polyRingHom n) (fun j => by rw [polyRingHom_generator]; exact x_mem_grading j)
      (fun j => by rw [polyRingHom_generator]; exact d_x j) _

theorem polyHom_x (j : Fin (n + 2)) : polyHom n (OPol.x j) = x j :=
  polyRingHom_generator j

/-- Compatibility with the differential `EQSkewDifferential.d` of `OPol_{n+2}`:
`d(ι(f)) = ι(d f)` in `ONH_{n+2}`. -/
theorem polyHom_d (f : SkewPolynomial (n + 2)) :
    polyHom n (OPol.equiv (n + 2) (EQSkewDifferential.d (n + 2) f)) =
      DG.d (polyHom n (OPol.equiv (n + 2) f)) :=
  (polyHom n).map_d (OPol.equiv (n + 2) f)

/-- The inclusion of dots is injective (the polynomial representation is faithful). -/
theorem polyHom_injective : Function.Injective (polyHom n) := by
  intro f g h
  have h' : OnhPolynomial.polyElem n f = OnhPolynomial.polyElem n g := h
  have := congrArg (fun a => action n a 1) h'
  simpa only [OnhPolynomial.action_polyElem, mul_one] using this

end ONH

end OddMath.Frontier.EQOnhDG

end
