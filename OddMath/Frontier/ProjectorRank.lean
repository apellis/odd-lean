import OddMath.Frontier.GradedTrace
import OddMath.Frontier.ZeroHecke
import OddMath.Frontier.LongestKernel
import OddMath.Frontier.ElementaryBasis
import OddMath.Frontier.OnhWindow
import OddMath.Frontier.PrefixEmbedding
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-! # Graded ranks of the images of the projectors `e_a` and `e_a ⊗ e_b`

EKL arXiv:1111.1320v1 §3.2, §4.4; Prop 2.2 (graded ranks).

`Vd N d` is the span of the monomials of total degree `d` in `SkewPolynomial N` (ordinary
degree: `Vd N d = polynomialPiece N (2d)`), free with the monomial basis.  An operator of
degree `0` has trace `∑_{|γ|=d} (T x^γ)_γ` on `Vd N d`.

* Degrees: `x_j` has degree `1`, `∂_i` degree `-1`, `x^A ∂_w` degree `|A| - ℓ(w)`, and
  `e_{n+2}` degree `0`.
* `e(V_{k+C}) = x^δ · OΛ_k` with `C = C(n+2,2)`, and `e(V_m) = 0` for `m < C`; hence
  `rk e(V_{k+C})` is the number of partitions of `k` with at most `n+2` parts.
* Two windows: `e_a ⊗ e_b` acts on `ι(f) ι'(g)` as `ι(e_a f) ι'(e_b g)`, with no sign, so
  `tr(e_a ⊗ e_b | V_d) = ∑_{i+j=d} tr(e_a | V_i) tr(e_b | V_j)`.
-/
namespace OddMath.Frontier.ProjectorRank
open OddMath.SkewPolynomial (SkewPolynomial monomial generator)
open NilHeckeAction NilCoxeterWords NilHeckeGradedEnd GradedTrace Module LinearMap
noncomputable section

/-! ## The monomial grading -/

/-- Exponent vectors of total degree `d`. -/
def expSet (N : ℕ) (d : ℤ) : Finset (Fin N → ℕ) :=
  (Finset.Nat.antidiagonalTuple N d.toNat).filter fun _ => 0 ≤ d

theorem mem_expSet {N : ℕ} {d : ℤ} {γ : Fin N → ℕ} :
    γ ∈ expSet N d ↔ ((∑ i, γ i : ℕ) : ℤ) = d := by
  simp only [expSet, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  omega

/-- The span of the monomials of total degree `d` (`⊥` for `d < 0`). -/
def Vd (N : ℕ) (d : ℤ) : Submodule ℤ (SkewPolynomial N) := polynomialPiece N (2*d)

theorem mem_Vd {N : ℕ} {d : ℤ} {f : SkewPolynomial N} :
    f ∈ Vd N d ↔ ∀ γ, ((∑ i, γ i : ℕ) : ℤ) ≠ d → f γ = 0 := by
  change (∀ a, pdegree a ≠ 2*d → f a = 0) ↔ _
  simp only [pdegree]
  exact ⟨fun h a ha => h a (by omega), fun h a ha => h a (by omega)⟩

theorem Vd_eq_supported (N : ℕ) (d : ℤ) :
    Vd N d = Finsupp.supported ℤ ℤ (expSet N d : Set (Fin N → ℕ)) := by
  ext f
  rw [mem_Vd, Finsupp.mem_supported']
  simp only [Finset.mem_coe, mem_expSet]

theorem monomial_mem_Vd {N : ℕ} (γ : Fin N → ℕ) (c : ℤ) :
    monomial γ c ∈ Vd N (∑ i, γ i : ℕ) := by
  rw [mem_Vd]
  intro δ hδ
  exact Finsupp.single_eq_of_ne fun h => hδ (by rw [h])

theorem Vd_neg (N : ℕ) {d : ℤ} (hd : d < 0) : Vd N d = ⊥ :=
  polynomial_negative N _ (by omega)

theorem Vd_eq_span (N : ℕ) (d : ℤ) :
    Vd N d = Submodule.span ℤ ((fun γ => monomial γ 1) '' (expSet N d : Set (Fin N → ℕ))) := by
  rw [Vd_eq_supported, Finsupp.supported_eq_span_single]

theorem iSup_Vd (N : ℕ) : ⨆ d, Vd N d = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  rw [← Finsupp.sum_single f]
  refine Submodule.sum_mem _ fun γ _ => ?_
  exact Submodule.mem_iSup_of_mem _ (monomial_mem_Vd γ (f γ))

/-- Coordinates of `V_d` in the monomial basis. -/
def reprVd (N : ℕ) (d : ℤ) : Vd N d ≃ₗ[ℤ] (expSet N d →₀ ℤ) :=
  (LinearEquiv.ofEq _ _ (Vd_eq_supported N d)).trans (Finsupp.supportedEquivFinsupp _)

/-- The monomial basis of `V_d`. -/
def monomialBasis (N : ℕ) (d : ℤ) : Basis (expSet N d) ℤ (Vd N d) := Basis.ofRepr (reprVd N d)

@[simp] theorem monomialBasis_repr (N : ℕ) (d : ℤ) (v : Vd N d) (γ : expSet N d) :
    (monomialBasis N d).repr v γ = (v : SkewPolynomial N) γ := rfl

@[simp] theorem monomialBasis_apply (N : ℕ) (d : ℤ) (γ : expSet N d) :
    (monomialBasis N d γ : SkewPolynomial N) = monomial γ 1 := by
  classical
  have hγ : monomial (γ : Fin N → ℕ) 1 ∈ Vd N d := by
    have := monomial_mem_Vd (γ : Fin N → ℕ) 1
    rwa [mem_expSet.1 γ.2] at this
  suffices monomialBasis N d γ = ⟨_, hγ⟩ from congrArg Subtype.val this
  apply (monomialBasis N d).repr.injective
  ext δ
  rw [Basis.repr_self, monomialBasis_repr]
  simp only [Finsupp.single_apply, Subtype.ext_iff, monomial]

instance (N : ℕ) (d : ℤ) : Module.Free ℤ (Vd N d) := Module.Free.of_basis (monomialBasis N d)

instance (N : ℕ) (d : ℤ) : Module.Finite ℤ (Vd N d) := Module.Finite.of_basis (monomialBasis N d)

theorem finrank_Vd (N : ℕ) (d : ℤ) : finrank ℤ (Vd N d) = (expSet N d).card := by
  rw [finrank_eq_card_basis (monomialBasis N d), Fintype.card_coe]

/-- Monomial-basis trace formula for an operator of degree `0`. -/
theorem trace_res_eq {N : ℕ} {T : SkewPolynomial N →ₗ[ℤ] SkewPolynomial N}
    (hT : HasDegree (Vd N) 0 T) (d : ℤ) :
    trace ℤ (Vd N d) (hT.res d d (add_zero d)) = ∑ γ ∈ expSet N d, T (monomial γ 1) γ := by
  rw [trace_eq_matrix_trace ℤ (monomialBasis N d), Matrix.trace]
  simp only [Matrix.diag, toMatrix_apply, monomialBasis_repr, restrict_coe_apply,
    monomialBasis_apply]
  exact Finset.sum_coe_sort (expSet N d) fun γ => T (monomial γ 1) γ

/-! ## Degrees of operators -/

section Degrees
variable {N : ℕ}

theorem hasDegree_comp {a b : ℤ} {S T : SkewPolynomial N →ₗ[ℤ] SkewPolynomial N}
    (hS : HasDegree (Vd N) a S) (hT : HasDegree (Vd N) b T) :
    HasDegree (Vd N) (a + b) (S ∘ₗ T) := fun d _ hv =>
  hS.mem (by ring) (hT d _ hv)

theorem hasDegree_add {a : ℤ} {S T : SkewPolynomial N →ₗ[ℤ] SkewPolynomial N}
    (hS : HasDegree (Vd N) a S) (hT : HasDegree (Vd N) a T) : HasDegree (Vd N) a (S + T) :=
  fun d _ hv => add_mem (hS d _ hv) (hT d _ hv)

theorem hasDegree_smul {a : ℤ} (z : ℤ) {T : SkewPolynomial N →ₗ[ℤ] SkewPolynomial N}
    (hT : HasDegree (Vd N) a T) : HasDegree (Vd N) a (z • T) :=
  fun d _ hv => Submodule.smul_mem _ z (hT d _ hv)

theorem hasDegree_id : HasDegree (Vd N) 0 (LinearMap.id : SkewPolynomial N →ₗ[ℤ] _) :=
  fun d _ hv => by simpa using hv

theorem mul_mem_Vd {a b : ℤ} {f g : SkewPolynomial N} (hf : f ∈ Vd N a) (hg : g ∈ Vd N b) :
    f * g ∈ Vd N (a + b) := by
  have h := polynomial_mul hf hg
  rwa [← mul_add] at h

/-- Left multiplication by an element of `V_k` has degree `k`. -/
theorem hasDegree_mulLeft {k : ℤ} {p : SkewPolynomial N} (hp : p ∈ Vd N k) :
    HasDegree (Vd N) k (LinearMap.mulLeft ℤ p) := fun d _ hv => by
  rw [add_comm]; exact mul_mem_Vd hp hv

/-- Left multiplication by `x_j` has degree `1`. -/
theorem hasDegree_generator (j : Fin N) :
    HasDegree (Vd N) 1 (LinearMap.mulLeft ℤ (generator j)) :=
  hasDegree_mulLeft (by simpa [Vd] using generator_mem j)

/-- Divided differences have degree `-1`. -/
theorem hasDegree_divided {n : ℕ} (i : Fin (n+1)) :
    HasDegree (Vd (n+2)) (-1) (AllRankDivided.divided i) := fun d _ hv => by
  have h := divided_mem i hv
  rwa [show 2*d - 2 = 2*(d + -1) by ring] at h

end Degrees

section Action
variable {n : ℕ}

theorem hasDegree_action_mul {a b : ℤ} {u v : Presented n}
    (hu : HasDegree (Vd (n+2)) a (action n u)) (hv : HasDegree (Vd (n+2)) b (action n v)) :
    HasDegree (Vd (n+2)) (a + b) (action n (u * v)) := by
  rw [map_mul]; exact hasDegree_comp hu hv

theorem hasDegree_action_one : HasDegree (Vd (n+2)) 0 (action n 1) := by
  rw [map_one]; exact hasDegree_id

theorem hasDegree_dot (j : Fin (n+2)) : HasDegree (Vd (n+2)) 1 (action n (dot n j)) := by
  rw [action_dot]; exact hasDegree_generator j

theorem hasDegree_crossing (i : Fin (n+1)) :
    HasDegree (Vd (n+2)) (-1) (action n (crossing n i)) := by
  rw [action_crossing]; exact hasDegree_divided i

/-- The ordered dot monomial `x^A` has degree `|A|`. -/
theorem hasDegree_dotMonomial (A : Fin (n+2) → ℕ) :
    HasDegree (Vd (n+2)) (∑ i, A i : ℕ) (action n (NilHeckeBasis.dotMonomial A)) :=
  fun d f hf => by
    rw [NilHeckeBasis.action_dotMonomial, add_comm d]
    exact mul_mem_Vd (monomial_mem_Vd A 1) hf

/-- A product of crossings along `w` has degree `-length w`. -/
theorem hasDegree_product (w : Word n) :
    HasDegree (Vd (n+2)) (-(w.length : ℤ)) (action n (product w)) := by
  induction w with
  | nil => simpa [product] using hasDegree_action_one
  | cons i w ih =>
      have h := hasDegree_action_mul (hasDegree_crossing i) ih
      rw [show (-1 : ℤ) + -(w.length : ℤ) = -((i :: w).length : ℤ) by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring] at h
      exact h

/-- `x^A ∂_w` has degree `|A| - length w`. -/
theorem hasDegree_dotMonomial_mul_product (A : Fin (n+2) → ℕ) (w : Word n) :
    HasDegree (Vd (n+2)) ((∑ i, A i : ℕ) - w.length)
      (action n (NilHeckeBasis.dotMonomial A * product w)) := by
  rw [sub_eq_add_neg]
  exact hasDegree_action_mul (hasDegree_dotMonomial A) (hasDegree_product w)

theorem hasDegree_zeroHecke (i : Fin (n+1)) :
    HasDegree (Vd (n+2)) 0 (action n (ZeroHecke.zeroHecke n i)) := by
  have h := hasDegree_action_mul (hasDegree_dot i.castSucc) (hasDegree_crossing i)
  rw [add_neg_cancel] at h
  exact h

theorem hasDegree_zeroHeckeProduct (w : Word n) :
    HasDegree (Vd (n+2)) 0 (action n (ZeroHecke.zeroHeckeProduct w)) := by
  induction w with
  | nil => exact hasDegree_action_one
  | cons i w ih => simpa using hasDegree_action_mul (hasDegree_zeroHecke i) ih

/-- The projector `e_{n+2}` has degree `0`. -/
theorem hasDegree_projector : HasDegree (Vd (n+2)) 0 (action n (ZeroHecke.projector n)) :=
  hasDegree_zeroHeckeProduct _

/-- The longest divided difference has degree `-C(n+2,2)`. -/
theorem hasDegree_D : HasDegree (Vd (n+2)) (-((n+2).choose 2 : ℕ)) (LongestDivided.D (n+2)) := by
  rw [← ZeroHecke.action_DElem, ZeroHecke.DElem, ← LongestFactor.wordIn_length n (n+2) le_rfl]
  exact hasDegree_product _

theorem projector_idem :
    action n (ZeroHecke.projector n) ∘ₗ action n (ZeroHecke.projector n) =
      action n (ZeroHecke.projector n) := by
  rw [← Module.End.mul_eq_comp, ← map_mul, ZeroHecke.projector_mul_projector]

end Action

/-! ## The image of `e_{n+2}` -/

section Image
variable {N : ℕ}

theorem monomial_mul_apply_add (a γ : Fin N → ℕ) (g : SkewPolynomial N) :
    (monomial a 1 * g) (a + γ) = OddMath.skewSign a γ * g γ := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [mul_add, Finsupp.add_apply, hf, hg]
  | single b s =>
      rw [show monomial a 1 * Finsupp.single b s = monomial (a + b) (1 * s * OddMath.skewSign a b)
        from OddMath.SkewPolynomial.mul_monomial a b 1 s]
      by_cases h : b = γ
      · subst h; simp [monomial, mul_comm]
      · have h' : a + b ≠ a + γ := fun e => h (add_left_cancel e)
        simp [monomial, Finsupp.single_eq_of_ne h', Finsupp.single_eq_of_ne h]

/-- Left multiplication by a monomial is injective. -/
theorem mulLeft_monomial_injective (a : Fin N → ℕ) :
    Function.Injective (LinearMap.mulLeft ℤ (monomial a 1 : SkewPolynomial N)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  ext γ
  have h := monomial_mul_apply_add a γ g
  rw [show monomial a 1 * g = 0 from hg, Finsupp.zero_apply] at h
  have hs : OddMath.skewSign a γ ≠ 0 := pow_ne_zero _ (by norm_num)
  simpa [hs] using h.symm

end Image

section Projector
variable (n : ℕ)

theorem staircase_mem_Vd : LongestDivided.staircase (n+2) ∈ Vd (n+2) ((n+2).choose 2 : ℕ) :=
  staircase_mem (n+2)

theorem mem_degreePiece {k : ℕ} {f : SkewPolynomial (n+2)} :
    f ∈ ElementaryBasis.degreePiece n k ↔
      f ∈ OddSymmetricKernel.kernelSubring n ∧ f ∈ Vd (n+2) k := by
  change (_ ∧ ∀ a, _ → _) ↔ _
  rw [mem_Vd]
  simp only [ElementaryBasis.weight, ne_eq, Nat.cast_inj]

private theorem sign_mul_self (k : ℕ) : ((-1 : ℤ)^k) * (-1)^k = 1 := by
  rw [← mul_pow]; norm_num

/-- `e(x^δ c) = x^δ c` for `c` odd symmetric. -/
theorem projector_staircase_mul {c : SkewPolynomial (n+2)}
    (hc : c ∈ OddSymmetricKernel.kernelSubring n) :
    action n (ZeroHecke.projector n) (LongestDivided.staircase (n+2) * c) =
      LongestDivided.staircase (n+2) * c := by
  rw [ZeroHecke.action_projector, LongestDivided.D_right_kernel n _ c hc,
    LongestDivided.D_staircase, smul_mul_assoc, one_mul, mul_smul_comm, smul_smul,
    sign_mul_self, one_smul]

/-- `e f = x^δ · (±D f)`. -/
theorem projector_apply_eq (f : SkewPolynomial (n+2)) :
    action n (ZeroHecke.projector n) f = LongestDivided.staircase (n+2) *
      ((-1 : ℤ)^((n+2).choose 3) • LongestDivided.D (n+2) f) := by
  rw [ZeroHecke.action_projector, mul_smul_comm]

/-- `e(V_{k+C}) = x^δ · OΛ_k` with `C = C(n+2,2)`. -/
theorem map_projector (k : ℕ) :
    (Vd (n+2) (k + ((n+2).choose 2 : ℕ))).map (action n (ZeroHecke.projector n)) =
      (ElementaryBasis.degreePiece n k).map
        (LinearMap.mulLeft ℤ (LongestDivided.staircase (n+2))) := by
  ext g
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨_, (mem_degreePiece n).2 ⟨?_, ?_⟩, (projector_apply_eq n f).symm⟩
    · exact Subring.zsmul_mem _ (LongestKernel.D_mem_kernel n f) _
    · refine Submodule.smul_mem _ _ (hasDegree_D.mem ?_ hf)
      ring
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hk, hc⟩ := (mem_degreePiece n).1 hc
    refine ⟨_, ?_, projector_staircase_mul n hk⟩
    rw [add_comm (k : ℤ)]
    exact mul_mem_Vd (staircase_mem_Vd n) hc

/-- Below degree `C(n+2,2)` the projector vanishes. -/
theorem map_projector_of_lt {m : ℤ} (hm : m < ((n+2).choose 2 : ℕ)) :
    (Vd (n+2) m).map (action n (ZeroHecke.projector n)) = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  have hD : LongestDivided.D (n+2) f ∈ Vd (n+2) (m + -((n+2).choose 2 : ℕ)) := hasDegree_D m f hf
  rw [Vd_neg _ (by omega), Submodule.mem_bot] at hD
  simp [projector_apply_eq, hD]

/-- Rank of `e(V_{k+C})`: the number of partitions of `k` with at most `n+2` parts. -/
theorem finrank_map_projector_add (k : ℕ) :
    finrank ℤ ((Vd (n+2) (k + ((n+2).choose 2 : ℕ))).map (action n (ZeroHecke.projector n))) =
      Fintype.card (ElementaryBasis.Index (n+2) k) := by
  rw [map_projector, ← ElementaryBasis.graded_rank]
  exact (Submodule.equivMapOfInjective _ (mulLeft_monomial_injective _) _).finrank_eq.symm

/-- Rank of `e(V_m)`: that of the degree `m - C(n+2,2)` piece of `OΛ_{n+2}`. -/
theorem finrank_map_projector (m : ℤ) :
    finrank ℤ ((Vd (n+2) m).map (action n (ZeroHecke.projector n))) =
      if (((n+2).choose 2 : ℕ) : ℤ) ≤ m then
        Fintype.card (ElementaryBasis.Index (n+2) (m - ((n+2).choose 2 : ℕ)).toNat)
      else 0 := by
  split_ifs with hm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + ((n+2).choose 2 : ℕ) :=
      ⟨(m - ((n+2).choose 2 : ℕ)).toNat, by omega⟩
    rw [finrank_map_projector_add, add_sub_cancel_right, Int.toNat_natCast]
  · rw [map_projector_of_lt n (by omega), finrank_bot]

/-- Trace of `e` on `V_m`. -/
theorem trace_projector (m : ℤ) :
    trace ℤ (Vd (n+2) m) (hasDegree_projector.res m m (add_zero m)) =
      if (((n+2).choose 2 : ℕ) : ℤ) ≤ m then
        (Fintype.card (ElementaryBasis.Index (n+2) (m - ((n+2).choose 2 : ℕ)).toNat) : ℤ)
      else 0 := by
  rw [hasDegree_projector.trace_res projector_idem, finrank_map_projector]
  split_ifs <;> simp

end Projector

/-! ## Strand windows -/

section Place
variable {a N : ℕ}

/-- The order embedding `j ↦ j + p`. -/
def shiftEmb (p : ℕ) (h : p + a ≤ N) : Fin a ↪o Fin N :=
  OrderEmbedding.ofStrictMono (fun j => ⟨j.val + p, by omega⟩)
    (fun _ _ hjk => Nat.add_lt_add_right hjk p)

@[simp] theorem shiftEmb_val (p : ℕ) (h : p + a ≤ N) (j : Fin a) :
    (shiftEmb p h j).val = j.val + p := rfl

/-- `SkewPolynomial a` placed on the variables `[p, p+a)` of rank `N`; no sign. -/
def place (p : ℕ) (h : p + a ≤ N) : SkewPolynomial a →+* SkewPolynomial N where
  toFun := VariableEmbedding.embed (shiftEmb p h)
  map_zero' := VariableEmbedding.embed_zero _
  map_one' := VariableEmbedding.embed_one _
  map_add' := VariableEmbedding.embed_add _
  map_mul' := VariableEmbedding.embed_mul _

theorem place_monomial (p : ℕ) (h : p + a ≤ N) (γ : Fin a → ℕ) (c : ℤ) :
    place p h (monomial γ c) = monomial (VariableEmbedding.expEmbed (shiftEmb p h) γ) c :=
  VariableEmbedding.embed_monomial _ _ _

theorem expEmbed_eq_zero (p : ℕ) (h : p + a ≤ N) (γ : Fin a → ℕ) {t : Fin N}
    (ht : t.val < p ∨ p + a ≤ t.val) : VariableEmbedding.expEmbed (shiftEmb p h) γ t = 0 := by
  refine VariableEmbedding.expEmbed_not_mem_range _ _ _ ?_
  rintro ⟨j, rfl⟩
  simp only [shiftEmb_val] at ht
  omega

theorem expEmbed_expSingle (p : ℕ) (h : p + a ≤ N) (j : Fin a) :
    VariableEmbedding.expEmbed (shiftEmb p h) (OddMath.SkewPolynomial.expSingle j) =
      OddMath.SkewPolynomial.expSingle (shiftEmb p h j) := by
  funext t
  by_cases ht : t ∈ Set.range (shiftEmb p h)
  · obtain ⟨i, rfl⟩ := ht
    simp [OddMath.SkewPolynomial.expSingle, (shiftEmb p h).injective.eq_iff]
  · rw [VariableEmbedding.expEmbed_not_mem_range _ _ _ ht, OddMath.SkewPolynomial.expSingle,
      if_neg fun e => ht ⟨j, e⟩]

theorem place_generator (p : ℕ) (h : p + a ≤ N) (j : Fin a) :
    place p h (generator j) = generator (shiftEmb p h j) := by
  change place p h (monomial _ 1) = monomial _ 1
  rw [place_monomial, expEmbed_expSingle]

end Place

section Window
variable {m n p : ℕ} (h : p + (m+2) ≤ n+2)

theorem shiftIndex_castSucc (i : Fin (m+1)) :
    (OnhWindow.shiftIndex h i).castSucc = shiftEmb p h i.castSucc := Fin.ext rfl

theorem shiftIndex_succ (i : Fin (m+1)) :
    (OnhWindow.shiftIndex h i).succ = shiftEmb p h i.succ :=
  Fin.ext (by simp only [Fin.val_succ, OnhWindow.shiftIndex_val, shiftEmb_val]; omega)

/-- `∂_i` and `s_i` transported along a window. -/
theorem place_divided_and_s (i : Fin (m+1)) (f : SkewPolynomial (m+2)) :
    AllRankDivided.divided (OnhWindow.shiftIndex h i) (place p h f) =
        place p h (AllRankDivided.divided i f) ∧
      AllRankDivided.s (OnhWindow.shiftIndex h i) (place p h f) =
        place p h (AllRankDivided.s i f) := by
  induction f using PrefixEmbedding.induction_generators with
  | hconst r =>
      simp only [map_zsmul, map_one, AllRankDivided.divided_one, smul_zero, map_zero, and_self]
  | hgen j =>
      rw [place_generator, AllRankDivided.divided_generator, AllRankDivided.divided_generator,
        AllRankDivided.s_generator, AllRankDivided.s_generator, map_neg, place_generator,
        shiftIndex_castSucc, shiftIndex_succ, ← (shiftEmb p h).injective.swap_apply]
      simp only [(shiftEmb p h).injective.eq_iff, and_true]
      split <;> simp
  | hadd f g hf hg => simp only [map_add, hf.1, hf.2, hg.1, hg.2, and_self]
  | hmul f g hf hg =>
      simp only [map_mul, AllRankDivided.divided_mul, hf.1, hf.2, hg.1, hg.2, map_add, and_self]

theorem windowHom_zeroHecke (i : Fin (m+1)) :
    OnhWindow.windowHom m n p h (ZeroHecke.zeroHecke m i) =
      ZeroHecke.zeroHecke n (OnhWindow.shiftIndex h i) := by
  rw [ZeroHecke.zeroHecke, map_mul, OnhWindow.windowHom_dot, OnhWindow.windowHom_crossing,
    ZeroHecke.zeroHecke]
  rfl

theorem windowHom_zeroHeckeProduct (w : Word m) :
    OnhWindow.windowHom m n p h (ZeroHecke.zeroHeckeProduct w) =
      ZeroHecke.zeroHeckeProduct (w.map (OnhWindow.shiftIndex h)) := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [ZeroHecke.zeroHeckeProduct_cons, map_mul, ih, windowHom_zeroHecke, List.map_cons,
        ZeroHecke.zeroHeckeProduct_cons]

end Window

section Spectator
variable {n : ℕ}

theorem action_zeroHecke_apply (k : Fin (n+1)) (F : SkewPolynomial (n+2)) :
    action n (ZeroHecke.zeroHecke n k) F = generator k.castSucc * AllRankDivided.divided k F := by
  rw [ZeroHecke.zeroHecke, action_mul_apply, action_crossing_apply, action_dot_apply]

theorem action_zeroHecke_place {m p : ℕ} (h : p + (m+2) ≤ n+2) (i : Fin (m+1))
    (f : SkewPolynomial (m+2)) :
    action n (ZeroHecke.zeroHecke n (OnhWindow.shiftIndex h i)) (place p h f) =
      place p h (action m (ZeroHecke.zeroHecke m i) f) := by
  rw [action_zeroHecke_apply, action_zeroHecke_apply, (place_divided_and_s h i f).1, map_mul,
    place_generator, shiftIndex_castSucc]

/-- `g` passes `∂̄_k = x_k ∂_k` from the left. -/
def LeftSpect (k : Fin (n+1)) (g : SkewPolynomial (n+2)) : Prop :=
  ∀ F, action n (ZeroHecke.zeroHecke n k) (g * F) = g * action n (ZeroHecke.zeroHecke n k) F

/-- `g` passes `∂̄_k = x_k ∂_k` from the right. -/
def RightSpect (k : Fin (n+1)) (g : SkewPolynomial (n+2)) : Prop :=
  ∀ F, action n (ZeroHecke.zeroHecke n k) (F * g) = action n (ZeroHecke.zeroHecke n k) F * g

theorem leftSpect_generator {k : Fin (n+1)} {j : Fin (n+2)} (hl : j ≠ k.castSucc)
    (hr : j ≠ k.succ) : LeftSpect k (generator j) := fun F => by
  rw [action_zeroHecke_apply, action_zeroHecke_apply,
    AllRankDivided.divided_spectator_mul k j hl hr, neg_mul, mul_neg, ← mul_assoc, ← mul_assoc,
    show generator k.castSucc * generator j = -(generator j * generator k.castSucc) from
      OddMath.SkewPolynomial.generator_anticommute _ _ (Ne.symm hl), neg_mul, neg_neg]

theorem rightSpect_generator {k : Fin (n+1)} {j : Fin (n+2)} (hl : j ≠ k.castSucc)
    (hr : j ≠ k.succ) : RightSpect k (generator j) := fun F => by
  rw [action_zeroHecke_apply, action_zeroHecke_apply,
    AllRankDivided.divided_mul_spectator k j hl hr, mul_assoc]

theorem leftSpect_induction {k : Fin (n+1)} {a : ℕ} {E : SkewPolynomial a →+* SkewPolynomial (n+2)}
    (hE : ∀ j, LeftSpect k (E (generator j))) (f : SkewPolynomial a) : LeftSpect k (E f) := by
  induction f using PrefixEmbedding.induction_generators with
  | hconst r =>
      intro F
      rw [map_zsmul, map_one, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul, map_zsmul]
  | hgen j => exact hE j
  | hadd f g hf hg => intro F; simp only [map_add, add_mul, hf F, hg F]
  | hmul f g hf hg => intro F; simp only [map_mul, mul_assoc, hf _, hg F]

theorem rightSpect_induction {k : Fin (n+1)} {a : ℕ} {E : SkewPolynomial a →+* SkewPolynomial (n+2)}
    (hE : ∀ j, RightSpect k (E (generator j))) (f : SkewPolynomial a) : RightSpect k (E f) := by
  induction f using PrefixEmbedding.induction_generators with
  | hconst r =>
      intro F
      rw [map_zsmul, map_one, mul_smul_comm, mul_one, mul_smul_comm, mul_one, map_zsmul]
  | hgen j => exact hE j
  | hadd f g hf hg => intro F; simp only [map_add, mul_add, hf F, hg F]
  | hmul f g hf hg => intro F; simp only [map_mul, ← mul_assoc, hf _, hg _]

/-- A windowed 0-Hecke product acts on `g · ι(f) · r` through `f`, for spectators `g`, `r`. -/
theorem action_window_zeroHeckeProduct {m p : ℕ} (h : p + (m+2) ≤ n+2) (w : Word m)
    {g r : SkewPolynomial (n+2)} (hg : ∀ i, LeftSpect (OnhWindow.shiftIndex h i) g)
    (hr : ∀ i, RightSpect (OnhWindow.shiftIndex h i) r) (f : SkewPolynomial (m+2)) :
    action n (OnhWindow.windowHom m n p h (ZeroHecke.zeroHeckeProduct w)) (g * place p h f * r) =
      g * place p h (action m (ZeroHecke.zeroHeckeProduct w) f) * r := by
  rw [windowHom_zeroHeckeProduct]
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [List.map_cons, ZeroHecke.zeroHeckeProduct_cons, action_mul_apply, ih, mul_assoc,
        hg i, hr i, action_zeroHecke_place, ZeroHecke.zeroHeckeProduct_cons, action_mul_apply,
        mul_assoc]

end Spectator

/-! ## Two windows: `e_a ⊗ e_b` -/

section TwoWindows
variable {m₁ m₂ n : ℕ} (h : m₁ + 2 + (m₂ + 2) ≤ n + 2)

/-- `ι_a ⊗ ι_b`: the first factor on the strands `[0, a)`, the second on `[a, a+b)`. -/
def placeL : SkewPolynomial (m₁+2) →+* SkewPolynomial (n+2) := place 0 (by omega)

/-- The second factor of `ι_a ⊗ ι_b`. -/
def placeR : SkewPolynomial (m₂+2) →+* SkewPolynomial (n+2) := place (m₁+2) h

/-- `e_a ⊗ e_b ∈ ONH_{a+b}`, with `a = m₁+2`, `b = m₂+2`. -/
def twoWindow : Presented n :=
  OnhWindow.windowHom m₁ n 0 (by omega) (ZeroHecke.projector m₁) *
    OnhWindow.windowHom m₂ n (m₁+2) h (ZeroHecke.projector m₂)

theorem action_window_projector {m p : ℕ} (h' : p + (m+2) ≤ n+2)
    {g r : SkewPolynomial (n+2)} (hg : ∀ i, LeftSpect (OnhWindow.shiftIndex h' i) g)
    (hr : ∀ i, RightSpect (OnhWindow.shiftIndex h' i) r) (f : SkewPolynomial (m+2)) :
    action n (OnhWindow.windowHom m n p h' (ZeroHecke.projector m)) (g * place p h' f * r) =
      g * place p h' (action m (ZeroHecke.projector m) f) * r :=
  action_window_zeroHeckeProduct h' _ hg hr f

/-- `(e_a ⊗ e_b)(ι f · ι' g) = ι(e_a f) · ι'(e_b g)`: no sign, since each `x_r ∂_r` passes
a spectator variable with sign `(-1)^2`. -/
theorem action_twoWindow (f : SkewPolynomial (m₁+2)) (g : SkewPolynomial (m₂+2)) :
    action n (twoWindow h) (placeL h f * placeR h g) =
      placeL h (action m₁ (ZeroHecke.projector m₁) f) *
        placeR h (action m₂ (ZeroHecke.projector m₂) g) := by
  have hR : ∀ i : Fin (m₂+1), LeftSpect (OnhWindow.shiftIndex h i) (placeL h f) := fun i =>
    leftSpect_induction (fun j => by
      rw [placeL, place_generator]
      refine leftSpect_generator ?_ ?_ <;> intro e <;> have := congrArg Fin.val e <;>
        simp at this <;> omega) f
  have hL : ∀ i : Fin (m₁+1), RightSpect (OnhWindow.shiftIndex (p := 0) (by omega) i)
      (placeR h (action m₂ (ZeroHecke.projector m₂) g)) := fun i =>
    rightSpect_induction (fun j => by
      rw [placeR, place_generator]
      refine rightSpect_generator ?_ ?_ <;> intro e <;> have := congrArg Fin.val e <;>
        simp at this <;> omega) _
  have h1 : ∀ i : Fin (m₁+1), LeftSpect (OnhWindow.shiftIndex (p := 0) (by omega) i)
      (1 : SkewPolynomial (n+2)) := fun _ F => by rw [one_mul, one_mul]
  have h2 : ∀ i : Fin (m₂+1), RightSpect (OnhWindow.shiftIndex h i)
      (1 : SkewPolynomial (n+2)) := fun _ F => by rw [mul_one, mul_one]
  have s2 : action n (OnhWindow.windowHom m₂ n (m₁+2) h (ZeroHecke.projector m₂))
      (placeL h f * placeR h g * 1) =
        placeL h f * placeR h (action m₂ (ZeroHecke.projector m₂) g) * 1 :=
    action_window_projector h hR h2 g
  have s1 : action n (OnhWindow.windowHom m₁ n 0 (by omega) (ZeroHecke.projector m₁))
      (1 * placeL h f * placeR h (action m₂ (ZeroHecke.projector m₂) g)) =
        1 * placeL h (action m₁ (ZeroHecke.projector m₁) f) *
          placeR h (action m₂ (ZeroHecke.projector m₂) g) :=
    action_window_projector _ h1 hL f
  rw [twoWindow, action_mul_apply, ← mul_one (placeL h f * placeR h g), s2, mul_one,
    ← one_mul (placeL h f), s1, one_mul]

theorem hasDegree_window_projector {m p : ℕ} (h' : p + (m+2) ≤ n+2) :
    HasDegree (Vd (n+2)) 0 (action n (OnhWindow.windowHom m n p h' (ZeroHecke.projector m))) := by
  rw [ZeroHecke.projector, windowHom_zeroHeckeProduct]
  exact hasDegree_zeroHeckeProduct _

theorem hasDegree_twoWindow : HasDegree (Vd (n+2)) 0 (action n (twoWindow h)) := by
  have hd := hasDegree_action_mul (hasDegree_window_projector (m := m₁) (p := 0) (n := n)
    (by omega)) (hasDegree_window_projector h)
  rwa [add_zero] at hd

/-- The exponent vector `γ ⊕ η`. -/
def join (γ : Fin (m₁+2) → ℕ) (η : Fin (m₂+2) → ℕ) : Fin (n+2) → ℕ :=
  VariableEmbedding.expEmbed (shiftEmb 0 (by omega)) γ +
    VariableEmbedding.expEmbed (shiftEmb (m₁+2) h) η

theorem join_left (γ : Fin (m₁+2) → ℕ) (η : Fin (m₂+2) → ℕ) (j : Fin (m₁+2)) :
    join h γ η (shiftEmb 0 (by omega) j) = γ j := by
  rw [join, Pi.add_apply, VariableEmbedding.expEmbed_apply,
    expEmbed_eq_zero _ _ _ (Or.inl (by simp)), add_zero]

theorem join_right (γ : Fin (m₁+2) → ℕ) (η : Fin (m₂+2) → ℕ) (j : Fin (m₂+2)) :
    join h γ η (shiftEmb (m₁+2) h j) = η j := by
  rw [join, Pi.add_apply, VariableEmbedding.expEmbed_apply,
    expEmbed_eq_zero _ _ _ (Or.inr (by simp)), zero_add]

theorem join_inj {γ γ' : Fin (m₁+2) → ℕ} {η η' : Fin (m₂+2) → ℕ}
    (e : join h γ η = join h γ' η') : γ = γ' ∧ η = η' :=
  ⟨funext fun j => by rw [← join_left h γ η, e, join_left],
    funext fun j => by rw [← join_right h γ η, e, join_right]⟩

theorem weight_join (γ : Fin (m₁+2) → ℕ) (η : Fin (m₂+2) → ℕ) :
    ∑ t, join h γ η t = ∑ i, γ i + ∑ i, η i := by
  simp only [join, Pi.add_apply, Finset.sum_add_distrib]
  rw [VariableEmbedding.sum_range _ _ fun t ht => VariableEmbedding.expEmbed_not_mem_range _ _ _ ht,
    VariableEmbedding.sum_range _ _ fun t ht => VariableEmbedding.expEmbed_not_mem_range _ _ _ ht]
  simp only [VariableEmbedding.expEmbed_apply]

theorem crossingCount_join (γ : Fin (m₁+2) → ℕ) (η : Fin (m₂+2) → ℕ) :
    OddMath.crossingCount (VariableEmbedding.expEmbed (shiftEmb (N := n+2) 0 (by omega)) γ)
      (VariableEmbedding.expEmbed (shiftEmb (m₁+2) h) η) = 0 := by
  refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun u hu => ?_
  have hut : u < t := (Finset.mem_filter.mp hu).2
  rw [Fin.lt_def] at hut
  by_cases ht : t.val < m₁ + 2
  · rw [expEmbed_eq_zero (m₁+2) h η (t := u) (Or.inl (by omega)), mul_zero]
  · rw [expEmbed_eq_zero 0 _ γ (t := t) (Or.inr (by omega)), zero_mul]

theorem placeL_mul_placeR_monomial (γ : Fin (m₁+2) → ℕ) (η : Fin (m₂+2) → ℕ) (c c' : ℤ) :
    placeL h (monomial γ c) * placeR h (monomial η c') = monomial (join h γ η) (c * c') := by
  rw [placeL, placeR, place_monomial, place_monomial]
  change OddMath.SkewPolynomial.mul _ _ = _
  rw [OddMath.SkewPolynomial.mul_monomial, OddMath.skewSign, crossingCount_join, pow_zero,
    mul_one]
  rfl

theorem coeff_placeL_mul_placeR (F : SkewPolynomial (m₁+2)) (G : SkewPolynomial (m₂+2))
    (γ : Fin (m₁+2) → ℕ) (η : Fin (m₂+2) → ℕ) :
    (placeL h F * placeR h G) (join h γ η) = F γ * G η := by
  classical
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F F' hF hF' => rw [map_add, add_mul, Finsupp.add_apply, hF, hF', Finsupp.add_apply, add_mul]
  | single γ' c =>
      induction G using Finsupp.induction_linear with
      | zero => simp
      | add G G' hG hG' =>
          rw [map_add, mul_add, Finsupp.add_apply, hG, hG', Finsupp.add_apply, mul_add]
      | single η' c' =>
          rw [show Finsupp.single γ' c = monomial γ' c from rfl,
            show Finsupp.single η' c' = monomial η' c' from rfl, placeL_mul_placeR_monomial]
          simp only [monomial, Finsupp.single_apply]
          by_cases hγ : γ' = γ
          · by_cases hη : η' = η
            · simp [hγ, hη]
            · rw [if_neg fun e => hη (join_inj h e).2, if_neg hη, mul_zero]
          · rw [if_neg fun e => hγ (join_inj h e).1, if_neg hγ, zero_mul]

/-- Diagonal coefficient of `e_a ⊗ e_b` on `x^{γ ⊕ η}`. -/
theorem coeff_twoWindow (γ : Fin (m₁+2) → ℕ) (η : Fin (m₂+2) → ℕ) :
    action n (twoWindow h) (monomial (join h γ η) 1) (join h γ η) =
      action m₁ (ZeroHecke.projector m₁) (monomial γ 1) γ *
        action m₂ (ZeroHecke.projector m₂) (monomial η 1) η := by
  rw [show monomial (join h γ η) (1 : ℤ) = placeL h (monomial γ 1) * placeR h (monomial η 1) by
    rw [placeL_mul_placeR_monomial, mul_one], action_twoWindow, coeff_placeL_mul_placeR]

/-- Restriction of an exponent vector to the first window. -/
def splitL (ζ : Fin (n+2) → ℕ) : Fin (m₁+2) → ℕ := fun j => ζ (shiftEmb 0 (by omega) j)

/-- Restriction of an exponent vector to the second window. -/
def splitR (ζ : Fin (n+2) → ℕ) : Fin (m₂+2) → ℕ := fun j => ζ (shiftEmb (m₁+2) h j)

theorem splitL_join (γ : Fin (m₁+2) → ℕ) (η : Fin (m₂+2) → ℕ) : splitL h (join h γ η) = γ :=
  funext (join_left h γ η)

theorem splitR_join (γ : Fin (m₁+2) → ℕ) (η : Fin (m₂+2) → ℕ) : splitR h (join h γ η) = η :=
  funext (join_right h γ η)

end TwoWindows

theorem homog_zeroHeckeProduct {m : ℕ} (w : Word m) :
    OnhWindow.Homog 0 (m+2) (2 * w.length) (ZeroHecke.zeroHeckeProduct w) := by
  induction w with
  | nil => exact OnhWindow.Homog.one
  | cons i w ih =>
      have hm := ((OnhWindow.Homog.gen (OnhWindow.isGen_full_dot i.castSucc)).mul
        (OnhWindow.Homog.gen (OnhWindow.isGen_full_crossing i))).mul ih
      rw [show 1 + 1 + 2 * w.length = 2 * (i :: w).length by simp; ring] at hm
      exact hm

/-- `e_a ⊗ e_b` is idempotent: the two windows commute (`e_a` is even). -/
theorem twoWindow_mul_self {m₁ m₂ n : ℕ} (h : m₁ + 2 + (m₂ + 2) ≤ n + 2) :
    twoWindow h * twoWindow h = twoWindow h := by
  set E₁ := OnhWindow.windowHom m₁ n 0 (by omega) (ZeroHecke.projector m₁)
  set E₂ := OnhWindow.windowHom m₂ n (m₁+2) h (ZeroHecke.projector m₂)
  have hc : E₁ * E₂ = E₂ * E₁ := OnhWindow.windowHom_even_commute
    (homog_zeroHeckeProduct (LongestDivided.wordIn m₁ (m₁+2) le_rfl)) (even_two_mul _)
    (ZeroHecke.projector m₂) (by omega)
  change E₁ * E₂ * (E₁ * E₂) = E₁ * E₂
  calc E₁ * E₂ * (E₁ * E₂) = E₁ * (E₂ * E₁) * E₂ := by simp only [mul_assoc]
    _ = E₁ * E₁ * (E₂ * E₂) := by rw [← hc]; simp only [mul_assoc]
    _ = E₁ * E₂ := by
      simp only [E₁, E₂, ← map_mul, ZeroHecke.projector_mul_projector]

section TwoWindowTrace
variable {m₁ m₂ n : ℕ} (hN : m₁ + 2 + (m₂ + 2) = n + 2)

theorem join_split (ζ : Fin (n+2) → ℕ) : join hN.le (splitL hN.le ζ) (splitR hN.le ζ) = ζ := by
  funext t
  by_cases ht : t.val < m₁ + 2
  · have e : t = shiftEmb (N := n+2) 0 (by omega) (⟨t.val, ht⟩ : Fin (m₁+2)) := Fin.ext (by simp)
    rw [e]
    exact join_left _ _ _ _
  · have e : t = shiftEmb (m₁+2) hN.le (⟨t.val - (m₁+2), by omega⟩ : Fin (m₂+2)) :=
      Fin.ext (by simp; omega)
    rw [e]
    exact join_right _ _ _ _

/-- `tr(e_a ⊗ e_b | V_d) = ∑_{i+j=d} tr(e_a | V_i) · tr(e_b | V_j)`. -/
theorem trace_twoWindow (d : ℕ) :
    trace ℤ (Vd (n+2) d) ((hasDegree_twoWindow hN.le).res d d (add_zero _)) =
      ∑ ij ∈ Finset.antidiagonal d,
        trace ℤ (Vd (m₁+2) ij.1) (hasDegree_projector.res _ _ (add_zero _)) *
          trace ℤ (Vd (m₂+2) ij.2) (hasDegree_projector.res _ _ (add_zero _)) := by
  classical
  let A : (Fin (m₁+2) → ℕ) → ℤ := fun γ => action m₁ (ZeroHecke.projector m₁) (monomial γ 1) γ
  let B : (Fin (m₂+2) → ℕ) → ℤ := fun η => action m₂ (ZeroHecke.projector m₂) (monomial η 1) η
  let S : (Fin (n+2) → ℕ) → (ℕ × ℕ) × ((Fin (m₁+2) → ℕ) × (Fin (m₂+2) → ℕ)) := fun ζ =>
    ((∑ i, splitL hN.le ζ i, ∑ i, splitR hN.le ζ i), (splitL hN.le ζ, splitR hN.le ζ))
  have hφ : ∀ ζ, action n (twoWindow hN.le) (monomial ζ 1) ζ =
      A (splitL hN.le ζ) * B (splitR hN.le ζ) := fun ζ => by
    have hc := coeff_twoWindow hN.le (splitL hN.le ζ) (splitR hN.le ζ)
    rwa [join_split hN] at hc
  have hinj : Set.InjOn S (expSet (n+2) d) := fun ζ _ ζ' _ e => by
    simp only [S, Prod.mk.injEq] at e
    rw [← join_split hN ζ, ← join_split hN ζ', e.2.1, e.2.2]
  have hmem : ∀ q : (ℕ × ℕ) × ((Fin (m₁+2) → ℕ) × (Fin (m₂+2) → ℕ)),
      q ∈ (expSet (n+2) d).image S ↔
        q.1 ∈ Finset.antidiagonal d ∧ q.2 ∈ expSet (m₁+2) q.1.1 ×ˢ expSet (m₂+2) q.1.2 := by
    rintro ⟨⟨i, j⟩, γ, η⟩
    simp only [Finset.mem_image, Finset.mem_antidiagonal, Finset.mem_product, mem_expSet, S,
      Prod.mk.injEq, Nat.cast_inj]
    constructor
    · rintro ⟨ζ, hζ, ⟨rfl, rfl⟩, rfl, rfl⟩
      refine ⟨?_, rfl, rfl⟩
      rw [← weight_join, join_split hN]
      exact_mod_cast hζ
    · rintro ⟨hij, rfl, rfl⟩
      refine ⟨join hN.le γ η, ?_, ?_⟩
      · rw [weight_join, hij]
      · simp only [splitL_join, splitR_join, and_self]
  rw [trace_res_eq]
  refine (Finset.sum_congr rfl fun ζ _ => hφ ζ).trans ?_
  refine Eq.trans ?_ (Finset.sum_congr rfl fun ij _ => by rw [trace_res_eq, trace_res_eq])
  calc ∑ ζ ∈ expSet (n+2) d, A (splitL hN.le ζ) * B (splitR hN.le ζ)
      = ∑ q ∈ (expSet (n+2) d).image S, A q.2.1 * B q.2.2 := by rw [Finset.sum_image hinj]
    _ = ∑ ij ∈ Finset.antidiagonal d,
          ∑ q ∈ expSet (m₁+2) ij.1 ×ˢ expSet (m₂+2) ij.2, A q.1 * B q.2 :=
        Finset.sum_finset_product (f := fun q => A q.2.1 * B q.2.2) _ (Finset.antidiagonal d)
          (fun ij => expSet (m₁+2) ij.1 ×ˢ expSet (m₂+2) ij.2) hmem
    _ = ∑ ij ∈ Finset.antidiagonal d, (∑ γ ∈ expSet (m₁+2) ij.1, A γ) *
          ∑ η ∈ expSet (m₂+2) ij.2, B η :=
        Finset.sum_congr rfl fun ij _ => by rw [Finset.sum_product, Finset.sum_mul_sum]

/-- Rank form: `rk (e_a ⊗ e_b)(V_d) = ∑_{i+j=d} rk e_a(V_i) · rk e_b(V_j)`. -/
theorem finrank_map_twoWindow (d : ℕ) :
    finrank ℤ ((Vd (n+2) d).map (action n (twoWindow hN.le))) =
      ∑ ij ∈ Finset.antidiagonal d,
        finrank ℤ ((Vd (m₁+2) ij.1).map (action m₁ (ZeroHecke.projector m₁))) *
          finrank ℤ ((Vd (m₂+2) ij.2).map (action m₂ (ZeroHecke.projector m₂))) := by
  have hidem : action n (twoWindow hN.le) ∘ₗ action n (twoWindow hN.le) =
      action n (twoWindow hN.le) := by
    rw [← Module.End.mul_eq_comp, ← map_mul, twoWindow_mul_self]
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [← (hasDegree_twoWindow hN.le).trace_res hidem, trace_twoWindow hN]
  simp only [hasDegree_projector.trace_res projector_idem]

/-- Explicit form: the ranks of `e_a(V_i)` are those of the pieces of `OΛ_a`. -/
theorem trace_twoWindow_card (d : ℕ) :
    trace ℤ (Vd (n+2) d) ((hasDegree_twoWindow hN.le).res d d (add_zero _)) =
      ∑ ij ∈ Finset.antidiagonal d,
        (if (((m₁+2).choose 2 : ℕ) : ℤ) ≤ ij.1 then
          (Fintype.card (ElementaryBasis.Index (m₁+2)
            ((ij.1 : ℤ) - ((m₁+2).choose 2 : ℕ)).toNat) : ℤ)
          else 0) *
        (if (((m₂+2).choose 2 : ℕ) : ℤ) ≤ ij.2 then
          (Fintype.card (ElementaryBasis.Index (m₂+2)
            ((ij.2 : ℤ) - ((m₂+2).choose 2 : ℕ)).toNat) : ℤ)
          else 0) := by
  rw [trace_twoWindow hN]
  simp only [trace_projector]

end TwoWindowTrace

end
end OddMath.Frontier.ProjectorRank
