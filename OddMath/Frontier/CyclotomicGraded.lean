import OddMath.Frontier.CyclotomicMatrix
import OddMath.Frontier.OddCategorificationInduction

/-! # Graded cyclotomic quotients and their `K₀`
EKL arXiv:1111.1320v1, Proposition 5.2 (p. 45) and §6, last paragraph (p. 47); `a = n+2`.
Gradings in the paper normalization (a dot of degree `2`, a crossing of degree `-2`).

* `ohGrading`, `onhCycGrading`: the gradings of `OH_{a,N}` and `ONH_a^N` induced from `OΛ_a` and
  `ONH_a` (`imageGrading`). The generators `h_m` and `x̃_1^N` are homogeneous
  (`hK_mem_kerGrading`, `firstDot_pow_mem`), so both gradings are direct sum decompositions
  (`ohDecomposition`, `onhCycDecomposition`, from `UniqueDecomposition.image`).
* `prop_5_2_degree_iff`: Proposition 5.2 is graded; `x` has degree `d` iff the entry `(v, w)` has
  degree `d + 2ℓ(w) − 2ℓ(v)`. The reversal `rev = w₀` of EKL (2.55) preserves degrees.
* `ohConnected`: for `a ≤ N`, `OH_{a,N}` is connected ("graded local", p. 47): it vanishes in
  negative degrees, its degree `0` part is `ℤ · 1` (detected by the constant term,
  `eq_constOHN_of_mem`), and `ℤ → OH_{a,N}` is injective.
* `onhCycK0Equiv`: `K₀(ONH_a^N) ≃ ℤ[q,q⁻¹]` for `2 ≤ a ≤ N` (graded Morita invariance and the
  classification over `OH_{a,N}`), with `[ONH_a^N] ↦ ∑_{w ∈ S_a} q^{-2ℓ(w)}`;
  `K₀(ONH_a^N) = 0` for `a > N` (`onhCycK0_subsingleton`).
* `ONH1 N = ℤ[x]/(x^N)` (`a = 1`, connected for `N ≥ 1`) and `ONH_0^N = ℤ`. `K0Cyc N`,
  `K₀(ONH^N) = ⊕_{a=0}^{N} K₀(ONH_a^N)`, is free of rank `N + 1` over `ℤ[q,q⁻¹]`
  (`finrank_K0Cyc`).
-/

namespace OddMath.Frontier.Cyclotomic
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open GradedK0 OddCategorification NilHeckeGradedEnd NilCoxeterWords
open scoped BigOperators
noncomputable section

section ImageGrading
variable {R S : Type*} [Ring R] [Ring S]

/-- The image of a grading along a ring homomorphism. -/
def imageGrading (f : R →+* S) (A : ℤ → AddSubgroup R) (d : ℤ) : AddSubgroup S :=
  (A d).map f.toAddMonoidHom

theorem mem_imageGrading {f : R →+* S} {A : ℤ → AddSubgroup R} {d : ℤ} {y : S} :
    y ∈ imageGrading f A d ↔ ∃ x ∈ A d, f x = y := Iff.rfl

theorem map_mem_imageGrading (f : R →+* S) {A : ℤ → AddSubgroup R} {d : ℤ} {x : R}
    (hx : x ∈ A d) : f x ∈ imageGrading f A d := ⟨x, hx, rfl⟩

instance imageGrading.gradedMonoid (f : R →+* S) (A : ℤ → AddSubgroup R)
    [SetLike.GradedMonoid A] : SetLike.GradedMonoid (imageGrading f A) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one f⟩
  mul_mem _ _ _ _ := by
    rintro ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, SetLike.GradedMul.mul_mem hx hy, map_mul f x y⟩

/-- The image of a connected grading is connected once `ℤ → S` is injective. -/
theorem imageGrading_connected (f : R →+* S) {A : ℤ → AddSubgroup R} (hA : Connected A)
    (hinj : Function.Injective (Int.cast : ℤ → S)) : Connected (imageGrading f A) where
  neg d hd := by
    rintro _ ⟨x, hx, rfl⟩
    change f x = 0
    rw [hA.neg d hd x hx, map_zero]
  zero := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hA.zero x hx
    exact ⟨z, (map_intCast f z).symm⟩
  inj := hinj

end ImageGrading

/-! ### Homogeneity -/

section Homogeneity
open NilHeckeAction NilHeckeGrading

/-- A ring endomorphism of `OPol` sending generators to degree `2` preserves degrees. -/
theorem ringHom_mem_polynomialPiece {N : ℕ} (φ : SkewPolynomial N →+* SkewPolynomial N)
    (hφ : ∀ j, φ (generator j) ∈ polynomialPiece N 2) {d : ℤ} {f : SkewPolynomial N}
    (hf : f ∈ polynomialPiece N d) : φ f ∈ polynomialPiece N d := by
  have hw : ∀ w : List (Fin N), φ (OddMath.PbwL3.Phi N (PbwRealization.word w)) ∈
      polynomialPiece N (2*(w.length : ℤ)) := by
    intro w
    induction w with
    | nil => simpa [PbwRealization.word] using NilHeckeGradedEnd.one_mem N
    | cons j w ih =>
      have h := polynomial_mul (hφ j) ih
      simpa [PbwRealization.word, OddMath.PbwL3.Phi_q, Nat.cast_add, mul_add, add_comm] using h
  rw [← Finsupp.sum_single f, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun a ha => ?_
  have hl : ((PbwRealization.orderedList a).length : ℕ) = ∑ j, a j := by
    rw [← ElementaryBasis.weight_exponents, PbwRealization.exponents_orderedList]
  rw [← support_degree hf ha]
  change φ (monomial a (f a)) ∈ _
  rw [← PbwRealization.Phi_smul_word, map_zsmul, map_zsmul]
  exact (polynomialPiece _ _).smul_mem _
    (by simpa only [hl] using hw (PbwRealization.orderedList a))

/-- The reversal `rev = w₀` of EKL (2.55) preserves degrees. -/
theorem revK_mem_kerGrading_iff (n : ℕ) (d : ℤ) (k : K n) :
    revK n k ∈ kerGrading n d ↔ k ∈ kerGrading n d := by
  have h : ∀ k : K n, k ∈ kerGrading n d → revK n k ∈ kerGrading n d := fun k hk =>
    ringHom_mem_polynomialPiece
      (SignedPermutation.skewAction (LongestElementary.longest (n+2))).toRingHom
      (fun j => by
        change SignedPermutation.skewAction _ (generator j) ∈ _
        rw [SignedPermutation.action_generator]
        exact (polynomialPiece _ _).smul_mem _ (generator_mem _)) hk
  exact ⟨fun hk => revK_revK n k ▸ h _ hk, h k⟩

theorem list_prod_mem {N : ℕ} (l : List (SkewPolynomial N))
    (hl : ∀ x ∈ l, x ∈ polynomialPiece N 2) :
    l.prod ∈ polynomialPiece N (2*(l.length : ℤ)) := by
  induction l with
  | nil => simpa using NilHeckeGradedEnd.one_mem N
  | cons x l ih =>
    have h := polynomial_mul (hl x List.mem_cons_self)
      (ih fun y hy => hl y (List.mem_cons_of_mem _ hy))
    simpa [Nat.cast_add, mul_add, add_comm] using h

theorem tildeGenerator_mem {N : ℕ} (i : Fin N) :
    PlacticEvaluation.tildeGenerator i ∈ polynomialPiece N 2 :=
  (polynomialPiece _ _).smul_mem _ (generator_mem i)

/-- `h_m` is homogeneous of degree `2m`. -/
theorem hK_mem_kerGrading (n m : ℕ) : hK n m ∈ kerGrading n (2*(m : ℤ)) := by
  change FiniteCompleteElementary.completePoly (n+2) m ∈ polynomialPiece (n+2) _
  refine Submodule.sum_mem _ fun f _ => ?_
  split_ifs
  · simpa using list_prod_mem (List.ofFn fun i => PlacticEvaluation.tildeGenerator (f i))
      (by simp [List.mem_ofFn, tildeGenerator_mem])
  · exact Submodule.zero_mem _

/-- `x̃_1^N` is homogeneous of degree `2N`. -/
theorem firstDot_pow_mem (n N : ℕ) : firstDot n ^ N ∈ onhGrading n (2*(N : ℤ)) := by
  induction N with
  | zero => simpa using unit_mem (n := n)
  | succ N ih =>
    rw [pow_succ]
    have h := degreePiece_mul ih (dot_mem (n := n) 0)
    convert h using 2

end Homogeneity


/-! ### Homogeneous decompositions -/

section Decomposition

/-- Every element is uniquely a finite sum of homogeneous elements (the convention of
`NilHeckeGrading.unique_homogeneous_decomposition`): the grading is a direct sum decomposition. -/
def UniqueDecomposition {R : Type*} [AddCommGroup R] (A : ℤ → AddSubgroup R) : Prop :=
  ∀ x : R, ∃! f : ℤ →₀ R, (∀ d, f d ∈ A d) ∧ f.sum (fun _ y => y) = x

variable {R R' S : Type*}

theorem uniqueDecomposition_of_indep [AddCommGroup R] {A : ℤ → AddSubgroup R}
    (hspan : ∀ x : R, ∃ f : ℤ →₀ R, (∀ d, f d ∈ A d) ∧ f.sum (fun _ y => y) = x)
    (hind : ∀ f : ℤ →₀ R, (∀ d, f d ∈ A d) → f.sum (fun _ y => y) = 0 → f = 0) :
    UniqueDecomposition A := by
  intro x
  obtain ⟨f, hf, hfx⟩ := hspan x
  refine ⟨f, ⟨hf, hfx⟩, fun g ⟨hg, hgx⟩ => sub_eq_zero.1 (hind (g - f) (fun d => ?_) ?_)⟩
  · rw [Finsupp.sub_apply]
    exact sub_mem (hg d) (hf d)
  · rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), hgx, hfx, sub_self]

namespace UniqueDecomposition

section Additive
variable [AddCommGroup R] [AddCommGroup R'] {A : ℤ → AddSubgroup R} {A' : ℤ → AddSubgroup R'}

theorem eq_zero (hA : UniqueDecomposition A) {f : ℤ →₀ R} (hf : ∀ d, f d ∈ A d)
    (hs : f.sum (fun _ y => y) = 0) : f = 0 :=
  (hA 0).unique ⟨hf, hs⟩ ⟨fun _ => zero_mem _, Finsupp.sum_zero_index⟩

/-- Transport along an additive retraction compatible with the gradings. -/
theorem of_retract (hA : UniqueDecomposition A) (φ : R' →+ R) (ψ : R →+ R')
    (hψφ : ∀ x, ψ (φ x) = x) (hφ : ∀ d x, x ∈ A' d → φ x ∈ A d)
    (hψ : ∀ d x, x ∈ A d → ψ x ∈ A' d) : UniqueDecomposition A' := by
  refine uniqueDecomposition_of_indep (fun x => ?_) (fun f hf hs => ?_)
  · obtain ⟨g, ⟨hg, hgx⟩, -⟩ := hA (φ x)
    refine ⟨g.mapRange ψ (map_zero ψ), fun d => ?_, ?_⟩
    · rw [Finsupp.mapRange_apply]
      exact hψ d _ (hg d)
    · rw [Finsupp.sum_mapRange_index (fun _ => rfl), ← hψφ x, ← hgx, map_finsuppSum]
  · have h := hA.eq_zero (f := f.mapRange φ (map_zero φ))
      (fun d => by rw [Finsupp.mapRange_apply]; exact hφ d _ (hf d))
      (by rw [Finsupp.sum_mapRange_index (fun _ => rfl), ← map_finsuppSum, hs, map_zero])
    ext d
    have := congrArg (fun g => ψ (g d)) h
    simpa [hψφ] using this

end Additive

section Ring
variable [Ring R] [Ring S] {A : ℤ → AddSubgroup R} (hA : UniqueDecomposition A)

/-- The homogeneous components. -/
def dec (x : R) : ℤ →₀ R := (hA x).exists.choose

theorem dec_mem (x : R) (d : ℤ) : hA.dec x d ∈ A d := (hA x).exists.choose_spec.1 d

theorem dec_sum (x : R) : (hA.dec x).sum (fun _ y => y) = x := (hA x).exists.choose_spec.2

theorem dec_eq {x : R} {f : ℤ →₀ R} (hf : ∀ d, f d ∈ A d) (hfx : f.sum (fun _ y => y) = x) :
    hA.dec x = f :=
  (hA x).unique ⟨hA.dec_mem x, hA.dec_sum x⟩ ⟨hf, hfx⟩

theorem dec_of_mem {x : R} {e : ℤ} (hx : x ∈ A e) : hA.dec x = Finsupp.single e x := by
  refine hA.dec_eq (fun d => ?_) (Finsupp.sum_single_index rfl)
  by_cases h : e = d
  · subst h
    rwa [Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne h]
    exact zero_mem _

/-- The homogeneous components, as an additive map. -/
def decHom : R →+ (ℤ →₀ R) where
  toFun := hA.dec
  map_zero' := hA.dec_eq (fun _ => zero_mem _) Finsupp.sum_zero_index
  map_add' x y := hA.dec_eq (fun d => add_mem (hA.dec_mem x d) (hA.dec_mem y d))
    (by rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hA.dec_sum, hA.dec_sum])

variable [SetLike.GradedMonoid A]

theorem dec_mul (x y : R) : hA.dec (x * y) = ∑ a ∈ (hA.dec x).support, ∑ b ∈ (hA.dec y).support,
    Finsupp.single (a + b) (hA.dec x a * hA.dec y b) := by
  conv_lhs => rw [← hA.dec_sum x, ← hA.dec_sum y, Finsupp.sum, Finsupp.sum, Finset.sum_mul_sum]
  change hA.decHom _ = _
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact hA.dec_of_mem (SetLike.GradedMul.mul_mem (hA.dec_mem x a) (hA.dec_mem y b))

/-- A two-sided ideal generated by homogeneous elements contains the components of its
elements. -/
theorem dec_mem_span {G : Set R} (hG : ∀ g ∈ G, ∃ e, g ∈ A e) {x : R}
    (hx : x ∈ TwoSidedIdeal.span G) (d : ℤ) : hA.dec x d ∈ TwoSidedIdeal.span G := by
  set I := TwoSidedIdeal.span G
  let I' : TwoSidedIdeal R := TwoSidedIdeal.mk' {x | ∀ d, hA.dec x d ∈ I}
    (fun d => by
      change hA.decHom 0 d ∈ I
      rw [map_zero, Finsupp.zero_apply]
      exact I.zero_mem)
    (fun {x y} hx hy d => by
      change hA.decHom (x + y) d ∈ I
      rw [map_add, Finsupp.add_apply]
      exact I.add_mem (hx d) (hy d))
    (fun {x} hx d => by
      change hA.decHom (-x) d ∈ I
      rw [map_neg, Finsupp.neg_apply]
      exact I.neg_mem (hx d))
    (fun {x y} hy d => by
      rw [dec_mul, Finset.sum_apply']
      refine sum_mem fun a _ => ?_
      rw [Finset.sum_apply']
      refine sum_mem fun b _ => ?_
      rw [Finsupp.single_apply]
      split_ifs
      · exact I.mul_mem_left _ _ (hy b)
      · exact I.zero_mem)
    (fun {x y} hx d => by
      rw [dec_mul, Finset.sum_apply']
      refine sum_mem fun a _ => ?_
      rw [Finset.sum_apply']
      refine sum_mem fun b _ => ?_
      rw [Finsupp.single_apply]
      split_ifs
      · exact I.mul_mem_right _ _ (hx a)
      · exact I.zero_mem)
  have hle : I ≤ I' := by
    rw [TwoSidedIdeal.span_le]
    intro g hg
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]
    intro d
    obtain ⟨e, he⟩ := hG g hg
    rw [hA.dec_of_mem he, Finsupp.single_apply]
    split_ifs
    · exact TwoSidedIdeal.subset_span hg
    · exact I.zero_mem
  have h := hle hx
  rw [TwoSidedIdeal.mem_mk'] at h
  exact h d

include hA in
/-- **Quotients by homogeneous ideals are graded**: if a two-sided ideal is generated by
homogeneous elements, the image grading of the quotient is a direct sum decomposition. -/
theorem image (π : R →+* S) (hπ : Function.Surjective π) {G : Set R}
    (hG : ∀ g ∈ G, ∃ e, g ∈ A e) (hker : ∀ x, π x = 0 ↔ x ∈ TwoSidedIdeal.span G) :
    UniqueDecomposition (imageGrading π A) := by
  classical
  refine uniqueDecomposition_of_indep (fun y => ?_) (fun f hf hs => ?_)
  · obtain ⟨x, rfl⟩ := hπ y
    refine ⟨(hA.dec x).mapRange π (map_zero π), fun d => ?_, ?_⟩
    · rw [Finsupp.mapRange_apply]
      exact map_mem_imageGrading π (hA.dec_mem x d)
    · rw [Finsupp.sum_mapRange_index (fun _ => rfl), ← map_finsuppSum, hA.dec_sum]
  · choose ℓ hℓ hℓf using hf
    replace hℓf : ∀ d, π (ℓ d) = f d := hℓf
    let F : ℤ →₀ R := Finsupp.onFinset f.support (fun d => if d ∈ f.support then ℓ d else 0)
      (fun d h => by by_contra hd; exact h (if_neg hd))
    have hF (d : ℤ) : F d = if d ∈ f.support then ℓ d else 0 := Finsupp.onFinset_apply
    have hFm (d : ℤ) : F d ∈ A d := by
      rw [hF]
      split_ifs
      · exact hℓ d
      · exact zero_mem _
    have hFs : π (F.sum fun _ y => y) = 0 := by
      rw [Finsupp.onFinset_sum _ (fun _ => rfl), map_sum, ← hs, Finsupp.sum]
      exact Finset.sum_congr rfl fun d hd => by rw [if_pos hd, hℓf]
    have hdec := hA.dec_eq hFm rfl
    ext d
    rw [Finsupp.zero_apply]
    by_cases hd : d ∈ f.support
    · have h := (hker _).2 (hA.dec_mem_span hG ((hker _).1 hFs) d)
      rwa [hdec, hF, if_pos hd, hℓf] at h
    · exact Finsupp.not_mem_support_iff.1 hd

end Ring
end UniqueDecomposition
end Decomposition

/-! ### The gradings of `OH_{a,N}` and `ONH_a^N` -/

/-- The grading of `OH_{a,N}` (`a = n+2`) induced from `OΛ_a`: `h_m` is homogeneous. -/
def ohGrading (n N : ℕ) : ℤ → AddSubgroup (OH n N) := imageGrading (toOH n N) (kerGrading n)

/-- The grading of `ONH_a^N` (`a = n+2`) induced from `ONH_a`: `x̃_1^N` is homogeneous. -/
def onhCycGrading (n N : ℕ) : ℤ → AddSubgroup (ONH n N) :=
  imageGrading (toONH n N) (onhGrading n)

instance (n N : ℕ) : SetLike.GradedMonoid (ohGrading n N) :=
  imageGrading.gradedMonoid _ _

instance (n N : ℕ) : SetLike.GradedMonoid (onhCycGrading n N) :=
  imageGrading.gradedMonoid _ _

theorem cor214_eq_onhIso (n : ℕ) : cor214 n = onhIso n := rfl

/-- **EKL Proposition 5.2, graded** (p. 45): `ONH_a^N ≅ Mat_{a!}(OH_{a,N})` is degree-preserving
when the entry `(v, w)` is shifted by `2ℓ(w) − 2ℓ(v)`, i.e. for the grading of
`End(⊕_{w ∈ S_a} OH_{a,N}{−2ℓ(w)})`, a free module of graded rank `∑_{w ∈ S_a} q^{±2ℓ(w)} =
q^{±C(a,2)}[a]!` (`onhCycK0Equiv_one_qFact`). -/
theorem prop_5_2_degree_iff (n N : ℕ) (d : ℤ) (x : ONH n N) :
    x ∈ onhCycGrading n N d ↔
      ∀ v w, prop_5_2 n N x v w ∈
        ohGrading n N (d + 2*(length w : ℤ) - 2*(length v : ℤ)) := by
  constructor
  · rintro ⟨T, hT, rfl⟩ v w
    have h := (mem_onhGrading_iff n d T).1 hT v w
    rw [lenShift, lenShift, ← cor214_eq_onhIso] at h
    refine ⟨revK n (cor214 n T v w), (revK_mem_kerGrading_iff n _ _).2 ?_,
      (prop_5_2_apply n N T v w).symm⟩
    convert h using 2
    ring
  · intro h
    choose k hk hkx using h
    set T := (cor214 n).symm (fun v w => revK n (k v w))
    have hT : cor214 n T = fun v w => revK n (k v w) := RingEquiv.apply_symm_apply _ _
    refine ⟨T, (mem_onhGrading_iff n d T).2 fun v w => ?_, (prop_5_2 n N).injective ?_⟩
    · rw [← cor214_eq_onhIso, hT, lenShift, lenShift]
      convert (revK_mem_kerGrading_iff n _ _).2 (hk v w) using 2
      ring
    · ext v w
      change prop_5_2 n N (toONH n N T) v w = _
      rw [prop_5_2_apply, hT, revK_revK, ← hkx v w]
      rfl

/-- Graded Proposition 5.2 for the matrix grading `matGrading` with shifts `2ℓ(w)`. -/
theorem prop_5_2_mem_matGrading (n N : ℕ) (d : ℤ) (x : ONH n N) :
    x ∈ onhCycGrading n N d ↔ prop_5_2 n N x ∈ matGrading (ohGrading n N) (lenShift n) d := by
  rw [prop_5_2_degree_iff, mem_matGrading]
  refine forall_congr' fun v => forall_congr' fun w => ?_
  rw [lenShift, lenShift, show d - 2 * (length v : ℤ) + 2 * (length w : ℤ) =
    d + 2 * (length w : ℤ) - 2 * (length v : ℤ) by ring]

/-! ### The gradings are direct sum decompositions -/

theorem onhDecomposition (n : ℕ) : UniqueDecomposition (onhGrading n) :=
  fun x => NilHeckeGrading.unique_homogeneous_decomposition x

/-- `OΛ_a` is a graded retract of `ONH_a`: scalar matrices, and the `(1,1)` entry, in the
coordinates of Corollary 2.14. -/
theorem kerDecomposition (n : ℕ) : UniqueDecomposition (kerGrading n) := by
  refine (onhDecomposition n).of_retract
    ((onhIso n).symm.toRingHom.comp (Matrix.scalar (Perm n))).toAddMonoidHom
    (AddMonoidHom.mk' (fun T => onhIso n T 1 1) fun T U => by
      simp only [map_add, Matrix.add_apply])
    (fun k => ?_) (fun d k hk => ?_) (fun d T hT => ?_)
  · change onhIso n ((onhIso n).symm (Matrix.scalar (Perm n) k)) 1 1 = k
    rw [RingEquiv.apply_symm_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  · change (onhIso n).symm (Matrix.scalar (Perm n) k) ∈ onhGrading n d
    rw [mem_onhGrading_iff, RingEquiv.apply_symm_apply, mem_matGrading]
    intro i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      rwa [sub_add_cancel]
    · exact zero_mem _
  · have h := (mem_onhGrading_iff n d T).1 hT 1 1
    rwa [sub_add_cancel] at h

/-- The grading of `OH_{a,N}` is a direct sum decomposition: `⟨h_m : m > N − a⟩` is generated by
homogeneous elements. -/
theorem ohDecomposition (n N : ℕ) : UniqueDecomposition (ohGrading n N) :=
  (kerDecomposition n).image (toOH n N) (toOH_surjective n N) (G := grassmannianGenerators n N)
    (by rintro _ ⟨m, -, rfl⟩; exact ⟨_, hK_mem_kerGrading n m⟩) (toOH_eq_zero_iff n N)

/-- The grading of `ONH_a^N` is a direct sum decomposition: `x̃_1^N` is homogeneous. -/
theorem onhCycDecomposition (n N : ℕ) : UniqueDecomposition (onhCycGrading n N) :=
  (onhDecomposition n).image (toONH n N) (toONH_surjective n N) (G := {firstDot n ^ N})
    (by rintro _ rfl; exact ⟨_, firstDot_pow_mem n N⟩) (toONH_eq_zero_iff n N)

/-! ### `OH_{a,N}` is connected -/

theorem grassmannianIdeal_le_ker (n N : ℕ) (h : n+2 ≤ N) :
    grassmannianIdeal n N ≤ TwoSidedIdeal.ker (constK n) := by
  rw [grassmannianIdeal, TwoSidedIdeal.span_le]
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ m by omega)
  rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
  exact constTerm_completePoly (n+2) m

/-- The constant term `OH_{a,N} → ℤ`, for `a ≤ N`. -/
def constOHN (n N : ℕ) (h : n+2 ≤ N) : OH n N →+* ℤ :=
  Ideal.Quotient.lift _ (constK n) (fun _ ha =>
    (TwoSidedIdeal.mem_ker _).mp (grassmannianIdeal_le_ker n N h (TwoSidedIdeal.mem_asIdeal.mp ha)))

theorem constOHN_toOH (n N : ℕ) (h : n+2 ≤ N) (x : K n) :
    constOHN n N h (toOH n N x) = constK n x := rfl

/-- `ℤ → OH_{a,N}` is injective for `a ≤ N`. -/
theorem intCast_OH_injective (n N : ℕ) (h : n+2 ≤ N) :
    Function.Injective (Int.cast : ℤ → OH n N) := fun a b hab => by
  simpa using congrArg (constOHN n N h) hab

/-- **`OH_{a,N}` is graded local** (EKL §6, p. 47), made precise over `ℤ`: for `a ≤ N` the grading
is connected (nothing in negative degrees, degree `0` is `ℤ · 1`, and `ℤ → OH_{a,N}` is
injective). -/
theorem ohConnected (n N : ℕ) (h : n+2 ≤ N) : Connected (ohGrading n N) :=
  imageGrading_connected _ (kerConnected n) (intCast_OH_injective n N h)

/-- The degree-zero part of `OH_{a,N}` is `ℤ`, detected by the constant term. -/
theorem eq_constOHN_of_mem (n N : ℕ) (h : n+2 ≤ N) {x : OH n N} (hx : x ∈ ohGrading n N 0) :
    x = (constOHN n N h x : OH n N) := by
  obtain ⟨z, rfl⟩ := (ohConnected n N h).zero x hx
  rw [map_intCast, Int.cast_id]

/-! ### `K₀(ONH_a^N)` -/

/-- `K₀` of a graded ring that is the zero ring vanishes. -/
theorem K0_subsingleton {R : Type*} [Ring R] [Subsingleton R] (A : ℤ → AddSubgroup R)
    [SetLike.GradedMonoid A] : Subsingleton (K0 A) := by
  have hP (P : GIdem A) : K0.of P = 0 := by
    rw [← K0.of_zero]
    refine K0.of_eq ⟨0, 0, fun _ _ => zero_mem _, fun _ _ => zero_mem _, ?_, ?_, ?_, ?_⟩ <;>
      exact Subsingleton.elim _ _
  have h : AddMonoidHom.id (K0 A) = 0 := K0.hom_ext fun P => hP P
  exact ⟨fun x y => by
    rw [← AddMonoidHom.id_apply (K0 A) x, ← AddMonoidHom.id_apply (K0 A) y, h]; rfl⟩

/-- `K₀(ONH_a^N) ≃ ℤ[q,q⁻¹]` for `2 ≤ a ≤ N` (EKL §6, p. 47): graded Proposition 5.2, graded
Morita invariance, and the classification of graded projectives over the connected `OH_{a,N}`. -/
def onhCycK0Equiv (n N : ℕ) (h : n+2 ≤ N) :
    K0 (onhCycGrading n N) ≃ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  (k0Equiv (prop_5_2 n N) (prop_5_2_mem_matGrading n N)).trans
    (K0.morita.trans (K0.classify (ohConnected n N h)))

/-- `[ONH_a^N] ↦ ∑_{w ∈ S_a} q^{-2ℓ(w)}`. -/
theorem onhCycK0Equiv_one (n N : ℕ) (h : n+2 ≤ N) :
    onhCycK0Equiv n N h (K0.of (GIdem.single 0)) =
      ∑ w : Perm n, LaurentPolynomial.T (-(2 * (length w : ℤ))) := by
  simp only [onhCycK0Equiv, LinearEquiv.trans_apply, k0Equiv_of, K0.morita_of, K0.classify_of]
  rw [← gdimAux_eq_of_mvn (ohConnected n N h) (GIdem.mvn_flatten _)]
  have h1 : (gmap (prop_5_2 n N) (prop_5_2_mem_matGrading n N) (GIdem.single 0)).e = 1 := by
    show (1 : Matrix (Fin 1) (Fin 1) (ONH n N)).map (prop_5_2 n N) = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : flat (gmap (prop_5_2 n N) (prop_5_2_mem_matGrading n N) (GIdem.single 0)).e = 1 := by
    rw [h1]
    exact (Matrix.compRingEquiv (Fin 1) (Perm n) (OH n N)).map_one
  rw [h2, gdimAux_one (ohConnected n N h), Fintype.sum_prod_type]
  erw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [gmap, GIdem.single, GIdem.free, lenShift]

/-- `[ONH_a^N] ↦ q^{-C(a,2)} [a]!`: the graded size `q^{C(a,2)}[a]!` of the matrix ring of EKL
p. 45, the sign of the exponent being that of the shift convention of `GradedK0`. -/
theorem onhCycK0Equiv_one_qFact (n N : ℕ) (h : n+2 ≤ N) :
    onhCycK0Equiv n N h (K0.of (GIdem.single 0)) =
      LaurentPolynomial.T (-(((n+2).choose 2 : ℕ) : ℤ)) * QuantumSl2Plus.qFact (n+2) := by
  rw [onhCycK0Equiv_one, sum_T_length_eq, ← sum_Sq_eq_qFact, Finset.mul_sum,
    Finset.sum_coe_sort (BoxPartitionCount.Sq (n+2)) fun ℓ =>
      (LaurentPolynomial.T (-(2 * ((∑ ν, ℓ ν : ℕ) : ℤ))) : LaurentPolynomial ℤ)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← LaurentPolynomial.T_add]
  congr 1
  ring

/-- `K₀(ONH_a^N) = 0` for `a > N`. -/
theorem onhCycK0_subsingleton {n N : ℕ} (h : N < n+2) : Subsingleton (K0 (onhCycGrading n N)) :=
  haveI := ONH_subsingleton h
  K0_subsingleton _

/-! ### `ONH_0^N = ℤ` and `ONH_1^N = ℤ[x]/(x^N)` -/

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) opolNonUnitalNonAssocRing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-- `⟨x^N⟩ ⊂ ONH_1 = OPol_1`. -/
def cyc1Ideal (N : ℕ) : TwoSidedIdeal (SkewPolynomial 1) :=
  TwoSidedIdeal.span {(generator 0 : SkewPolynomial 1) ^ N}

/-- `ONH_1^N = OPol_1/⟨x^N⟩ = ℤ[x]/(x^N)`. -/
def ONH1 (N : ℕ) : Type := SkewPolynomial 1 ⧸ (cyc1Ideal N).asIdeal

instance (N : ℕ) : Ring (ONH1 N) := Ideal.Quotient.ring _

/-- The quotient map `ONH_1 → ONH_1^N`. -/
def toONH1 (N : ℕ) : SkewPolynomial 1 →+* ONH1 N := Ideal.Quotient.mk _

/-- The grading of `ONH_1^N` induced from `OPol_1`. -/
def onh1Grading (N : ℕ) : ℤ → AddSubgroup (ONH1 N) := imageGrading (toONH1 N) opolGrading

instance (N : ℕ) : SetLike.GradedMonoid (onh1Grading N) := imageGrading.gradedMonoid _ _

/-- `x^N` is homogeneous of degree `2N`. -/
theorem generator_pow_mem (N : ℕ) :
    (generator 0 : SkewPolynomial 1) ^ N ∈ opolGrading (2*(N : ℤ)) := by
  induction N with
  | zero => simpa using NilHeckeGradedEnd.one_mem 1
  | succ N ih =>
    rw [pow_succ]
    have h := polynomial_mul ih (generator_mem (0 : Fin 1))
    convert h using 2

/-- `OPol` is graded by polynomial degree. -/
theorem polynomialDecomposition (N : ℕ) :
    UniqueDecomposition fun d => (polynomialPiece N d).toAddSubgroup := by
  refine uniqueDecomposition_of_indep (fun f => ?_) (fun F hF hs => ?_)
  · classical
    refine ⟨∑ a ∈ f.support, Finsupp.single (pdegree a) (monomial a (f a)), fun d => ?_, ?_⟩
    · rw [Finset.sum_apply']
      refine sum_mem fun a _ => ?_
      rw [Finsupp.single_apply]
      split_ifs with h
      · exact h ▸ monomial_mem a (f a)
      · exact zero_mem _
    · rw [← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
      simp only [Finsupp.sum_single_index]
      exact Finsupp.sum_single f
  · have hc (d : ℤ) (a : Fin N → ℕ) (h : pdegree a ≠ d) : F d a = 0 := hF d a h
    ext d a
    rw [Finsupp.zero_apply, Finsupp.zero_apply]
    by_cases h : pdegree a = d
    · subst h
      have := congrArg (fun g : SkewPolynomial N => g a) hs
      simp only [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.zero_apply] at this
      rwa [Finset.sum_eq_single (pdegree a) (fun e _ he => hc e a (Ne.symm he))
        (fun hn => by rw [Finsupp.not_mem_support_iff.1 hn, Finsupp.zero_apply])] at this
    · exact hc d a h

/-- The grading of `ONH_1^N` is a direct sum decomposition. -/
theorem onh1Decomposition (N : ℕ) : UniqueDecomposition (onh1Grading N) :=
  UniqueDecomposition.image (A := opolGrading) (polynomialDecomposition 1) (toONH1 N)
    Ideal.Quotient.mk_surjective
    (G := {(generator 0 : SkewPolynomial 1) ^ N}) (by rintro _ rfl; exact ⟨_, generator_pow_mem N⟩)
    (fun _ => Ideal.Quotient.eq_zero_iff_mem.trans TwoSidedIdeal.mem_asIdeal)

theorem cyc1Ideal_le_ker {N : ℕ} (hN : 1 ≤ N) : cyc1Ideal N ≤ TwoSidedIdeal.ker (constTerm 1) := by
  rw [cyc1Ideal, TwoSidedIdeal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
    TwoSidedIdeal.mem_ker, map_pow, constTerm_generator, zero_pow (by omega)]

/-- The constant term `ONH_1^N → ℤ`, for `N ≥ 1`. -/
def constONH1 {N : ℕ} (hN : 1 ≤ N) : ONH1 N →+* ℤ :=
  Ideal.Quotient.lift _ (constTerm 1) (fun _ ha =>
    (TwoSidedIdeal.mem_ker _).mp (cyc1Ideal_le_ker hN (TwoSidedIdeal.mem_asIdeal.mp ha)))

/-- `ONH_1^N` is connected for `N ≥ 1`. -/
theorem onh1Connected {N : ℕ} (hN : 1 ≤ N) : Connected (onh1Grading N) :=
  imageGrading_connected _ opolConnected fun a b hab => by
    simpa using congrArg (constONH1 hN) hab

theorem ONH1_zero_subsingleton : Subsingleton (ONH1 0) := by
  have h : toONH1 0 1 = 0 := Ideal.Quotient.eq_zero_iff_mem.2
    (TwoSidedIdeal.mem_asIdeal.2 (TwoSidedIdeal.subset_span (by simp)))
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_one (toONH1 0), h]

/-! ### `K₀(ONH^N)` -/

local notation "L" => LaurentPolynomial ℤ

/-- `K₀(ONH_a^N)`: `ONH_0^N = ℤ`, `ONH_1^N = ℤ[x]/(x^N)`, `ONH_{n+2}^N`. -/
def KCyc (N : ℕ) : ℕ → Type
  | 0 => K0 intGrading
  | 1 => K0 (onh1Grading N)
  | n+2 => K0 (onhCycGrading n N)

instance KCyc.addCommGroup (N : ℕ) : ∀ a, AddCommGroup (KCyc N a)
  | 0 => inferInstanceAs (AddCommGroup (K0 intGrading))
  | 1 => inferInstanceAs (AddCommGroup (K0 (onh1Grading N)))
  | n+2 => inferInstanceAs (AddCommGroup (K0 (onhCycGrading n N)))

instance KCyc.module (N : ℕ) : ∀ a, Module L (KCyc N a)
  | 0 => inferInstanceAs (Module L (K0 intGrading))
  | 1 => inferInstanceAs (Module L (K0 (onh1Grading N)))
  | n+2 => inferInstanceAs (Module L (K0 (onhCycGrading n N)))

/-- `K₀(ONH_a^N) ≃ ℤ[q,q⁻¹]` for `a ≤ N` (EKL §6, p. 47). -/
def cycRankEquiv (N : ℕ) : (a : ℕ) → a ≤ N → (KCyc N a ≃ₗ[L] L)
  | 0, _ => K0.classify intConnected
  | 1, h => K0.classify (onh1Connected h)
  | n+2, h => onhCycK0Equiv n N h

/-- `K₀(ONH_a^N) = 0` for `a > N`. -/
theorem KCyc_subsingleton (N : ℕ) : ∀ a, N < a → Subsingleton (KCyc N a)
  | 0, h => absurd h (Nat.not_lt_zero N)
  | 1, h => by
    obtain rfl : N = 0 := by omega
    haveI := ONH1_zero_subsingleton
    exact K0_subsingleton (onh1Grading 0)
  | _+2, h => onhCycK0_subsingleton h

/-- `K₀(ONH^N) = ⊕_{a=0}^{N} K₀(ONH_a^N)`. -/
abbrev K0Cyc (N : ℕ) : Type := Π₀ a : Fin (N+1), KCyc N a

/-- A `ℤ[q,q⁻¹]`-basis of `K₀(ONH^N)` with one vector for each `a ≤ N`. -/
def basisK0Cyc (N : ℕ) : Basis (Fin (N+1)) L (K0Cyc N) :=
  (DFinsupp.basis fun a : Fin (N+1) =>
    (Basis.singleton (Fin 1) L).map (cycRankEquiv N a (Nat.lt_succ_iff.mp a.isLt)).symm).reindex
    (Equiv.sigmaUnique (Fin (N+1)) fun _ => Fin 1)

instance (N : ℕ) : Module.Free L (K0Cyc N) := Module.Free.of_basis (basisK0Cyc N)

/-- **EKL §6, last paragraph (p. 47)**: `K₀(ONH^N)` is free of rank `N + 1` over `ℤ[q,q⁻¹]`, the
rank of the integral form of the irreducible `U_q(sl_2)`-module of highest weight `N`. -/
theorem finrank_K0Cyc (N : ℕ) : Module.finrank L (K0Cyc N) = N + 1 := by
  rw [Module.finrank_eq_card_basis (basisK0Cyc N), Fintype.card_fin]

end
end OddMath.Frontier.Cyclotomic
