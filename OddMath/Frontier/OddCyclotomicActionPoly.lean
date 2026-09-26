import OddMath.Frontier.OddCyclotomicActionRes
import OddMath.Frontier.OddGrassmannSchur

/-!
# The polynomial representation of `ONH_a^N`

EKL arXiv:1111.1320v1, §5–§6. Rank `a = m+2`. Let `J ⊂ OΛ_a` be the two-sided ideal cut out by
the cyclotomic relation in the right Schubert coordinates of Corollary 2.14
(`Cyclotomic.revGrassmannianIdeal`, the image of `⟨h_j : j > N − a⟩` under `w₀`), and
`OPol_a·J` the polynomials whose right Schubert coordinates lie in `J` (`Cyclotomic.rightSpan`).

* `VMod m N = OPol_a/(OPol_a·J)`, a left `ONH_a^N`-module (`actV`); as an abelian group it is
  `⊕_{w ∈ S_a} OH_{a,N}` (`vmodEquiv`), free of rank `a!·C(N, a)` for `a ≤ N`
  (`vmod_free_finite`).
* An element of `ONH_a^N` is determined by its values on the classes of the Schubert polynomials
  (`eq_zero_of_act`, `eq_of_act`), and every family of values is realised (`ofCols`,
  `action_ofCols`): Proposition 5.2 in the form `ONH_a^N ≅ Hom_{OΛ_a}(OPol_a, VMod)`.
* `Etil`: the degree-zero idempotent `𝔰_w ↦ δ_{w,1} 𝔰_1` of `ONH_a`.
* `span_place`: every polynomial in `a` variables is, modulo `OPol_a·J`,
  `∑_{k < N-(a-1)} f_k(x_1, …, x_{a-1}) x_a^k`. This is the odd analogue of the presentation of the
  cohomology of the two-step flag variety `Fl(a-1, a; N)` over that of `Gr(a-1, N)`; it comes
  from `h_j(x̃_a, …, x̃_1) ∈ J` for `j ≥ N − a + 1` and
  `h_j(x̃_a, …, x̃_1) = ∑_i x̃_a^i h_{j-i}(x̃_{a-1}, …, x̃_1)` (`revComplete_expand`).
* The strand windows act on `ι(f) · x_a^k` through `f` (`action_window_place`,
  `action_dotHom_place`), `ι` the inclusion of the first `a - 1` variables.
* `bijective_of_surjective_of_finrank_eq`: a surjection between free `ℤ`-modules of the same finite
  rank is bijective.
-/

noncomputable section
open LaurentPolynomial Matrix

namespace OddMath.Frontier.OddCyclotomicAction
open GradedK0 OddCategorification Cyclotomic OddBialgebra
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeAction NilCoxeterWords NilHeckeEndomorphism OddSchubertAction
open PlacticEvaluation FiniteCompleteElementary

/- `OPol` carries its own ring structure; the pointwise `Finsupp` multiplication is not used. -/
attribute [-instance] Finsupp.instMul Finsupp.instMulZeroClass Finsupp.instSemigroupWithZero
  Finsupp.instNonUnitalNonAssocSemiring Finsupp.instNonUnitalSemiring
  Finsupp.instNonUnitalCommSemiring Finsupp.instNonUnitalNonAssocRing Finsupp.instNonUnitalRing
  Finsupp.instNonUnitalCommRing

/-! ### The module `VMod m N = OPol_a/(OPol_a·J)` -/

/-- `OPol_a·J`, `J = rev⟨h_j : j > N − a⟩`, as a subgroup. -/
def Wsub (m N : ℕ) : Submodule ℤ (SkewPolynomial (m+2)) where
  carrier := rightSpan m (revGrassmannianIdeal m N)
  add_mem' := rightSpan_add m _
  zero_mem' := fun w => by rw [map_zero, Pi.zero_apply]; exact TwoSidedIdeal.zero_mem _
  smul_mem' c _ hf := rightSpan_zsmul m _ c hf

theorem mem_Wsub {m N : ℕ} {f : SkewPolynomial (m+2)} :
    f ∈ Wsub m N ↔ ∀ w, coordinates m f w ∈ revGrassmannianIdeal m N := Iff.rfl

theorem Wsub_mul_left {m N : ℕ} (p : SkewPolynomial (m+2)) {f : SkewPolynomial (m+2)}
    (hf : f ∈ Wsub m N) : p * f ∈ Wsub m N :=
  rightSpan_mul_left m _ p hf

/-- The module `OPol_a/(OPol_a·J)`. -/
abbrev VMod (m N : ℕ) : Type := SkewPolynomial (m+2) ⧸ Wsub m N

/-- The natural action preserves `OPol_a·J`: it is right `OΛ_a`-linear. -/
theorem action_mem_Wsub {m N : ℕ} (T : Presented m) {f : SkewPolynomial (m+2)}
    (hf : f ∈ Wsub m N) : action m T f ∈ Wsub m N :=
  rightSpan_map m _ (action m T).toAddMonoidHom (fun g k => (actionEquiv m T).property g k) hf

/-- The action of `ONH_a` on `VMod`. -/
def actPre (m N : ℕ) : Presented m →+* Module.End ℤ (VMod m N) where
  toFun T := (Wsub m N).mapQ (Wsub m N) (action m T) fun _ hf => action_mem_Wsub T hf
  map_one' := by
    apply Submodule.linearMap_qext
    ext f
    simp
  map_mul' T U := by
    apply Submodule.linearMap_qext
    ext f
    simp [action_mul_apply]
  map_zero' := by
    apply Submodule.linearMap_qext
    ext f
    simp
  map_add' T U := by
    apply Submodule.linearMap_qext
    ext f
    simp

theorem actPre_mk {m N : ℕ} (T : Presented m) (f : SkewPolynomial (m+2)) :
    actPre m N T (Submodule.Quotient.mk f) = Submodule.Quotient.mk (action m T f) := rfl

theorem x1_pow_mem_Wsub (m N : ℕ) : x1 m ^ N ∈ Wsub m N := by
  have h := (entryIdeal_le_iff m N (entryIdeal (cor214 m (firstDot m ^ N)))).1 le_rfl
  rw [entryIdeal_eq_rev] at h
  exact h

theorem cyclotomicIdeal_le_ker_actPre (m N : ℕ) :
    cyclotomicIdeal m N ≤ TwoSidedIdeal.ker (actPre m N) := by
  rw [cyclotomicIdeal, TwoSidedIdeal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
    TwoSidedIdeal.mem_ker]
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, actPre_mk,
    action_firstDot_pow, LinearMap.zero_apply]
  obtain ⟨g, hg⟩ := x1_pow_normal m N f
  rw [hg, Submodule.Quotient.mk_eq_zero]
  exact Wsub_mul_left g (x1_pow_mem_Wsub m N)

/-- **The action of `ONH_a^N` on `OPol_a/(OPol_a·J)`.** -/
def actV (m N : ℕ) : ONH m N →+* Module.End ℤ (VMod m N) :=
  liftTwoSided (cyclotomicIdeal m N) (actPre m N) (cyclotomicIdeal_le_ker_actPre m N)

theorem actV_toONH {m N : ℕ} (T : Presented m) (f : SkewPolynomial (m+2)) :
    actV m N (toONH m N T) (Submodule.Quotient.mk f) = Submodule.Quotient.mk (action m T f) := by
  have h := liftTwoSided_mk (cyclotomicIdeal m N) (actPre m N) (cyclotomicIdeal_le_ker_actPre m N) T
  exact congrArg (fun φ : Module.End ℤ (VMod m N) => φ (Submodule.Quotient.mk f)) h

/-! ### Faithfulness and Proposition 5.2 -/

theorem cor214_apply (m : ℕ) (T : Presented m) (v w : Perm m) :
    cor214 m T v w = coordinates m (action m T (schubert w)) v := by
  rw [cor214, RingEquiv.trans_apply, matrixEquiv_apply, actionEquiv_apply]

/-- `ONH_a^N` acts faithfully on the classes of the Schubert polynomials. -/
theorem eq_zero_of_act {m N : ℕ} (y : ONH m N)
    (h : ∀ w, actV m N y (Submodule.Quotient.mk (schubert w)) = 0) : y = 0 := by
  obtain ⟨T, rfl⟩ := toONH_surjective m N y
  apply (prop_5_2 m N).injective
  rw [map_zero]
  ext v w
  have hw := h w
  rw [actV_toONH, Submodule.Quotient.mk_eq_zero, mem_Wsub] at hw
  rw [prop_5_2_apply, Matrix.zero_apply]
  change entryMap m N (cor214 m T v w) = 0
  rw [entryMap_eq_zero_iff, entryIdeal_eq_rev, cor214_apply]
  exact hw v

theorem eq_of_act {m N : ℕ} {y z : ONH m N}
    (h : ∀ w, actV m N y (Submodule.Quotient.mk (schubert w)) =
      actV m N z (Submodule.Quotient.mk (schubert w))) : y = z := by
  rw [← sub_eq_zero]
  exact eq_zero_of_act _ fun w => by rw [map_sub, LinearMap.sub_apply, h w, sub_self]

/-- The element of `ONH_a` sending the Schubert polynomial `𝔰_w` to `f w`. -/
def ofCols {m : ℕ} (f : Perm m → SkewPolynomial (m+2)) : Presented m :=
  (cor214 m).symm fun v w => coordinates m (f w) v

theorem action_ofCols {m : ℕ} (f : Perm m → SkewPolynomial (m+2)) (w : Perm m) :
    action m (ofCols f) (schubert w) = f w := by
  apply (coordinates m).injective
  funext v
  rw [← cor214_apply, ofCols, RingEquiv.apply_symm_apply]

/-- `T = U` in `ONH_a` iff they agree on the Schubert polynomials. -/
theorem ext_schubert {m : ℕ} {T U : Presented m}
    (h : ∀ w, action m T (schubert w) = action m U (schubert w)) : T = U := by
  apply (cor214 m).injective
  ext v w
  rw [cor214_apply, cor214_apply, h w]

theorem ofCols_mem {m : ℕ} {d : ℤ} {f : Perm m → SkewPolynomial (m+2)}
    (hf : ∀ w, f w ∈ NilHeckeGradedEnd.polynomialPiece (m+2) (d + 2 * (length w : ℤ))) :
    ofCols f ∈ onhGrading m d := by
  rw [mem_onhGrading_iff, ← cor214_eq_onhIso]
  intro v w
  rw [ofCols, RingEquiv.apply_symm_apply]
  exact mem_of_deg_eq (NilHeckeGradedEnd.coordinates_mem (hf w) v)
    (by simp only [lenShift]; ring)

/-! ### The projection onto the first Schubert line -/

/-- `𝔰_w ↦ δ_{w,1} 𝔰_1`, a degree-zero idempotent of `ONH_a` (under Corollary 2.14 the matrix
unit at `(1, 1)`). -/
def Etil (m : ℕ) : Presented m := ofCols fun w => if w = 1 then schubert 1 else 0

theorem action_Etil_schubert (m : ℕ) (w : Perm m) :
    action m (Etil m) (schubert w) = if w = 1 then schubert 1 else 0 :=
  action_ofCols _ w

theorem one_eq_smul_schubert (m : ℕ) :
    ∃ c : ℤ, c * c = 1 ∧ (1 : SkewPolynomial (m+2)) = c • schubert 1 := by
  obtain ⟨c, hc, h1⟩ := schubert_one_sq m
  exact ⟨c, hc, by rw [h1, smul_smul, hc, one_smul]⟩

theorem action_Etil_one (m : ℕ) : action m (Etil m) 1 = 1 := by
  obtain ⟨c, _, h1⟩ := one_eq_smul_schubert m
  rw [h1, map_zsmul, action_Etil_schubert, if_pos rfl]

theorem Etil_mul_self (m : ℕ) : Etil m * Etil m = Etil m := ext_schubert fun w => by
  rw [action_mul_apply, action_Etil_schubert]
  split_ifs
  · rw [action_Etil_schubert, if_pos rfl]
  · rw [map_zero]

theorem Etil_mem (m : ℕ) : Etil m ∈ onhGrading m 0 := ofCols_mem fun w => by
  split_ifs with h
  · subst h
    rw [zero_add]
    exact NilHeckeGradedEnd.schubert_mem 1
  · exact zero_mem _

/-! ### Strand windows acting on `OPol` -/

theorem divided_mul_pow_spectator {n : ℕ} (i : Fin (n+1)) (j : Fin (n+2))
    (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) (F : SkewPolynomial (n+2)) (k : ℕ) :
    AllRankDivided.divided i (F * generator j ^ k) =
      AllRankDivided.divided i F * generator j ^ k := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, AllRankDivided.divided_mul_spectator i j hl hr, ih, mul_assoc]

/-- The window `ONH_{a} ⊂ ONH_{a+1}` on the first `a` strands acts on `ι(f) · x_{a+1}^k` through
`f`. -/
theorem action_window_place (n : ℕ) (T : Presented n) (f : SkewPolynomial (n+2)) (k : ℕ) :
    action (n+1) (OnhWindow.windowHom n (n+1) 0 (window_le_succ n) T)
      (ProjectorRank.place 0 (window_le_succ n) f * generator (Fin.last (n+2)) ^ k) =
    ProjectorRank.place 0 (window_le_succ n) (action n T f) * generator (Fin.last (n+2)) ^ k := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective T
  induction a using FreeAlgebra.induction generalizing f with
  | grade0 r =>
    simp only [algebraMap_int_eq, _root_.eq_intCast, map_intCast, Module.End.intCast_apply,
      map_zsmul,
      smul_mul_assoc]
  | grade1 g =>
    cases g with
    | inl j =>
      change action (n+1) (OnhWindow.windowHom n (n+1) 0 _ (dot n j)) _ =
        ProjectorRank.place 0 _ (action n (dot n j) f) * _
      rw [OnhWindow.windowHom_dot, action_dot_apply, action_dot_apply, map_mul,
        ProjectorRank.place_generator, mul_assoc]
      rfl
    | inr i =>
      change action (n+1) (OnhWindow.windowHom n (n+1) 0 _ (crossing n i)) _ =
        ProjectorRank.place 0 _ (action n (crossing n i) f) * _
      rw [OnhWindow.windowHom_crossing, action_crossing_apply, action_crossing_apply]
      rw [divided_mul_pow_spectator]
      · exact congrArg (· * _) (ProjectorRank.place_divided_and_s (window_le_succ n) i f).1
      · intro h
        have := congrArg Fin.val h
        simp at this
        omega
      · intro h
        have := congrArg Fin.val h
        simp at this
        omega
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb, add_mul]
  | mul a b ha hb =>
    rw [(Ideal.Quotient.mk _).map_mul, (OnhWindow.windowHom _ _ _ _).map_mul, action_mul_apply,
      hb, ha, action_mul_apply]

theorem le_one_two : 0 + 1 ≤ 2 := by omega

/-- `ONH_1 = OPol_1 → ONH_2`, `x ↦ x_1`, acts by left multiplication by `x_1`. -/
theorem action_dotHom_place (f : SkewPolynomial 1) (g : SkewPolynomial 2) :
    action 0 (dotHom 0 0 f) g = ProjectorRank.place 0 le_one_two f * g := by
  induction f using PrefixEmbedding.induction_generators generalizing g with
  | hconst r =>
    rw [map_zsmul, map_one, map_zsmul, map_one, LinearMap.smul_apply, Module.End.one_apply,
      map_zsmul, map_one, smul_mul_assoc, one_mul]
  | hgen j =>
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [dotHom_generator, action_dot_apply, ProjectorRank.place_generator]
    rfl
  | hadd f f' hf hf' => rw [map_add, map_add, LinearMap.add_apply, hf, hf', map_add, add_mul]
  | hmul f f' hf hf' => rw [map_mul, action_mul_apply, hf', hf, map_mul, mul_assoc]

/-! ### The two-step flag relation: `OPol_a/(OPol_a·J) = ∑_{k < N-(a-1)} ι(OPol_{a-1}) x_a^k` -/

section Flag

variable (m : ℕ)

theorem le_place (m : ℕ) : 0 + (m+1) ≤ m+2 := by omega

/-- `OPol_{a-1} → OPol_a` on the first `a - 1` variables (`a = m+2`). -/
abbrev pl : SkewPolynomial (m+1) →+* SkewPolynomial (m+2) := ProjectorRank.place 0 (le_place m)

/-- The last variable `x_a` of `OPol_a`. -/
abbrev xl : SkewPolynomial (m+2) := generator (Fin.last (m+1))

variable {m}

theorem pl_generator (j : Fin (m+1)) : pl m (generator j) = generator j.castSucc := by
  rw [ProjectorRank.place_generator]
  congr 1

theorem xl_mul_pl (f : SkewPolynomial (m+1)) : ∃ f', xl m * pl m f = pl m f' * xl m := by
  induction f using PrefixEmbedding.induction_generators with
  | hconst r => exact ⟨r • 1, by rw [map_zsmul, map_one, mul_smul_comm, smul_mul_assoc, mul_one,
      one_mul]⟩
  | hgen j =>
    refine ⟨-generator j, ?_⟩
    rw [pl_generator, map_neg, pl_generator, neg_mul]
    exact OddMath.SkewPolynomial.generator_anticommute _ _ (Fin.castSucc_lt_last j).ne'
  | hadd f g hf hg =>
    obtain ⟨f', hf'⟩ := hf
    obtain ⟨g', hg'⟩ := hg
    exact ⟨f' + g', by rw [map_add, mul_add, hf', hg', map_add, add_mul]⟩
  | hmul f g hf hg =>
    obtain ⟨f', hf'⟩ := hf
    obtain ⟨g', hg'⟩ := hg
    exact ⟨f' * g', by rw [map_mul, ← mul_assoc, hf', mul_assoc, hg', ← mul_assoc, map_mul]⟩

theorem xl_pow_mul_pl (j : ℕ) (f : SkewPolynomial (m+1)) :
    ∃ f', xl m ^ j * pl m f = pl m f' * xl m ^ j := by
  induction j generalizing f with
  | zero => exact ⟨f, by rw [pow_zero, one_mul, mul_one]⟩
  | succ j ih =>
    obtain ⟨f₁, h₁⟩ := ih f
    obtain ⟨f₂, h₂⟩ := xl_mul_pl f₁
    exact ⟨f₂, by rw [pow_succ', mul_assoc, h₁, ← mul_assoc, h₂, mul_assoc, ← pow_succ']⟩

/-- `OPol_a` is spanned by the `ι(f) x_a^k`. -/
theorem mem_span_pl (g : SkewPolynomial (m+2)) :
    g ∈ Submodule.span ℤ (Set.range fun p : SkewPolynomial (m+1) × ℕ => pl m p.1 * xl m ^ p.2) := by
  set U := Submodule.span ℤ (Set.range fun p : SkewPolynomial (m+1) × ℕ => pl m p.1 * xl m ^ p.2)
  have hgen : ∀ j : Fin (m+2), ∀ u ∈ U, generator j * u ∈ U := by
    intro j u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨f, k⟩, rfl⟩ := hx
      induction j using Fin.lastCases with
      | last =>
        obtain ⟨f', hf'⟩ := xl_mul_pl f
        refine Submodule.subset_span ⟨(f', k+1), ?_⟩
        change pl m f' * xl m ^ (k+1) = xl m * (pl m f * xl m ^ k)
        rw [← mul_assoc, hf', mul_assoc, ← pow_succ']
      | cast j =>
        refine Submodule.subset_span ⟨(generator j * f, k), ?_⟩
        change pl m (generator j * f) * xl m ^ k = _
        rw [map_mul, pl_generator, mul_assoc]
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact U.smul_mem c hx
  have key : ∀ f : SkewPolynomial (m+2), ∀ u ∈ U, f * u ∈ U := by
    intro f
    induction f using PrefixEmbedding.induction_generators with
    | hconst r => intro u hu; rw [smul_mul_assoc, one_mul]; exact U.smul_mem r hu
    | hgen j => exact hgen j
    | hadd f g hf hg => intro u hu; rw [add_mul]; exact add_mem (hf u hu) (hg u hu)
    | hmul f g hf hg => intro u hu; rw [mul_assoc]; exact hf _ (hg u hu)
  have h1 : (1 : SkewPolynomial (m+2)) ∈ U :=
    Submodule.subset_span ⟨(1, 0), by simp⟩
  simpa using key g 1 h1

/-- `h_k(x̃_a, …, x̃_1) = ∑_{j ≤ k} x̃_a^j h_{k-j}(x̃_{a-1}, …, x̃_1)`. -/
theorem revComplete_expand (k : ℕ) :
    revComplete m (m+2) k = ∑ j ∈ Finset.range (k+1),
      tildeGenerator (Fin.last (m+1)) ^ j * revComplete m (m+1) (k - j) := by
  induction k with
  | zero => simp [revComplete]
  | succ k ih =>
    rw [revComplete_succ m (m+1) k (by omega), ih, Finset.sum_range_succ' _ (k+1), Finset.mul_sum,
      Nat.sub_zero, pow_zero, one_mul]
    refine congrArg (· + revComplete m (m+1) (k+1)) (Finset.sum_congr rfl fun x _ => ?_)
    rw [← mul_assoc, pow_succ', Nat.add_sub_add_right]
    rfl

theorem revAlphabet_mem_range (i : Fin (m+1)) : revAlphabet m (m+1) i ∈ (pl m).range := by
  have hi : m + 1 - 1 - i.val < m + 1 := by omega
  rw [revAlphabet, dif_pos (by omega : m + 1 - 1 - i.val < m + 2)]
  refine ⟨tildeGenerator ⟨m + 1 - 1 - i.val, hi⟩, ?_⟩
  rw [tildeGenerator, tildeGenerator, map_zsmul, pl_generator]
  rfl

theorem revComplete_mem_range (k : ℕ) : revComplete m (m+1) k ∈ (pl m).range := by
  classical
  rw [revComplete, FiniteWords.weakSum_eq]
  refine Subring.sum_mem _ fun f _ => ?_
  split_ifs
  · exact Subring.list_prod_mem _ fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact revAlphabet_mem_range _
  · exact Subring.zero_mem _

theorem revComplete_full_mem {N k : ℕ} (hk : N < k + (m+2)) : revComplete m (m+2) k ∈ Wsub m N := by
  rw [revComplete_full_eq]
  refine (Wsub m N).smul_mem _ ?_
  rw [mem_Wsub]
  exact (kernel_mem_rightSpan_iff m _ _).2 (TwoSidedIdeal.subset_span ⟨k, hk, rfl⟩)

variable (m) in
/-- Polynomials `≡ ∑_{k < N-(a-1)} ι(f_k) x_a^k` modulo `OPol_a·J`. -/
def flagSpan (N : ℕ) : Submodule ℤ (SkewPolynomial (m+2)) where
  carrier := {g | ∃ h : Fin (N - (m+1)) → SkewPolynomial (m+1),
    g - ∑ k, pl m (h k) * xl m ^ (k : ℕ) ∈ Wsub m N}
  add_mem' := by
    rintro g₁ g₂ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
    refine ⟨h₁ + h₂, ?_⟩
    convert add_mem e₁ e₂ using 1
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    abel
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c g ⟨h, e⟩
    refine ⟨c • h, ?_⟩
    convert (Wsub m N).smul_mem c e using 1
    simp only [Pi.smul_apply, map_zsmul, smul_mul_assoc, smul_sub, Finset.smul_sum]

theorem Wsub_le_flagSpan (N : ℕ) : Wsub m N ≤ flagSpan m N :=
  fun g hg => ⟨0, by simpa using hg⟩

theorem tilde_last_eq : tildeGenerator (Fin.last (m+1)) = ((-1 : ℤ) ^ (m+1)) • xl m := rfl

theorem pl_mul_xl_pow_mem {N : ℕ} (M : ℕ) (f : SkewPolynomial (m+1)) :
    pl m f * xl m ^ M ∈ flagSpan m N := by
  induction M using Nat.strong_induction_on generalizing f with
  | _ M ih =>
    by_cases hM : M < N - (m+1)
    · refine ⟨fun k => if (k : ℕ) = M then f else 0, ?_⟩
      have hs : ∑ k : Fin (N - (m+1)), pl m (if (k : ℕ) = M then f else 0) * xl m ^ (k : ℕ) =
          pl m f * xl m ^ M := by
        rw [Finset.sum_eq_single ⟨M, hM⟩]
        · simp
        · intro k _ hk
          rw [if_neg (fun e => hk (Fin.ext e)), map_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      show pl m f * xl m ^ M - ∑ k : Fin (N - (m+1)),
        pl m (if (k : ℕ) = M then f else 0) * xl m ^ (k : ℕ) ∈ Wsub m N
      rw [hs, sub_self]
      exact zero_mem _
    · have hN : N < M + (m+2) := by omega
      set c : ℤ := (-1) ^ (m+1)
      have hc : c * c = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      set t := tildeGenerator (Fin.last (m+1))
      have ht : t = c • xl m := tilde_last_eq
      -- `x_a^M = c^M t^M`
      have hx : xl m ^ M = c ^ M • t ^ M := by
        rw [ht, smul_pow, smul_smul, ← mul_pow, hc, one_pow, one_smul]
      -- `t^M = h_M(full) - ∑_{j < M} t^j h_{M-j}(first)`
      have hexp := revComplete_expand (m := m) M
      rw [Finset.sum_range_succ, Nat.sub_self] at hexp
      have h0 : revComplete m (m+1) 0 = 1 := by simp [revComplete]
      rw [h0, mul_one] at hexp
      have htM : t ^ M = revComplete m (m+2) M -
          ∑ j ∈ Finset.range M, t ^ j * revComplete m (m+1) (M - j) := by
        rw [hexp]; abel
      rw [hx, mul_smul_comm, htM, mul_sub, Finset.mul_sum]
      refine (flagSpan m N).smul_mem _ (sub_mem (Wsub_le_flagSpan N (Wsub_mul_left _
        (revComplete_full_mem hN))) (sum_mem fun j hj => ?_))
      have hjM : j < M := Finset.mem_range.1 hj
      obtain ⟨p, hp⟩ := revComplete_mem_range (m := m) (M - j)
      obtain ⟨p', hp'⟩ := xl_pow_mul_pl j p
      rw [← hp, ht, smul_pow, smul_mul_assoc, mul_smul_comm, ← mul_assoc, mul_assoc (pl m f),
        hp', ← mul_assoc, ← map_mul]
      exact (flagSpan m N).smul_mem _ (ih j hjM _)

/-- **The two-step flag relation.** Modulo `OPol_a·J`, every polynomial in `a = m+2` variables is
`∑_{k < N-(a-1)} ι(f_k) x_a^k` with `f_k` a polynomial in the first `a - 1` variables. -/
theorem span_place (N : ℕ) (g : SkewPolynomial (m+2)) :
    ∃ h : Fin (N - (m+1)) → SkewPolynomial (m+1),
      g - ∑ k, pl m (h k) * xl m ^ (k : ℕ) ∈ Wsub m N := by
  have hle : Submodule.span ℤ (Set.range fun p : SkewPolynomial (m+1) × ℕ =>
      pl m p.1 * xl m ^ p.2) ≤ flagSpan m N :=
    Submodule.span_le.2 fun _ ⟨p, hp⟩ => hp ▸ pl_mul_xl_pow_mem p.2 p.1
  exact hle (mem_span_pl g)

end Flag

/-! ### Ranks -/

section Rank

/-- `OH_{a,N}` is free of rank `C(N, a)`, `2 ≤ a ≤ N` (Proposition 5.4). -/
theorem OH_free_finite {n N : ℕ} (h : n+2 ≤ N) :
    Module.Free ℤ (OH n N) ∧ Module.Finite ℤ (OH n N) ∧
      Module.finrank ℤ (OH n N) = N.choose (n+2) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨inferInstance, Module.Finite.of_basis (OddGrassmannSchur.proposition_5_4 n b),
    OddGrassmannSchur.finrank_OH n b⟩

/-- `f ↦ ([rev c_w(f)])_w`, the right Schubert coordinates reduced to `OH_{a,N}`. -/
def vmodEval (m N : ℕ) : SkewPolynomial (m+2) →ₗ[ℤ] (Perm m → OH m N) :=
  LinearMap.pi fun w => (entryMap m N).toAddMonoidHom.toIntLinearMap ∘ₗ
    (LinearMap.proj w) ∘ₗ (coordinates m).toLinearMap

theorem vmodEval_apply (m N : ℕ) (f : SkewPolynomial (m+2)) (w : Perm m) :
    vmodEval m N f w = entryMap m N (coordinates m f w) := rfl

theorem ker_vmodEval (m N : ℕ) : LinearMap.ker (vmodEval m N) = Wsub m N := by
  ext f
  rw [LinearMap.mem_ker, mem_Wsub, funext_iff]
  refine forall_congr' fun w => ?_
  rw [vmodEval_apply, Pi.zero_apply, entryMap_eq_zero_iff, entryIdeal_eq_rev]

theorem vmodEval_surjective (m N : ℕ) : Function.Surjective (vmodEval m N) := by
  intro c
  choose k hk using fun w => entryMap_surjective m N (c w)
  refine ⟨synthesis m k, funext fun w => ?_⟩
  rw [vmodEval_apply, coordinates_synthesis, hk]

/-- `OPol_a/(OPol_a·J) ≅ ⊕_{w ∈ S_a} OH_{a,N}` as abelian groups. -/
def vmodEquiv (m N : ℕ) : VMod m N ≃ₗ[ℤ] (Perm m → OH m N) :=
  (Submodule.quotEquivOfEq _ _ (ker_vmodEval m N).symm).trans
    ((vmodEval m N).quotKerEquivOfSurjective (vmodEval_surjective m N))

theorem vmodEquiv_mk (m N : ℕ) (f : SkewPolynomial (m+2)) :
    vmodEquiv m N (Submodule.Quotient.mk f) = vmodEval m N f := rfl

theorem card_perm (m : ℕ) : Fintype.card (Perm m) = (m+2).factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- `VMod` is free of rank `a!·C(N, a)` for `a ≤ N`. -/
theorem vmod_free_finite {m N : ℕ} (h : m+2 ≤ N) :
    Module.Free ℤ (VMod m N) ∧ Module.Finite ℤ (VMod m N) ∧
      Module.finrank ℤ (VMod m N) = (m+2).factorial * N.choose (m+2) := by
  obtain ⟨h1, h2, h3⟩ := OH_free_finite h
  refine ⟨Module.Free.of_equiv (vmodEquiv m N).symm, Module.Finite.equiv (vmodEquiv m N).symm, ?_⟩
  rw [(vmodEquiv m N).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    card_perm, h3, smul_eq_mul]

/-- A surjective linear map between free `ℤ`-modules of the same finite rank is bijective. -/
theorem bijective_of_surjective_of_finrank_eq {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ M'] [Module.Finite ℤ M']
    (f : M →ₗ[ℤ] M') (hf : Function.Surjective f)
    (h : Module.finrank ℤ M = Module.finrank ℤ M') : Function.Bijective f := by
  let e : M' ≃ₗ[ℤ] M := LinearEquiv.ofFinrankEq M' M h.symm
  have hg : Function.Surjective (e.toLinearMap ∘ₗ f) := e.surjective.comp hf
  have hi := OrzechProperty.injective_of_surjective_endomorphism _ hg
  exact ⟨fun x y hxy => hi (by simp [hxy]), hf⟩

end Rank

end OddMath.Frontier.OddCyclotomicAction
