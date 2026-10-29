import OddMath.SKM.RouquierHomDistinctMixed
import OddMath.SKM.RouquierHomDistinctMixedDots
import OddMath.SKM.RouquierHomDistinctPost
import OddMath.SKM.RouquierRightTranspose
import OddMath.SKM.RouquierMateSectors

/-!
# The distinct-colour mixed mate `U` with a dotted crossing

The mate `U = M(J⁻¹)` of `homDistinctMixedMate` (formalizing
`docs/Nondegeneracy/SwappedDistinctMixedMates.md` (7), (8)) is taken around the two shifted
postcomposition adjunctions of a reservoir edge `E' ⊣ F'`. When the crossing is `J⁻¹`
followed by an endomorphism `Φ` of its target `E ≫ Π^κ(Y ≫ E')` (the action of the
parameter polynomial `Q`), the mate is `homDistinctMixedMateDot`. This is the mirror image of
`homDistinctMixedPreMateDot`: here the dot that must be transposed is the one on the
postcomposed edge `E'`, and it is transposed along `E' ⊣ F'`.

* `homShiftPostAdjunction_counit_transpose`: a post dot `Y ◁ y` before the shifted counit
  equals the transposed dot `(Π^κ H ◁ yᵀ) ▷ E'`, where `yᵀ = rightTranspose A A y`.
* `homDistinctMixedMateDot_monomial`: for even `x : E ⟶ E` and even `y : E' ⟶ E'`, the
  dotted mate of `x ▷ _ ≫ E ◁ Π^κ(Y ◁ y)` is `(x ▷ Y ≫ E ◁ (Π^κ H ◁ yᵀ)) ≫ U`.
* `homDistinctMixedMateDotLinear`: the dotted mate is linear in `Φ`.
* `isUnit_smul_pow_add_of_mem_admissibleMonomials`: in an algebra, `c • aᵈ + N` is a unit when `a` is a
  unit, `c` a unit scalar, `b` nilpotent and `N` a combination of monomials `aᵖ bᑫ` with
  `q ≥ 1`, where the admissible exponents commute. This is (14) for the source polynomial.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Transpose
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {x c d : B} {E' : c ⟶ d} {F' : d ⟶ c}

/-- A dot on the postcomposed edge before the post counit is its right transpose on the
right adjoint. -/
theorem homPostCounit_whiskerLeft (A : SuperAdjunction (k := k) E' F') (Z : x ⟶ d)
    (y : E' ⟶ E') :
    (Z ≫ F') ◁ y ≫ (homPostCounit A).app Z =
      (Z ◁ SuperAdjunction.rightTranspose A A y) ▷ E' ≫ (homPostCounit A).app Z := by
  rw [homPostCounit_app, TwoSupercategory.associator_naturality_right_assoc (R := k),
    TwoSupercategory.associator_naturality_middle_assoc (R := k),
    ← TwoSupercategory.whiskerLeft_comp'_assoc k, ← TwoSupercategory.whiskerLeft_comp'_assoc k,
    ← SuperAdjunction.rightTranspose_counit]

end Transpose

section Mate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B}

/-- The shifted counit absorbs the transposed dot: for even `y`,
`Π^κ(Y ◁ y) ≫ ε = Π^κ((Π^κ H ◁ yᵀ) ▷ E') ≫ ε` with `Y = Π^κ H ≫ F'`. -/
theorem homShiftPostAdjunction_counit_transpose {E' : c ⟶ d} {F' : d ⟶ c}
    (A : SuperAdjunction (k := k) E' F') (κ : ZMod 2) (H : b ⟶ d) {y : E' ⟶ E'}
    (hy : y ∈ parity (R := k) _ _ 0) :
    (homParityShift (k := k) κ).map
        (((homParityShift (k := k) κ).obj H ≫ F') ◁ y) ≫
        (homShiftPostAdjunction A b κ).counit.app H =
      (homParityShift (k := k) κ).map
        (((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y) ▷ E') ≫
        (homShiftPostAdjunction A b κ).counit.app H := by
  set δ := homParityShiftDatum (k := k) (C := b ⟶ d) κ
  set Y := (homParityShift (k := k) κ).obj H ≫ F'
  have hyT := SuperAdjunction.rightTranspose_mem A A hy
  have hε : (homShiftPostAdjunction A b κ).counit.app H = sign k (κ * κ) •
      ((homParityShiftDatum (k := k) κ).iso (Y ≫ E')).hom ≫
        ((δ.iso H).hom ▷ F') ▷ E' ≫ (homPostCounit A).app H := by
    rw [homShiftPostAdjunction_counit_app, homShiftConjugationIso_hom_signed,
      Linear.smul_comp, Category.assoc]
    rfl
  have h1 := (homParityShiftDatum (k := k) (C := b ⟶ d) κ |>.hom_naturality_even
    (X := Y ≫ E') (Y := Y ≫ E') (TwoSupercategory.whiskerLeft_mem Y hy))
  have h2 := (homParityShiftDatum (k := k) (C := b ⟶ d) κ |>.hom_naturality_even
    (X := Y ≫ E') (Y := Y ≫ E') (TwoSupercategory.whiskerRight_mem E'
      (TwoSupercategory.whiskerLeft_mem ((homParityShift (k := k) κ).obj H) hyT)))
  rw [hε, Linear.comp_smul, Linear.comp_smul, reassoc_of% h1, reassoc_of% h2]
  congr 2
  rw [← TwoSupercategory.whisker_exchange_of_even_right_assoc (R := k) _ hy,
    homPostCounit_whiskerLeft, ← TwoSupercategory.comp_whiskerRight'_assoc k,
    ← TwoSupercategory.comp_whiskerRight'_assoc k,
    TwoSupercategory.whisker_exchange_of_even_right (R := k) _ hyT]

variable (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)

/-- The mate of `J⁻¹` followed by an endomorphism `Φ` of the target of `J⁻¹`, around the
two shifted post adjunctions. -/
def homDistinctMixedMateDot
    (Φ : E ≫ (homParityShift (k := k) κ).obj
        (((homParityShift (k := k) κ).obj H ≫ F') ≫ E') ⟶
      E ≫ (homParityShift (k := k) κ).obj
        (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')) :
    E ≫ ((homParityShift (k := k) κ).obj H ≫ F') ⟶
      (homParityShift (k := k) τ).obj (E ≫ H) ≫ F' :=
  (homShiftPostAdjunction A a τ).unit.app (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫
    (homParityShift (k := k) τ).map
      ((homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫
        Φ ≫ E ◁ (homShiftPostAdjunction A b κ).counit.app H) ▷ F'

theorem homDistinctMixedMateDot_id :
    homDistinctMixedMateDot E A κ τ H (𝟙 _) = homDistinctMixedMate E A κ τ H := by
  rw [homDistinctMixedMateDot, homDistinctMixedMate, Category.id_comp]

/-- The dotted mate as a `k`-linear map of the dot. -/
def homDistinctMixedMateDotLinear :
    End (E ≫ (homParityShift (k := k) κ).obj
        (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')) →ₗ[k]
      (E ≫ ((homParityShift (k := k) κ).obj H ≫ F') ⟶
        (homParityShift (k := k) τ).obj (E ≫ H) ≫ F') where
  toFun Φ := homDistinctMixedMateDot E A κ τ H Φ
  map_add' Φ Ψ := by
    simp only [homDistinctMixedMateDot]
    rw [Preadditive.add_comp, Preadditive.comp_add, Functor.map_add,
      TwoSupercategory.add_whiskerRight (R := k), Preadditive.comp_add]
  map_smul' s Φ := by
    simp only [homDistinctMixedMateDot, RingHom.id_apply]
    rw [Linear.smul_comp, Linear.comp_smul, Functor.map_smul,
      TwoSupercategory.smul_whiskerRight (R := k), Linear.comp_smul]

theorem homDistinctMixedMateDotLinear_apply (Φ) :
    homDistinctMixedMateDotLinear E A κ τ H Φ = homDistinctMixedMateDot E A κ τ H Φ := rfl

/-- The source-side transport of a pre dot and a post dot: for even `x` and `y`, the dotted
mate of `x ▷ _ ≫ E ◁ Π^κ(Y ◁ y)` is `(x ▷ Y ≫ E ◁ (Π^κ H ◁ yᵀ)) ≫ U`. -/
theorem homDistinctMixedMateDot_monomial {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0) :
    homDistinctMixedMateDot E A κ τ H
        (x ▷ (homParityShift (k := k) κ).obj
            (((homParityShift (k := k) κ).obj H ≫ F') ≫ E') ≫
          E ◁ (homParityShift (k := k) κ).map
            (((homParityShift (k := k) κ).obj H ≫ F') ◁ y)) =
      (x ▷ ((homParityShift (k := k) κ).obj H ≫ F') ≫
        E ◁ ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) ≫
        homDistinctMixedMate E A κ τ H := by
  set Y := (homParityShift (k := k) κ).obj H ≫ F'
  set J := homMixedInterchange (k := k) E E' κ τ Y
  set g : Y ⟶ Y := (homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y
  have hg : g ∈ parity (R := k) Y Y 0 :=
    TwoSupercategory.whiskerLeft_mem _ (SuperAdjunction.rightTranspose_mem A A hy)
  have hx' : J.inv ≫ x ▷ _ = (homParityShift (k := k) τ).map ((x ▷ Y) ▷ E') ≫ J.inv := by
    have h := homMixedInterchange_pre (k := k) E E' κ τ Y x hx
    rw [koszulSign_zero_right, one_smul] at h
    rw [Iso.eq_comp_inv, Category.assoc, h, Iso.inv_hom_id_assoc]
  have hg' : J.inv ≫ E ◁ (homParityShift (k := k) κ).map (g ▷ E') =
      (homParityShift (k := k) τ).map ((E ◁ g) ▷ E') ≫ J.inv := by
    have h := homMixedInterchange_naturality_even (k := k) E E' κ τ hg
    rw [Iso.eq_comp_inv, Category.assoc, h, Iso.inv_hom_id_assoc]
  have hcore : J.inv ≫ (x ▷ _ ≫ E ◁ (homParityShift (k := k) κ).map (Y ◁ y)) ≫
      E ◁ (homShiftPostAdjunction A b κ).counit.app H =
      (homParityShift (k := k) τ).map ((x ▷ Y ≫ E ◁ g) ▷ E') ≫ J.inv ≫
        E ◁ (homShiftPostAdjunction A b κ).counit.app H := by
    rw [Category.assoc, ← TwoSupercategory.whiskerLeft_comp (R := k),
      homShiftPostAdjunction_counit_transpose A κ H hy,
      TwoSupercategory.whiskerLeft_comp (R := k), reassoc_of% hx', reassoc_of% hg',
      TwoSupercategory.comp_whiskerRight (R := k), Functor.map_comp, Category.assoc]
  unfold homDistinctMixedMateDot homDistinctMixedMate
  rw [hcore, Functor.map_comp, TwoSupercategory.comp_whiskerRight (R := k)]
  have hn : (x ▷ Y ≫ E ◁ g) ≫ (homShiftPostAdjunction A a τ).unit.app (E ≫ Y) =
      (homShiftPostAdjunction A a τ).unit.app (E ≫ Y) ≫
        (homParityShift (k := k) τ).map
          ((homParityShift (k := k) τ).map ((x ▷ Y ≫ E ◁ g) ▷ E')) ▷ F' :=
    (homShiftPostAdjunction A a τ).unit.naturality _
  rw [← reassoc_of% hn, Category.assoc]

end Mate

section Nilpotent
variable {k : Type r} [CommRing k] {R : Type*} [Ring R] [Algebra k R]

/-- The span of the admissible monomials `aᵖ bᑫ` with `q ≥ m`. -/
def admissibleMonomials (a b : R) (Pa Pb : ℕ → Prop) (m : ℕ) : Submodule k R :=
  Submodule.span k {z | ∃ p q, Pa p ∧ Pb q ∧ m ≤ q ∧ z = a ^ p * b ^ q}

theorem admissibleMonomials_mul {a b : R} {Pa Pb : ℕ → Prop}
    (hPa : ∀ p p', Pa p → Pa p' → Pa (p + p')) (hPb : ∀ q q', Pb q → Pb q' → Pb (q + q'))
    (hc : ∀ p q, Pa p → Pb q → Commute (a ^ p) (b ^ q)) (m n : ℕ) :
    admissibleMonomials (k := k) a b Pa Pb m * admissibleMonomials a b Pa Pb n ≤
      admissibleMonomials a b Pa Pb (m + n) := by
  rw [admissibleMonomials, admissibleMonomials, Submodule.span_mul_span]
  refine Submodule.span_mono ?_
  rintro z ⟨u, ⟨p, q, hp, hq, hm, rfl⟩, w, ⟨p', q', hp', hq', hn, rfl⟩, rfl⟩
  refine ⟨p + p', q + q', hPa p p' hp hp', hPb q q' hq hq', by omega, ?_⟩
  simp only
  rw [pow_add, pow_add, mul_assoc, ← mul_assoc (b ^ q), ← (hc p' q hp' hq).eq]
  simp only [mul_assoc]

/-- A combination of admissible monomials, each divisible by the nilpotent `b`, is
nilpotent. -/
theorem isNilpotent_of_mem_admissibleMonomials {a b : R} {Pa Pb : ℕ → Prop}
    (hPa : ∀ p p', Pa p → Pa p' → Pa (p + p')) (hPb : ∀ q q', Pb q → Pb q' → Pb (q + q'))
    (hc : ∀ p q, Pa p → Pb q → Commute (a ^ p) (b ^ q)) (hb : IsNilpotent b) {N : R}
    (hN : N ∈ admissibleMonomials (k := k) a b Pa Pb 1) : IsNilpotent N := by
  obtain ⟨n, hn⟩ := hb
  have hpow : ∀ m, N ^ (m + 1) ∈ admissibleMonomials (k := k) a b Pa Pb (m + 1) := by
    intro m
    induction m with
    | zero => simpa using hN
    | succ m ih =>
      rw [pow_succ]
      exact admissibleMonomials_mul hPa hPb hc (m + 1) 1 (Submodule.mul_mem_mul ih hN)
  refine ⟨n + 1, ?_⟩
  have hz : admissibleMonomials (k := k) a b Pa Pb (n + 1) = ⊥ := by
    rw [admissibleMonomials, Submodule.span_eq_bot]
    rintro z ⟨p, q, -, -, hq, rfl⟩
    rw [pow_eq_zero_of_le (by omega) hn, mul_zero]
  simpa [hz] using hpow n

/-- (14) for the source polynomial: `c • aᵈ + N` is a unit. -/
theorem isUnit_smul_pow_add_of_mem_admissibleMonomials {a b : R} {Pa Pb : ℕ → Prop}
    (hPa : ∀ p p', Pa p → Pa p' → Pa (p + p')) (hPb : ∀ q q', Pb q → Pb q' → Pb (q + q'))
    (hc : ∀ p q, Pa p → Pb q → Commute (a ^ p) (b ^ q)) (hb : IsNilpotent b)
    (ha : IsUnit a) (c : kˣ) {d : ℕ} (hd : Pa d) {N : R}
    (hN : N ∈ admissibleMonomials (k := k) a b Pa Pb 1) :
    IsUnit ((c : k) • a ^ d + N) := by
  have hu : IsUnit ((c : k) • a ^ d) := by
    rw [Algebra.smul_def]
    exact ((c.isUnit.map (algebraMap k R)).mul (ha.pow d))
  have hcomm : Commute N ((c : k) • a ^ d) := by
    refine Commute.smul_right ?_ _
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hN
    · rintro z ⟨p, q, -, hq, -, rfl⟩
      exact (((Commute.pow_pow_self a d p).symm.mul_left (hc d q hd hq).symm)).symm.symm
    · exact Commute.zero_left _
    · intro z z' _ _ h h'
      exact h.add_left h'
    · intro s z _ h
      exact h.smul_left s
  exact (isNilpotent_of_mem_admissibleMonomials hPa hPb hc hb hN).isUnit_add_left_of_commute
    hu hcomm

end Nilpotent
end OddMath.SKM
