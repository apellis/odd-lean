import OddMath.SKM.RouquierHomDistinctMixedPostDots
import OddMath.SKM.RouquierCoupled

/-!
# Invertibility of the post-side dotted mixed mate

This is (13)–(15) of `docs/Nondegeneracy/SwappedDistinctMixedMates.md` on the post side: the
crossing is `J⁻¹` followed by a polynomial `Φ` in the two dots `X = x ▷ _` (on the
precomposed edge `E`) and `Y = E ◁ Π^κ(_ ◁ y)` (on the postcomposed edge `E'`). Every
monomial `Xᵖ Yᑫ` moves to the source side of the undotted mate `U = homDistinctMixedMate` as
`Aᵖ Bᑫ`, where `A = x ▷ _` and `B = E ◁ (Π^κ H ◁ yᵀ)` with `yᵀ` the right transpose of `y`
along `E' ⊣ F'` (`homDistinctMixedMateDot_pow_mul_pow`). If `x` is invertible, `y` is
nilpotent and `Φ = c • Xᵈ + N` with `c` a unit and `N` a combination of monomials with a
positive power of `Y`, the source polynomial is a unit and the dotted mate is invertible
(`homDistinctMixedMateDot_isIso`).
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Powers
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B] in
/-- A functor preserves vertical powers. -/
theorem map_rouquierPower {C : Type*} [Category C] {a b : B} (G : (a ⟶ b) ⥤ C)
    {E : a ⟶ b} (x : E ⟶ E) (n : ℕ) :
    G.map (rouquierPower x n) = (show End (G.obj E) from G.map x) ^ n := by
  induction n with
  | zero => exact G.map_id E
  | succ n ih => rw [rouquierPower_succ, G.map_comp, ih, pow_succ', End.mul_def]

/-- The right transpose of a nilpotent even endomorphism is nilpotent. -/
theorem isNilpotent_rightTranspose {a b : B} {E : a ⟶ b} {F : b ⟶ a}
    (A : SuperAdjunction (k := k) E F) {y : E ⟶ E} (hy : y ∈ parity (R := k) _ _ 0)
    (hn : IsNilpotent (show End E from y)) :
    IsNilpotent (show End F from SuperAdjunction.rightTranspose A A y) := by
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  have h := SuperAdjunction.rightTranspose_power A hy n
  rw [rouquierPower_eq_pow, hn, koszulSign_zero_left, one_pow, one_smul,
    rouquierPower_eq_pow] at h
  rw [← h]
  exact (SuperAdjunction.rightTransposeLinear A A).map_zero

end Powers

section Mate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)
  {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0) {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0)

/-- The pre dot on the target of `J⁻¹`. -/
abbrev mixedPostTargetPreDot (x : E ⟶ E) :
    End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')) :=
  x ▷ (homParityShift (k := k) κ).obj (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')

/-- The post dot on the target of `J⁻¹`. -/
abbrev mixedPostTargetPostDot (y : E' ⟶ E') :
    End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')) :=
  E ◁ (homParityShift (k := k) κ).map (((homParityShift (k := k) κ).obj H ≫ F') ◁ y)

/-- The pre dot on the source of `U`. -/
abbrev mixedPostSourcePreDot (x : E ⟶ E) :
    End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) :=
  x ▷ ((homParityShift (k := k) κ).obj H ≫ F')

/-- The transposed post dot on the source of `U`. -/
abbrev mixedPostSourcePostDot (A : SuperAdjunction (k := k) E' F') (y : E' ⟶ E') :
    End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) :=
  E ◁ ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)

include hx in
theorem commute_mixedPostTarget :
    Commute (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y) :=
  (TwoSupercategory.whisker_exchange_of_even_left (R := k) hx _).symm

include hx in
theorem commute_mixedPostSource :
    Commute (mixedPostSourcePreDot (k := k) E κ H (F' := F') x)
      (mixedPostSourcePostDot (k := k) E κ H A y) :=
  (TwoSupercategory.whisker_exchange_of_even_left (R := k) hx _).symm

include hx hy in
/-- (13) for a monomial: `Xᵖ Yᑫ` moves to `Aᵖ Bᑫ` on the source side of `U`. -/
theorem homDistinctMixedMateDot_pow_mul_pow (p q : ℕ) :
    homDistinctMixedMateDot E A κ τ H
        (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ p *
          mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q) =
      (mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ p *
          mixedPostSourcePostDot (k := k) E κ H A y ^ q :
          End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) ≫
        homDistinctMixedMate E A κ τ H := by
  have hxp : rouquierPower x p ∈ parity (R := k) E E 0 := by
    simpa using rouquierPower_mem (k := k) hx p
  have hyq : rouquierPower y q ∈ parity (R := k) E' E' 0 := by
    simpa using rouquierPower_mem (k := k) hy q
  have ht := ((commute_mixedPostTarget (k := k) E κ H (F' := F') hx (y := y)).pow_pow p q).eq
  have hs := ((commute_mixedPostSource (k := k) E A κ H hx (y := y)).pow_pow p q).eq
  set Y := (homParityShift (k := k) κ).obj H ≫ F'
  have hY : mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q =
      E ◁ (homParityShift (k := k) κ).map (Y ◁ rouquierPower y q) := by
    rw [whiskerLeft_rouquierPower (k := k), rouquierPower_eq_pow, ← map_rouquierPower,
      rouquierPower_eq_pow, whiskerLeft_rouquierPower (k := k)]
  have hB : mixedPostSourcePostDot (k := k) E κ H A y ^ q =
      E ◁ ((homParityShift (k := k) κ).obj H ◁
        rouquierPower (SuperAdjunction.rightTranspose A A y) q) := by
    rw [whiskerLeft_rouquierPower (k := k), rouquierPower_eq_pow,
      whiskerLeft_rouquierPower (k := k)]
  rw [ht, hs, End.mul_def, End.mul_def, whiskerRight_rouquierPower (k := k),
    whiskerRight_rouquierPower (k := k), hY, hB,
    homDistinctMixedMateDot_monomial E A κ τ H hxp hyq,
    SuperAdjunction.rightTranspose_power A hy q, koszulSign_zero_left, one_pow, one_smul]

include hx hy in
/-- The source polynomial: `Dot Φ = Ψ ≫ U` with `Ψ` an admissible combination of the
source monomials, when `Φ` is an admissible combination of the target monomials. -/
theorem exists_homDistinctMixedMateDot_eq (m : ℕ) {N}
    (hN : N ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y) (fun _ => True) (fun _ => True) m) :
    ∃ Ψ ∈ admissibleMonomials (k := k)
      (mixedPostSourcePreDot (k := k) E κ H (F' := F') x)
      (mixedPostSourcePostDot (k := k) E κ H A y) (fun _ => True) (fun _ => True) m,
      homDistinctMixedMateDot E A κ τ H N = Ψ ≫ homDistinctMixedMate E A κ τ H := by
  induction hN using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, -, -, hm, rfl⟩ := hz
    exact ⟨_, Submodule.subset_span ⟨p, q, trivial, trivial, hm, rfl⟩,
      homDistinctMixedMateDot_pow_mul_pow E A κ τ H hx hy p q⟩
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [← homDistinctMixedMateDotLinear_apply, map_zero, Limits.zero_comp]
  | add z z' _ _ h h' =>
    obtain ⟨Ψ, hΨ, e⟩ := h
    obtain ⟨Ψ', hΨ', e'⟩ := h'
    refine ⟨Ψ + Ψ', Submodule.add_mem _ hΨ hΨ', ?_⟩
    rw [← homDistinctMixedMateDotLinear_apply, map_add, homDistinctMixedMateDotLinear_apply,
      homDistinctMixedMateDotLinear_apply, e, e', Preadditive.add_comp]
  | smul s z _ h =>
    obtain ⟨Ψ, hΨ, e⟩ := h
    refine ⟨s • Ψ, Submodule.smul_mem _ s hΨ, ?_⟩
    rw [← homDistinctMixedMateDotLinear_apply, map_smul, homDistinctMixedMateDotLinear_apply,
      e, Linear.smul_comp]

include hx hy in
/-- (15) on the post side: the dotted mate of `c • Xᵈ + N` is invertible when `x` is
invertible, `y` is nilpotent, `c` is a unit and `N` is a combination of monomials `Xᵖ Yᑫ`
with `q ≥ 1`. -/
theorem homDistinctMixedMateDot_isIso [IsIso x] (hn : IsNilpotent (show End E' from y))
    (c : kˣ) (e : ℕ) {N}
    (hN : N ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y) (fun _ => True) (fun _ => True) 1) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((c : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ e + N)) := by
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_homDistinctMixedMateDot_eq E A κ τ H hx hy 1 hN
  have h0 := homDistinctMixedMateDot_pow_mul_pow E A κ τ H hx hy e 0
  simp only [pow_zero, mul_one] at h0
  rw [← homDistinctMixedMateDotLinear_apply, map_add, map_smul,
    homDistinctMixedMateDotLinear_apply, homDistinctMixedMateDotLinear_apply, h0, hΨe,
    ← Linear.smul_comp, ← Preadditive.add_comp]
  have ha : IsUnit (mixedPostSourcePreDot (k := k) E κ H (F' := F') x) := by
    refine ⟨⟨_, inv x ▷ ((homParityShift (k := k) κ).obj H ≫ F'), ?_, ?_⟩, rfl⟩ <;>
      rw [End.mul_def, ← TwoSupercategory.comp_whiskerRight (R := k)] <;>
      simp only [IsIso.hom_inv_id, IsIso.inv_hom_id] <;>
      exact TwoSupercategory.id_whiskerRight (R := k) _ _
  have hb : IsNilpotent (mixedPostSourcePostDot (k := k) E κ H A y) := by
    obtain ⟨n, hn'⟩ := isNilpotent_rightTranspose A hy hn
    refine ⟨n, ?_⟩
    rw [← rouquierPower_eq_pow] at hn'
    rw [whiskerLeft_rouquierPower (k := k), rouquierPower_eq_pow,
      whiskerLeft_rouquierPower (k := k), hn']
    rw [whiskerLeft_zero' (k := k), whiskerLeft_zero' (k := k)]
  have hu := isUnit_smul_pow_add_of_mem_admissibleMonomials (k := k)
    (Pa := fun _ => True) (Pb := fun _ => True) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun p q _ _ => (commute_mixedPostSource (k := k) E A κ H hx (y := y)).pow_pow p q)
    hb ha c (d := e) trivial hΨ
  have : IsIso ((c : k) • mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ e + Ψ :
      End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) := (isUnit_iff_isIso _).mp hu
  infer_instance

end Mate
end OddMath.SKM
