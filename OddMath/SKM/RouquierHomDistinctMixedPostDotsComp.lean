import OddMath.SKM.RouquierHomDistinctMixedPostDotsIso

/-!
# The post-side dotted mixed mate with an arbitrary crossing

This extends (13)–(15) of `docs/Nondegeneracy/SwappedDistinctMixedMates.md` on the post side
from polynomial crossings to an arbitrary endomorphism `Φ` of the target of `J⁻¹`. A pre dot
`X = x ▷ _` in front of `Φ` moves to the source pre dot `A = x ▷ _` of the dotted mate for every
`Φ` (`homDistinctMixedMateDot_preDot_comp`). A post dot `Y = E ◁ Π^κ(_ ◁ y)` in front of `Φ`
moves to the transposed source dot `B = E ◁ (Π^κ H ◁ yᵀ)` when `Φ` commutes with `Y` and with
the transposed target dot `Γ = E ◁ Π^κ((Π^κ H ◁ yᵀ) ▷ E')`
(`homDistinctMixedMateDot_postDot_comp`). Hence an admissible polynomial `N` in front of `Φ`
moves to an admissible source polynomial (`exists_homDistinctMixedMateDot_comp_eq`).

`homDistinctMixedMateDot_isIso_of_comp`: if `x` is invertible, `y` is nilpotent, `Φ` commutes
with `Y` and `Γ`, and `(c • Xᵈ + N) ≫ Φ = c' • Xᵉ + N'` with `c`, `c'` units and `N`, `N'`
combinations of monomials with a positive power of `Y`, then the dotted mate of `Φ` is
invertible. This is the case of a crossing that is the inverse of a polynomial up to a
polynomial factor, for instance `a = (y - x)⁻¹`.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Mate
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)

/-- The transposed post dot on the target of `J⁻¹`. -/
abbrev mixedPostTargetTransposeDot (A : SuperAdjunction (k := k) E' F') (y : E' ⟶ E') :
    End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')) :=
  E ◁ (homParityShift (k := k) κ).map
    (((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y) ▷ E')

/-- A pre dot in front of the crossing moves to the source of the dotted mate. -/
theorem homDistinctMixedMateDot_preDot_comp {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) :
    homDistinctMixedMateDot E A κ τ H
        (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ≫ Φ) =
      mixedPostSourcePreDot (k := k) E κ H (F' := F') x ≫ homDistinctMixedMateDot E A κ τ H Φ := by
  have hx' : (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫ x ▷ _ = (homParityShift (k := k) τ).map ((x ▷ ((homParityShift (k := k) κ).obj H ≫ F')) ▷ E') ≫ (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv := by
    have h := homMixedInterchange_pre (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F') x hx
    rw [koszulSign_zero_right, one_smul] at h
    rw [Iso.eq_comp_inv, Category.assoc, h, Iso.inv_hom_id_assoc]
  unfold homDistinctMixedMateDot
  rw [Category.assoc, reassoc_of% hx', Functor.map_comp, TwoSupercategory.comp_whiskerRight (R := k)]
  have hn : (x ▷ ((homParityShift (k := k) κ).obj H ≫ F')) ≫ (homShiftPostAdjunction A a τ).unit.app (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) =
      (homShiftPostAdjunction A a τ).unit.app (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫
        (homParityShift (k := k) τ).map
          ((homParityShift (k := k) τ).map ((x ▷ ((homParityShift (k := k) κ).obj H ≫ F')) ▷ E')) ▷ F' :=
    (homShiftPostAdjunction A a τ).unit.naturality _
  rw [← reassoc_of% hn]

/-- The post dot and the transposed post dot on the target of `J⁻¹` commute. -/
theorem commute_mixedPostTargetPostDot_transposeDot {y : E' ⟶ E'}
    (hy : y ∈ parity (R := k) E' E' 0) :
    Commute (mixedPostTargetPostDot (k := k) E κ H (F' := F') y)
      (mixedPostTargetTransposeDot (k := k) E κ H A y) := by
  have hyT := SuperAdjunction.rightTranspose_mem A A hy
  have hg := TwoSupercategory.whiskerLeft_mem ((homParityShift (k := k) κ).obj H) hyT
  change _ ≫ _ = _ ≫ _
  rw [← TwoSupercategory.whiskerLeft_comp (R := k), ← TwoSupercategory.whiskerLeft_comp (R := k),
    ← Functor.map_comp, ← Functor.map_comp,
    TwoSupercategory.whisker_exchange_of_even_left (R := k) hg]

/-- A post dot in front of a crossing that commutes with it and with its transpose moves to the
transposed source dot of the dotted mate. -/
theorem homDistinctMixedMateDot_postDot_comp {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0)
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')))
    (h₁ : Commute Φ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y))
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y)) :
    homDistinctMixedMateDot E A κ τ H
        (mixedPostTargetPostDot (k := k) E κ H (F' := F') y ≫ Φ) =
      mixedPostSourcePostDot (k := k) E κ H A y ≫ homDistinctMixedMateDot E A κ τ H Φ := by
  have hg : (homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y ∈
      parity (R := k) ((homParityShift (k := k) κ).obj H ≫ F') ((homParityShift (k := k) κ).obj H ≫ F') 0 :=
    TwoSupercategory.whiskerLeft_mem _ (SuperAdjunction.rightTranspose_mem A A hy)
  have hg' : (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫ E ◁ (homParityShift (k := k) κ).map (((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y) ▷ E') =
      (homParityShift (k := k) τ).map ((E ◁ ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) ▷ E') ≫ (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv := by
    have h := homMixedInterchange_naturality_even (k := k) E E' κ τ hg
    rw [Iso.eq_comp_inv, Category.assoc, h, Iso.inv_hom_id_assoc]
  have e₁ : mixedPostTargetPostDot (k := k) E κ H (F' := F') y ≫ Φ =
      Φ ≫ mixedPostTargetPostDot (k := k) E κ H (F' := F') y := h₁.eq
  have e₂ : mixedPostTargetTransposeDot (k := k) E κ H A y ≫ Φ =
      Φ ≫ mixedPostTargetTransposeDot (k := k) E κ H A y := h₂.eq
  have hcore : (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y ≫ Φ) ≫
      E ◁ (homShiftPostAdjunction A b κ).counit.app H =
      (homParityShift (k := k) τ).map ((E ◁ ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) ▷ E') ≫ (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫ Φ ≫
        E ◁ (homShiftPostAdjunction A b κ).counit.app H := by
    rw [e₁, Category.assoc]
    dsimp only [mixedPostTargetPostDot]
    rw [← TwoSupercategory.whiskerLeft_comp (R := k),
      homShiftPostAdjunction_counit_transpose A κ H hy,
      TwoSupercategory.whiskerLeft_comp (R := k)]
    change (homMixedInterchange (k := k) E E' κ τ ((homParityShift (k := k) κ).obj H ≫ F')).inv ≫ Φ ≫ mixedPostTargetTransposeDot (k := k) E κ H A y ≫ _ = _
    rw [← reassoc_of% e₂, ← reassoc_of% hg']
  unfold homDistinctMixedMateDot
  rw [hcore, Functor.map_comp, TwoSupercategory.comp_whiskerRight (R := k)]
  have hn : (E ◁ ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) ≫ (homShiftPostAdjunction A a τ).unit.app (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) =
      (homShiftPostAdjunction A a τ).unit.app (E ≫ ((homParityShift (k := k) κ).obj H ≫ F')) ≫
        (homParityShift (k := k) τ).map
          ((homParityShift (k := k) τ).map ((E ◁ ((homParityShift (k := k) κ).obj H ◁ SuperAdjunction.rightTranspose A A y)) ▷ E')) ▷ F' :=
    (homShiftPostAdjunction A a τ).unit.naturality _
  rw [← reassoc_of% hn]

theorem homDistinctMixedMateDot_preDot_pow_comp {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    (p : ℕ) (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) :
    homDistinctMixedMateDot E A κ τ H
        ((mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ p) ≫ Φ) =
      (mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ p :
        End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) ≫
        homDistinctMixedMateDot E A κ τ H Φ := by
  induction p with
  | zero => rw [pow_zero, pow_zero, End.one_def, End.one_def, Category.id_comp, Category.id_comp]
  | succ p ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, Category.assoc, Category.assoc,
      homDistinctMixedMateDot_preDot_comp E A κ τ H hx, ih]

theorem homDistinctMixedMateDot_postDot_pow_comp {y : E' ⟶ E'}
    (hy : y ∈ parity (R := k) E' E' 0) (q : ℕ)
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')))
    (h₁ : Commute Φ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y))
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y)) :
    homDistinctMixedMateDot E A κ τ H
        ((mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q) ≫ Φ) =
      (mixedPostSourcePostDot (k := k) E κ H A y ^ q :
        End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) ≫
        homDistinctMixedMateDot E A κ τ H Φ := by
  induction q with
  | zero => rw [pow_zero, pow_zero, End.one_def, End.one_def, Category.id_comp, Category.id_comp]
  | succ q ih =>
    have hc := commute_mixedPostTargetPostDot_transposeDot E A κ H hy
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, Category.assoc, Category.assoc,
      homDistinctMixedMateDot_postDot_comp E A κ τ H hy, ih]
    · change Commute (Φ * _) _
      exact h₁.mul_left (Commute.pow_left (Commute.refl _) q)
    · change Commute (Φ * _) _
      exact h₂.mul_left (hc.pow_left q)

/-- An admissible monomial in front of the crossing moves to the source. -/
theorem homDistinctMixedMateDot_pow_mul_pow_comp {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0) (p q : ℕ)
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')))
    (h₁ : Commute Φ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y))
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y)) :
    homDistinctMixedMateDot E A κ τ H
        ((mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ p *
          mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q :
          End (E ≫ (homParityShift (k := k) κ).obj
            (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) ≫ Φ) =
      (mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ p *
          mixedPostSourcePostDot (k := k) E κ H A y ^ q :
          End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) ≫
        homDistinctMixedMateDot E A κ τ H Φ := by
  have ht := ((commute_mixedPostTarget (k := k) E κ H (F' := F') hx (y := y)).pow_pow p q).eq
  have hs := ((commute_mixedPostSource (k := k) E A κ H hx (y := y)).pow_pow p q).eq
  rw [ht, hs, End.mul_def, End.mul_def, Category.assoc,
    homDistinctMixedMateDot_preDot_pow_comp E A κ τ H hx,
    homDistinctMixedMateDot_postDot_pow_comp E A κ τ H hy q Φ h₁ h₂, Category.assoc]

/-- An admissible polynomial in front of the crossing moves to an admissible source
polynomial. -/
theorem exists_homDistinctMixedMateDot_comp_eq {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0) (m : ℕ)
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')))
    (h₁ : Commute Φ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y))
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y)) {N}
    (hN : N ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y) (fun _ => True) (fun _ => True) m) :
    ∃ Ψ ∈ admissibleMonomials (k := k)
      (mixedPostSourcePreDot (k := k) E κ H (F' := F') x)
      (mixedPostSourcePostDot (k := k) E κ H A y) (fun _ => True) (fun _ => True) m,
      homDistinctMixedMateDot E A κ τ H (N ≫ Φ) = Ψ ≫ homDistinctMixedMateDot E A κ τ H Φ := by
  induction hN using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, q, -, -, hm, rfl⟩ := hz
    exact ⟨_, Submodule.subset_span ⟨p, q, trivial, trivial, hm, rfl⟩,
      homDistinctMixedMateDot_pow_mul_pow_comp E A κ τ H hx hy p q Φ h₁ h₂⟩
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [Limits.zero_comp, ← homDistinctMixedMateDotLinear_apply, map_zero, Limits.zero_comp]
  | add z z' _ _ h h' =>
    obtain ⟨Ψ, hΨ, e⟩ := h
    obtain ⟨Ψ', hΨ', e'⟩ := h'
    refine ⟨Ψ + Ψ', Submodule.add_mem _ hΨ hΨ', ?_⟩
    rw [Preadditive.add_comp, ← homDistinctMixedMateDotLinear_apply, map_add,
      homDistinctMixedMateDotLinear_apply, homDistinctMixedMateDotLinear_apply, e, e',
      Preadditive.add_comp]
  | smul s z _ h =>
    obtain ⟨Ψ, hΨ, e⟩ := h
    refine ⟨s • Ψ, Submodule.smul_mem _ s hΨ, ?_⟩
    rw [Linear.smul_comp, ← homDistinctMixedMateDotLinear_apply, map_smul,
      homDistinctMixedMateDotLinear_apply, e, Linear.smul_comp]

/-- The dotted mate of a crossing `Φ` is invertible when an admissible unit polynomial in front
of `Φ` gives another one: `(c • Xᵈ + N) ≫ Φ = c' • Xᵉ + N'`, with `x` invertible, `y`
nilpotent, and `Φ` commuting with the post dot and its transpose. -/
theorem homDistinctMixedMateDot_isIso_of_comp {x : E ⟶ E} (hx : x ∈ parity (R := k) E E 0)
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' 0) [IsIso x]
    (hn : IsNilpotent (show End E' from y))
    (Φ : End (E ≫ (homParityShift (k := k) κ).obj
      (((homParityShift (k := k) κ).obj H ≫ F') ≫ E')))
    (h₁ : Commute Φ (mixedPostTargetPostDot (k := k) E κ H (F' := F') y))
    (h₂ : Commute Φ (mixedPostTargetTransposeDot (k := k) E κ H A y))
    (c c' : kˣ) (d e : ℕ) {N N'}
    (hN : N ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y) (fun _ => True) (fun _ => True) 1)
    (hN' : N' ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y) (fun _ => True) (fun _ => True) 1)
    (h : ((c : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ d + N) ≫ Φ =
      (c' : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ e + N') :
    IsIso (homDistinctMixedMateDot E A κ τ H Φ) := by
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_homDistinctMixedMateDot_comp_eq E A κ τ H hx hy 1 Φ h₁ h₂ hN
  have h0 := homDistinctMixedMateDot_pow_mul_pow_comp E A κ τ H hx hy d 0 Φ h₁ h₂
  simp only [pow_zero, mul_one] at h0
  have hR : IsIso (homDistinctMixedMateDot E A κ τ H
      ((c' : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ e + N')) :=
    homDistinctMixedMateDot_isIso E A κ τ H hx hy hn c' e hN'
  rw [← h, Preadditive.add_comp, Linear.smul_comp, ← homDistinctMixedMateDotLinear_apply,
    map_add, map_smul, homDistinctMixedMateDotLinear_apply, homDistinctMixedMateDotLinear_apply,
    h0, hΨe, ← Linear.smul_comp, ← Preadditive.add_comp] at hR
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
    hb ha c (d := d) trivial hΨ
  have : IsIso ((c : k) • mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ d + Ψ :
      End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) := (isUnit_iff_isIso _).mp hu
  exact IsIso.of_isIso_comp_left
    ((c : k) • mixedPostSourcePreDot (k := k) E κ H (F' := F') x ^ d + Ψ :
      End (E ≫ ((homParityShift (k := k) κ).obj H ≫ F'))) _

end Mate
end OddMath.SKM
