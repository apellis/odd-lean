/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightMixedSlides
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightMixedInductionSquare
import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierMateKernel
import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierData

/-!
# The distinct-colour quadratic relation on the global weight factors

Brundan–Ellis, *Super Kac–Moody 2-categories* (arXiv:1701.04133v2), relation (1.7) for
`i ≠ j`, for the cyclotomic global action on weight factors, with the parameters of
`parameterTwist`.

* `heightContentMixedSquareNe`, `heightContentMixedSquareZero`: the relation on content
  blocks, with arbitrary height and content transports, from `heightInduction_square_ne`,
  `heightInduction_square_zero`.
* `globalActionCross_square_ne`, `globalActionCross_square_zero`: the relation for the
  weight-level crossings.
* `globalActionSignedCross_square_ne`, `globalActionSignedCross_square_zero`: the `quadNe` and
  `quadZero` fields of `RouquierMulticolour` for the crossing of `globalRouquierData`, with the
  scalars `parameterTwist D Sc`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

/-! ### Powers of endomorphisms -/

section EndoPower

theorem endoPower_map {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {Y : 𝒞}
    (f : Y ⟶ Y) (m : ℕ) : F.map (endoPower f m) = endoPower (F.map f) m := by
  induction m with
  | zero => exact F.map_id Y
  | succ m ih => rw [endoPower_succ, endoPower_succ, F.map_comp, ih]

theorem endoPower_pi_apply {J : Type*} {C : J → Type*} [∀ j, Category (C j)]
    {P : ∀ j, C j} (f : P ⟶ P) (m : ℕ) (j : J) : endoPower f m j = endoPower (f j) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [endoPower_succ, endoPower_succ, ← ih]
    rfl

theorem endoPower_fullSubcategory_hom {C₀ : Type*} [Category C₀] {P : ObjectProperty C₀}
    {Y : P.FullSubcategory} (f : Y ⟶ Y) (m : ℕ) : (endoPower f m).hom = endoPower f.hom m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [endoPower_succ, endoPower_succ, ObjectProperty.FullSubcategory.comp_hom, ih]

theorem endoPower_eqToHom_conj {𝒞 : Type*} [Category 𝒞] {O Y : 𝒞} (e : O = Y) (f : Y ⟶ Y)
    (m : ℕ) : endoPower (eqToHom e ≫ f ≫ eqToHom e.symm) m =
      eqToHom e ≫ endoPower f m ≫ eqToHom e.symm := by
  subst e
  simp

theorem eqToHom_conj_comp {𝒞 : Type*} [Category 𝒞] {O Y : 𝒞} (e : O = Y) (f g : Y ⟶ Y) :
    (eqToHom e ≫ f ≫ eqToHom e.symm) ≫ (eqToHom e ≫ g ≫ eqToHom e.symm) =
      eqToHom e ≫ (f ≫ g) ≫ eqToHom e.symm := by
  subst e
  simp

theorem eqToHom_conj_smul {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] {O Y : 𝒞}
    (e : O = Y) (r : k) (f : Y ⟶ Y) :
    r • (eqToHom e ≫ f ≫ eqToHom e.symm) = eqToHom e ≫ (r • f) ≫ eqToHom e.symm := by
  subst e
  simp

theorem eqToHom_conj_add {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {O Y : 𝒞}
    (e : O = Y) (f g : Y ⟶ Y) :
    eqToHom e ≫ f ≫ eqToHom e.symm + eqToHom e ≫ g ≫ eqToHom e.symm =
      eqToHom e ≫ (f + g) ≫ eqToHom e.symm := by
  subst e
  simp

theorem eqToHom_conj_sum {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {O Y : 𝒞}
    (e : O = Y) {ι : Type*} (s : Finset ι) (f : ι → (Y ⟶ Y)) :
    ∑ x ∈ s, eqToHom e ≫ f x ≫ eqToHom e.symm = eqToHom e ≫ (∑ x ∈ s, f x) ≫ eqToHom e.symm := by
  subst e
  simp

end EndoPower

/-! ### Components in `𝔖ℭ𝔞𝔱` and in products -/

section Components
variable {A B : SCat k}

omit [Fintype I] in
theorem scat_rouquierPower_app {F : A ⟶ B} {x : F ⟶ F} {p : ZMod 2}
    (hx : x ∈ parity (R := k) F F p) (m : ℕ) (Z : A.carrier) :
    (SKM.rouquierPower x m).app ((m : ZMod 2) * p) Z = endoPower (x.app p Z) m := by
  induction m with
  | zero => simp [SKM.rouquierPower, endoPower]
  | succ m ih =>
    have hP : SKM.rouquierPower x m ∈ parity (R := k) F F ((m : ZMod 2) * p) := by
      clear ih
      induction m with
      | zero => rw [Nat.cast_zero, zero_mul]; exact id_mem (R := k) _
      | succ m ih' =>
        have hc := comp_mem ih' hx
        rwa [show (m : ZMod 2) * p + p = ((m + 1 : ℕ) : ZMod 2) * p by push_cast; ring] at hc
    rw [show SKM.rouquierPower x (m + 1) = SKM.rouquierPower x m ≫ x from rfl,
      show ((m + 1 : ℕ) : ZMod 2) * p = (m : ZMod 2) * p + p by push_cast; ring,
      scat_comp_app_of_mem hP hx, ih, endoPower_succ]

omit [Fintype I] in
theorem scat_rouquierPower_mem {F : A ⟶ B} {x : F ⟶ F} {p : ZMod 2}
    (hx : x ∈ parity (R := k) F F p) (m : ℕ) :
    SKM.rouquierPower x m ∈ parity (R := k) F F ((m : ZMod 2) * p) := by
  induction m with
  | zero => rw [Nat.cast_zero, zero_mul]; exact id_mem (R := k) _
  | succ m ih =>
    have hc := comp_mem ih hx
    rwa [show (m : ZMod 2) * p + p = ((m + 1 : ℕ) : ZMod 2) * p by push_cast; ring] at hc

omit [Fintype I] in
theorem scat_sum_app {F G : A ⟶ B} {ι : Type*} (s : Finset ι) (x : ι → (F ⟶ G)) (p : ZMod 2)
    (Z : A.carrier) : (∑ t ∈ s, x t).app p Z = ∑ t ∈ s, (x t).app p Z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert t s ht ih => rw [Finset.sum_insert ht, Finset.sum_insert ht, SCat.add_app, ih]

omit [Fintype I] in
/-- Two even 2-morphisms of `𝔖ℭ𝔞𝔱` agree once their even components agree. -/
theorem scat_eq_of_even {F G : A ⟶ B} {x y : F ⟶ G} (hx : x ∈ parity (R := k) F G 0)
    (hy : y ∈ parity (R := k) F G 0) (h : ∀ Z, x.app 0 Z = y.app 0 Z) : x = y := by
  apply SCat.hom_ext
  · exact h
  · intro Z
    rw [Superfunctor.app_eq_zero_of_mem hx (by decide) Z,
      Superfunctor.app_eq_zero_of_mem hy (by decide) Z]

omit [Fintype I] in
theorem pi_add_apply' {J : Type*} {C : J → Type*} [∀ j, Category (C j)]
    [∀ j, Preadditive (C j)] {P Q : ∀ j, C j} (f g : P ⟶ Q) (j : J) :
    (f + g) j = f j + g j := rfl

omit [Fintype I] in
theorem pi_smul_apply' {J : Type*} {C : J → Type*} [∀ j, Category (C j)]
    [∀ j, Preadditive (C j)] [∀ j, Linear k (C j)] {P Q : ∀ j, C j} (r : k) (f : P ⟶ Q)
    (j : J) : (r • f) j = r • f j := rfl

omit [Fintype I] in
theorem pi_sum_apply' {J : Type*} {C : J → Type*} [∀ j, Category (C j)]
    [∀ j, Preadditive (C j)] {P Q : ∀ j, C j} {ι : Type*} (s : Finset ι) (f : ι → (P ⟶ Q))
    (j : J) : (∑ t ∈ s, f t) j = ∑ t ∈ s, f t j := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert t s ht ih => rw [Finset.sum_insert ht, Finset.sum_insert ht, pi_add_apply', ih]

omit [Fintype I] in
theorem smul_congr_of_ne {V : Type*} [AddCommMonoid V] [Module k V] (c : k) {x y : V}
    (h : c ≠ 0 → x = y) : c • x = c • y := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [h hc]

omit [Fintype I] in
theorem scat_comp_app_of_mem' {F G H : A ⟶ B} {x : F ⟶ G} {y : G ⟶ H} {s t r : ZMod 2}
    (hx : x ∈ parity (R := k) F G s) (hy : y ∈ parity (R := k) G H t) (h : s + t = r)
    (Z : A.carrier) : (x ≫ y).app r Z = x.app s Z ≫ y.app t Z := by
  subst h
  exact scat_comp_app_of_mem hx hy Z

omit [Fintype I] in
theorem scat_rouquierPower_app' {F : A ⟶ B} {x : F ⟶ F} {p q : ZMod 2}
    (hx : x ∈ parity (R := k) F F p) (m : ℕ) (h : (m : ZMod 2) * p = q) (Z : A.carrier) :
    (SKM.rouquierPower x m).app q Z = endoPower (x.app p Z) m := by
  subst h
  exact scat_rouquierPower_app hx m Z

omit [Fintype I] in
theorem scat_rouquierPower_mem' {F : A ⟶ B} {x : F ⟶ F} {p q : ZMod 2}
    (hx : x ∈ parity (R := k) F F p) (m : ℕ) (h : (m : ZMod 2) * p = q) :
    SKM.rouquierPower x m ∈ parity (R := k) F F q := by
  subst h
  exact scat_rouquierPower_mem hx m

omit [Fintype I] in
theorem endoPower_scat_map {C : SCat k} (G : B ⟶ C) {Y : B.carrier} (f : Y ⟶ Y) (m : ℕ) :
    G.map (endoPower f m) = endoPower (G.map f) m :=
  endoPower_map G.toFunctor f m

end Components

section ContentHom
variable (i : I) (n : ℕ) (β : Multiset I)

theorem heightContentInductionDot_app_hom (p : ZMod 2)
    (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) :
    ((heightContentDot D Sc i a ha n β).app p M).hom =
      (heightSuperInductionDot D Sc i a ha n).app p M.obj := rfl

theorem heightContentInduction_map_hom'
    {M M' : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)}
    (f : M ⟶ M') :
    ((heightContentInduction D Sc i a ha n β).map f).hom =
      (heightSuperInduction D Sc i a ha n).map f.hom := rfl

theorem heightContentInduction_obj_obj'
    (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha n β)) :
    ((heightContentInduction D Sc i a ha n β).obj M).obj =
      (heightSuperInduction D Sc i a ha n).obj M.obj := rfl

end ContentHom

/-! ### Content blocks -/

section Content
variable {i j : I} (hij : i ≠ j)
include hij

attribute [local irreducible] ContentSupported SuperBimodule.tensor

/-- **The distinct-colour quadratic relation on content blocks**, `d_{ij} ≠ 0`, with arbitrary
height and content transports. -/
theorem heightContentMixedSquareNe (hd : D.d i j ≠ 0) (m₀ : ℕ) (γ₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₀ γ₀))
    {m₁ m₂ : ℕ} {γ₁ γ₂ : Multiset I}
    (p₁ : m₀ + 1 = m₁) (q₁ : {j} + γ₀ = γ₁) (p₂ : m₁ + 1 = m₂) (q₂ : {i} + γ₁ = γ₂)
    (hc : {i} + ({j} + γ₀) = γ₂) (hc' : {j} + ({i} + γ₀) = γ₂) (pX : m₀ + 1 + 1 = m₂)
    (O : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₂ γ₂)) :
    ∀ (a₁ : O = _) (a₂ : _ = _) (a₃ : _ = O)
      (b : O = (heightContentCast D Sc a ha p₂ q₂).obj
        ((heightContentInduction D Sc i a ha m₁ γ₁).obj
          ((heightContentCast D Sc a ha p₁ q₁).obj
            ((heightContentInduction D Sc j a ha m₀ γ₀).obj N)))),
    eqToHom a₁ ≫ (heightContentCast D Sc a ha pX rfl).map
          ((heightBlockCross D Sc a ha i j m₀ γ₀ γ₂ hc).app (D.parity i * D.parity j) N) ≫
        eqToHom a₂ ≫ (heightContentCast D Sc a ha pX rfl).map
          ((heightBlockCross D Sc a ha j i m₀ γ₀ γ₂ hc').app (D.parity j * D.parity i) N) ≫
        eqToHom a₃ =
      eqToHom b ≫
        (((parameterTwist D Sc).t i j : k) • endoPower (Y := (heightContentCast D Sc a ha p₂ q₂).obj
                ((heightContentInduction D Sc i a ha m₁ γ₁).obj
                  ((heightContentCast D Sc a ha p₁ q₁).obj
                    ((heightContentInduction D Sc j a ha m₀ γ₀).obj N))))
            ((heightContentCastTrans D Sc a ha p₂ q₂
              (heightContentDot D Sc i a ha m₁ γ₁)).app (D.parity i)
              ((heightContentCast D Sc a ha p₁ q₁).obj
                ((heightContentInduction D Sc j a ha m₀ γ₀).obj N))) (D.dn i j) +
          ((parameterTwist D Sc).t j i : k) • endoPower (Y := (heightContentCast D Sc a ha p₂ q₂).obj
                ((heightContentInduction D Sc i a ha m₁ γ₁).obj
                  ((heightContentCast D Sc a ha p₁ q₁).obj
                    ((heightContentInduction D Sc j a ha m₀ γ₀).obj N))))
            (((heightContentCast D Sc a ha p₂ q₂).map
              ((heightContentInduction D Sc i a ha m₁ γ₁).map
                ((heightContentCastTrans D Sc a ha p₁ q₁
                  (heightContentDot D Sc j a ha m₀ γ₀)).app (D.parity j) N)))) (D.dn j i) +
          ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
            (parameterTwist D Sc).s i j p q •
              (endoPower (Y := (heightContentCast D Sc a ha p₂ q₂).obj
                ((heightContentInduction D Sc i a ha m₁ γ₁).obj
                  ((heightContentCast D Sc a ha p₁ q₁).obj
                    ((heightContentInduction D Sc j a ha m₀ γ₀).obj N)))) (((heightContentCast D Sc a ha p₂ q₂).map
                ((heightContentInduction D Sc i a ha m₁ γ₁).map
                  ((heightContentCastTrans D Sc a ha p₁ q₁
                    (heightContentDot D Sc j a ha m₀ γ₀)).app (D.parity j) N)))) q ≫
              endoPower (Y := (heightContentCast D Sc a ha p₂ q₂).obj
                ((heightContentInduction D Sc i a ha m₁ γ₁).obj
                  ((heightContentCast D Sc a ha p₁ q₁).obj
                    ((heightContentInduction D Sc j a ha m₀ γ₀).obj N)))) ((heightContentCastTrans D Sc a ha p₂ q₂
                (heightContentDot D Sc i a ha m₁ γ₁)).app (D.parity i)
                ((heightContentCast D Sc a ha p₁ q₁).obj
                  ((heightContentInduction D Sc j a ha m₀ γ₀).obj N))) p)) ≫
        eqToHom b.symm := by
  intro a₁ a₂ a₃ b
  subst p₁ q₁ p₂ q₂
  obtain rfl : hc = rfl := rfl
  obtain rfl : pX = rfl := rfl
  subst b
  rw [heightContentCastTrans_app_eq_map, heightContentCastTrans_app_eq_map]
  apply (fullHomEquiv (k := k) _ _ _).injective
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, map_add, map_smul, map_sum]
  simp only [fullHomEquiv_apply, ObjectProperty.FullSubcategory.comp_hom,
    endoPower_fullSubcategory_hom, heightContentCast_map_hom, heightContentInductionDot_app_hom,
    heightContentInduction_map_hom', eqToHom_refl, Category.id_comp, Category.comp_id]
  simp only [heightBlockCross_app]
  exact heightInduction_square_ne D Sc hij a ha m₀ N.obj hd

/-- **The distinct-colour quadratic relation on content blocks**, `d_{ij} = 0`. -/
theorem heightContentMixedSquareZero (hd : D.d i j = 0) (m₀ : ℕ) (γ₀ : Multiset I)
    (N : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₀ γ₀))
    {m₂ : ℕ} {γ₂ : Multiset I}
    (hc : {i} + ({j} + γ₀) = γ₂) (hc' : {j} + ({i} + γ₀) = γ₂) (pX : m₀ + 1 + 1 = m₂)
    (O : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m₂ γ₂)) :
    ∀ (a₁ : O = _) (a₂ : _ = _) (a₃ : _ = O),
    eqToHom a₁ ≫ (heightContentCast D Sc a ha pX rfl).map
          ((heightBlockCross D Sc a ha i j m₀ γ₀ γ₂ hc).app (D.parity i * D.parity j) N) ≫
        eqToHom a₂ ≫ (heightContentCast D Sc a ha pX rfl).map
          ((heightBlockCross D Sc a ha j i m₀ γ₀ γ₂ hc').app (D.parity j * D.parity i) N) ≫
        eqToHom a₃ =
      ((parameterTwist D Sc).t i j : k) • 𝟙 O := by
  intro a₁ a₂ a₃
  subst hc pX a₁
  apply (fullHomEquiv (k := k) _ _ _).injective
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, map_smul]
  simp only [fullHomEquiv_apply, ObjectProperty.FullSubcategory.comp_hom,
    heightContentCast_map_hom, eqToHom_refl, Category.id_comp, Category.comp_id,
    ObjectProperty.FullSubcategory.id_hom]
  simp only [heightBlockCross_app]
  exact heightInduction_square_zero D Sc hij a ha m₀ N.obj hd

end Content

omit [Fintype I] in
/-- A nonzero parameter `s^{pq}_{ij}` forces `p |i| = q |j| = 0`. -/
theorem scalars_parity_of_s_ne_zero (S : SKM.Scalars D k) {i j : I} {p q : ℕ}
    (hs : S.s i j p q ≠ 0) : (p : ZMod 2) * D.parity i = 0 ∧ (q : ZMod 2) * D.parity j = 0 := by
  constructor
  · rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) ((p : ZMod 2) * D.parity i) with h | h
    · exact h
    · exact absurd (S.s_eq_zero i j p q h) hs
  · rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) ((q : ZMod 2) * D.parity j) with h | h
    · exact h
    · exact absurd ((S.s_symm i j p q).trans (S.s_eq_zero j i q p h)) hs

omit [Fintype I] in
theorem parity_mul_add_parity_mul (u w : ZMod 2) : u * w + w * u = 0 := by
  rw [mul_comm w, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

/-! ### Weight level -/

section Weight
variable {i j : I} (hij : i ≠ j) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃) (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)
include hij

attribute [local irreducible] ContentSupported SuperBimodule.tensor

omit hij in
/-- The composite induction at the successor block `β ↦ β + j + i`. -/
theorem globalActionE_comp_obj_blockSucc₂ (M : WeightProduct D Sc a ha Λ x₀)
    (β : WeightBlocks D Λ x₀) :
    Superfunctor.obj (globalActionE D Sc a ha i Λ h₂)
        (Superfunctor.obj (globalActionE D Sc a ha j Λ h₁) M) (blockSucc₂ D i j Λ h₁ h₂ β) =
      (blockInd D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)).obj
        ((blockInd D Sc a ha j Λ h₁ β).obj (M β)) :=
  (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)
    ((globalEFunctor D Sc a ha j Λ h₁).obj M)).trans
    (congrArg (blockInd D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)).obj
      (inductionComponent_obj_blockSucc D Sc a ha j Λ h₁ β M))

omit hij in
/-- The outer dot on the successor block `β ↦ β + j + i`, conjugated by the transport
`globalActionE_comp_obj_blockSucc₂`. -/
theorem globalActionDot_outer_component (M : WeightProduct D Sc a ha Λ x₀)
    (β : WeightBlocks D Λ x₀) :
    (globalActionDot D Sc a ha i Λ h₂).app (D.parity i)
        (Superfunctor.obj (globalActionE D Sc a ha j Λ h₁) M) (blockSucc₂ D i j Λ h₁ h₂ β) =
      eqToHom (globalActionE_comp_obj_blockSucc₂ D Sc a ha Λ h₁ h₂ M β) ≫
        (blockDot D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)).app (D.parity i)
          ((blockInd D Sc a ha j Λ h₁ β).obj (M β)) ≫
        eqToHom (globalActionE_comp_obj_blockSucc₂ D Sc a ha Λ h₁ h₂ M β).symm := by
  refine (globalWeightDotComponent_blockSucc D Sc a ha i Λ h₂ _ _ (blockSucc D Λ j h₁ β)).trans ?_
  rw [superNatTrans_app_of_eq (blockDot D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)) _
    (show Superfunctor.obj (globalActionE D Sc a ha j Λ h₁) M (blockSucc D Λ j h₁ β) =
      (blockInd D Sc a ha j Λ h₁ β).obj (M β) from
      inductionComponent_obj_blockSucc D Sc a ha j Λ h₁ β M)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

omit hij in
/-- The inner dot on the successor block `β ↦ β + j + i`, with the same transport. -/
theorem globalActionDot_inner_component (M : WeightProduct D Sc a ha Λ x₀)
    (β : WeightBlocks D Λ x₀) :
    Superfunctor.map (globalActionE D Sc a ha i Λ h₂)
        ((globalActionDot D Sc a ha j Λ h₁).app (D.parity j) M) (blockSucc₂ D i j Λ h₁ h₂ β) =
      eqToHom (globalActionE_comp_obj_blockSucc₂ D Sc a ha Λ h₁ h₂ M β) ≫
        (blockInd D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)).map
          ((blockDot D Sc a ha j Λ h₁ β).app (D.parity j) (M β)) ≫
        eqToHom (globalActionE_comp_obj_blockSucc₂ D Sc a ha Λ h₁ h₂ M β).symm := by
  refine (inductionComponent_map_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β) _).trans ?_
  have hD₁ : (globalActionDot D Sc a ha j Λ h₁).app (D.parity j) M (blockSucc D Λ j h₁ β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha j Λ h₁ β M) ≫
        (blockDot D Sc a ha j Λ h₁ β).app (D.parity j) (M β) ≫
          eqToHom (inductionComponent_obj_blockSucc D Sc a ha j Λ h₁ β M).symm :=
    globalWeightDotComponent_blockSucc D Sc a ha j Λ h₁ _ M β
  rw [hD₁]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- **The distinct-colour quadratic relation (1.7) on the global factors**, `d_{ij} ≠ 0`, with
the parameters of `parameterTwist`. -/
theorem globalActionCross_square_ne (hd : D.d i j ≠ 0) :
    globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄ ≫
        globalActionCross D Sc a ha j i Λ h₃ h₄ h₁ h₂ =
      ((parameterTwist D Sc).t i j : k) • (globalActionE D Sc a ha j Λ h₁ ◁
          SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) (D.dn i j)) +
      ((parameterTwist D Sc).t j i : k) • (SKM.rouquierPower
          (globalActionDot D Sc a ha j Λ h₁) (D.dn j i) ▷ globalActionE D Sc a ha i Λ h₂) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        (parameterTwist D Sc).s i j p q •
          (SKM.rouquierPower (globalActionDot D Sc a ha j Λ h₁) q ▷
              globalActionE D Sc a ha i Λ h₂ ≫
            globalActionE D Sc a ha j Λ h₁ ◁
              SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) p) := by
  have mo := globalActionDot_mem D Sc a ha i Λ h₂
  have mi := globalActionDot_mem D Sc a ha j Λ h₁
  have po := dn_cast_mul_parity D hij
  have pin := dn_cast_mul_parity D hij.symm
  have m₁ := comp_mem (globalActionCross_mem D Sc a ha i j Λ h₁ h₂ h₃ h₄)
    (globalActionCross_mem D Sc a ha j i Λ h₃ h₄ h₁ h₂)
  rw [parity_mul_add_parity_mul] at m₁
  have hterm : ∀ p q, (parameterTwist D Sc).s i j p q ≠ 0 →
      (SKM.rouquierPower (globalActionDot D Sc a ha j Λ h₁) q ▷
          globalActionE D Sc a ha i Λ h₂ ≫
        globalActionE D Sc a ha j Λ h₁ ◁
          SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) p) ∈
        parity (R := k) _ _ 0 ∧
      ∀ M, (SKM.rouquierPower (globalActionDot D Sc a ha j Λ h₁) q ▷
          globalActionE D Sc a ha i Λ h₂ ≫
        globalActionE D Sc a ha j Λ h₁ ◁
          SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) p).app 0 M =
        Superfunctor.map (globalActionE D Sc a ha i Λ h₂)
            (endoPower ((globalActionDot D Sc a ha j Λ h₁).app (D.parity j) M) q) ≫
          endoPower ((globalActionDot D Sc a ha i Λ h₂).app (D.parity i)
            (Superfunctor.obj (globalActionE D Sc a ha j Λ h₁) M)) p := by
    intro p q hs
    obtain ⟨hp, hq⟩ := scalars_parity_of_s_ne_zero D (parameterTwist D Sc) hs
    have r₁ := TwoSupercategory.whiskerRight_mem (R := k) (globalActionE D Sc a ha i Λ h₂)
      (scat_rouquierPower_mem' mi q hq)
    have r₂ := TwoSupercategory.whiskerLeft_mem (R := k) (globalActionE D Sc a ha j Λ h₁)
      (scat_rouquierPower_mem' mo p hp)
    refine ⟨by simpa using comp_mem r₁ r₂, fun M => ?_⟩
    rw [scat_comp_app_of_mem' r₁ r₂ (add_zero 0) M, SCat.whiskerRight_app, SCat.whiskerLeft_app,
      scat_rouquierPower_app' mi q hq, scat_rouquierPower_app' mo p hp]
  have m₂ : ((parameterTwist D Sc).t i j : k) • (globalActionE D Sc a ha j Λ h₁ ◁
          SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) (D.dn i j)) +
      ((parameterTwist D Sc).t j i : k) • (SKM.rouquierPower
          (globalActionDot D Sc a ha j Λ h₁) (D.dn j i) ▷ globalActionE D Sc a ha i Λ h₂) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        (parameterTwist D Sc).s i j p q •
          (SKM.rouquierPower (globalActionDot D Sc a ha j Λ h₁) q ▷
              globalActionE D Sc a ha i Λ h₂ ≫
            globalActionE D Sc a ha j Λ h₁ ◁
              SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) p) ∈
        parity (R := k) _ _ 0 := by
    refine add_mem (add_mem (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_))
      (Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_)
    · exact TwoSupercategory.whiskerLeft_mem (R := k) _ (scat_rouquierPower_mem' mo _ po)
    · exact TwoSupercategory.whiskerRight_mem (R := k) _ (scat_rouquierPower_mem' mi _ pin)
    · by_cases hs : (parameterTwist D Sc).s i j p q = 0
      · rw [hs, zero_smul]
        exact zero_mem _
      · exact Submodule.smul_mem _ _ (hterm p q hs).1
  refine scat_eq_of_even m₁ m₂ fun M => ?_
  rw [scat_comp_app_of_mem' (globalActionCross_mem D Sc a ha i j Λ h₁ h₂ h₃ h₄)
    (globalActionCross_mem D Sc a ha j i Λ h₃ h₄ h₁ h₂) (parity_mul_add_parity_mul _ _) M]
  simp only [SCat.add_app, SCat.smul_app, scat_sum_app]
  rw [SCat.whiskerLeft_app, scat_rouquierPower_app' mo _ po, SCat.whiskerRight_app,
    scat_rouquierPower_app' mi _ pin, endoPower_scat_map]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    (show (parameterTwist D Sc).s i j p q •
        (SKM.rouquierPower (globalActionDot D Sc a ha j Λ h₁) q ▷
            globalActionE D Sc a ha i Λ h₂ ≫
          globalActionE D Sc a ha j Λ h₁ ◁
            SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) p).app 0 M =
      (parameterTwist D Sc).s i j p q •
        (endoPower (Superfunctor.map (globalActionE D Sc a ha i Λ h₂)
            ((globalActionDot D Sc a ha j Λ h₁).app (D.parity j) M)) q ≫
          endoPower ((globalActionDot D Sc a ha i Λ h₂).app (D.parity i)
            (Superfunctor.obj (globalActionE D Sc a ha j Λ h₁) M)) p) by
      exact smul_congr_of_ne _ fun hs => by rw [(hterm p q hs).2 M, endoPower_scat_map])]
  funext ζ
  simp only [pi_comp_apply', pi_add_apply', pi_smul_apply', pi_sum_apply', endoPower_pi_apply]
  by_cases hζ : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ζ
  · obtain ⟨β, rfl⟩ := hζ
    have e₂ := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ (rfl : blockSucc₂ D i j Λ h₁ h₂ β = _)
    have hX : (globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M (blockSucc₂ D i j Λ h₁ h₂ β) =
        globalWeightCrossVia D Sc a ha i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j) M β
          (blockSucc₂ D i j Λ h₁ h₂ β) rfl :=
      globalWeightCrossComponent_of D Sc a ha i j Λ h₁ h₂ h₃ h₄ _ M β _ rfl
    have hX' : (globalActionCross D Sc a ha j i Λ h₃ h₄ h₁ h₂).app
        (D.parity j * D.parity i) M (blockSucc₂ D i j Λ h₁ h₂ β) =
        globalWeightCrossVia D Sc a ha j i Λ h₃ h₄ h₁ h₂ (D.parity j * D.parity i) M β
          (blockSucc₂ D i j Λ h₁ h₂ β) e₂ :=
      globalWeightCrossComponent_of D Sc a ha j i Λ h₃ h₄ h₁ h₂ _ M β _ e₂
    rw [hX, hX', globalActionDot_outer_component D Sc a ha Λ h₁ h₂ M β,
      globalActionDot_inner_component D Sc a ha Λ h₁ h₂ M β]
    simp only [endoPower_eqToHom_conj, eqToHom_conj_comp, eqToHom_conj_smul, eqToHom_conj_sum,
      eqToHom_conj_add]
    unfold globalWeightCrossVia
    simp only [Category.assoc, eqToHom_trans_assoc]
    exact heightContentMixedSquareNe D Sc a ha hij hd β.1.card β.1 (M β)
      (m₁ := (blockSucc D Λ j h₁ β).1.card) (γ₁ := (blockSucc D Λ j h₁ β).1)
      (m₂ := (blockSucc₂ D i j Λ h₁ h₂ β).1.card) (γ₂ := (blockSucc₂ D i j Λ h₁ h₂ β).1)
      _ _ _ _ _ _ _ _ _ _ _ _
  · exact (globalEFunctor_comp_isZero D Sc a ha i j Λ h₁ h₂ ζ
      (fun ⟨β, hβ⟩ => hζ ⟨β, hβ⟩) M).eq_of_src _ _

/-- **The distinct-colour quadratic relation (1.7) on the global factors**, `d_{ij} = 0`. -/
theorem globalActionCross_square_zero (hd : D.d i j = 0) :
    globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄ ≫
        globalActionCross D Sc a ha j i Λ h₃ h₄ h₁ h₂ =
      ((parameterTwist D Sc).t i j : k) • 𝟙 _ := by
  have m₁ := comp_mem (globalActionCross_mem D Sc a ha i j Λ h₁ h₂ h₃ h₄)
    (globalActionCross_mem D Sc a ha j i Λ h₃ h₄ h₁ h₂)
  rw [parity_mul_add_parity_mul] at m₁
  refine scat_eq_of_even m₁ (Submodule.smul_mem _ _ (id_mem (R := k) _)) fun M => ?_
  rw [scat_comp_app_of_mem' (globalActionCross_mem D Sc a ha i j Λ h₁ h₂ h₃ h₄)
    (globalActionCross_mem D Sc a ha j i Λ h₃ h₄ h₁ h₂) (parity_mul_add_parity_mul _ _) M,
    SCat.smul_app, SCat.id_app_zero]
  funext ζ
  rw [pi_comp_apply', pi_smul_apply']
  by_cases hζ : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ζ
  · obtain ⟨β, rfl⟩ := hζ
    have e₂ := blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ (rfl : blockSucc₂ D i j Λ h₁ h₂ β = _)
    have hX : (globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M (blockSucc₂ D i j Λ h₁ h₂ β) =
        globalWeightCrossVia D Sc a ha i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j) M β
          (blockSucc₂ D i j Λ h₁ h₂ β) rfl :=
      globalWeightCrossComponent_of D Sc a ha i j Λ h₁ h₂ h₃ h₄ _ M β _ rfl
    have hX' : (globalActionCross D Sc a ha j i Λ h₃ h₄ h₁ h₂).app
        (D.parity j * D.parity i) M (blockSucc₂ D i j Λ h₁ h₂ β) =
        globalWeightCrossVia D Sc a ha j i Λ h₃ h₄ h₁ h₂ (D.parity j * D.parity i) M β
          (blockSucc₂ D i j Λ h₁ h₂ β) e₂ :=
      globalWeightCrossComponent_of D Sc a ha j i Λ h₃ h₄ h₁ h₂ _ M β _ e₂
    rw [hX, hX']
    unfold globalWeightCrossVia
    simp only [Category.assoc, eqToHom_trans_assoc]
    exact heightContentMixedSquareZero D Sc a ha hij hd β.1.card β.1 (M β)
      (m₂ := (blockSucc₂ D i j Λ h₁ h₂ β).1.card) (γ₂ := (blockSucc₂ D i j Λ h₁ h₂ β).1)
      _ _ _ _ _ _ _
  · exact (globalEFunctor_comp_isZero D Sc a ha i j Λ h₁ h₂ ζ
      (fun ⟨β, hβ⟩ => hζ ⟨β, hβ⟩) M).eq_of_src _ _

variable [DecidableEq I]

/-- The `quadNe` field of `RouquierMulticolour` for the signed global crossing, with the
scalars `parameterTwist D Sc`. -/
theorem globalActionSignedCross_square_ne (hd : D.d i j ≠ 0) :
    globalActionSignedCross D Sc a ha Λ i j h₁ h₂ h₃ h₄ ≫
        globalActionSignedCross D Sc a ha Λ j i h₃ h₄ h₁ h₂ =
      ((parameterTwist D Sc).t i j : k) • (globalActionE D Sc a ha j Λ h₁ ◁
          SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) (D.dn i j)) +
      ((parameterTwist D Sc).t j i : k) • (SKM.rouquierPower
          (globalActionDot D Sc a ha j Λ h₁) (D.dn j i) ▷ globalActionE D Sc a ha i Λ h₂) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        (parameterTwist D Sc).s i j p q •
          (SKM.rouquierPower (globalActionDot D Sc a ha j Λ h₁) q ▷
              globalActionE D Sc a ha i Λ h₂ ≫
            globalActionE D Sc a ha j Λ h₁ ◁
              SKM.rouquierPower (globalActionDot D Sc a ha i Λ h₂) p) := by
  simp only [globalActionSignedCross, hij, hij.symm, ↓reduceIte]
  exact globalActionCross_square_ne D Sc a ha hij Λ h₁ h₂ h₃ h₄ hd

/-- The `quadZero` field of `RouquierMulticolour` for the signed global crossing, with the
scalars `parameterTwist D Sc`. -/
theorem globalActionSignedCross_square_zero (hd : D.d i j = 0) :
    globalActionSignedCross D Sc a ha Λ i j h₁ h₂ h₃ h₄ ≫
        globalActionSignedCross D Sc a ha Λ j i h₃ h₄ h₁ h₂ =
      ((parameterTwist D Sc).t i j : k) • 𝟙 _ := by
  simp only [globalActionSignedCross, hij, hij.symm, ↓reduceIte]
  exact globalActionCross_square_zero D Sc a ha hij Λ h₁ h₂ h₃ h₄ hd

end Weight

end OddMath.QuiverHecke.CyclotomicAction
