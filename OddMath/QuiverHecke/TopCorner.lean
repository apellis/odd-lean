/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.HeckeCorner
import OddMath.QuiverHecke.UpDown
import OddMath.QuiverHecke.WidthZero

/-!
# The local corner of `α(z) α′(z′)` on `E_𝐢 F_𝐢′ 1_λ`

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. For primitive idempotents `z` of `E_s` and `z′` of `E_t` in `H`, the endomorphisms of
`E_s F_t 1_λ` of the form `α′(y) α(x) β`, with `x ∈ z H z`, `y ∈ z′ H z′` and `β` an endomorphism
of `1_λ` in the rightmost region, form a local corner graded by degree and parity. Its
identity is `α′(z′) α(z)`.

* `bubPiece μ γ`: the homogeneous endomorphisms of `1_μ`. They form a local corner with radical
  zero, since `End(1_μ)` vanishes in negative degree and is `k` in degree zero (Theorem 8.1).
* `upMap`, `dnMap`, `bubMap`: the maps of the corners under the upward placement, the downward
  placement and the placement of bubbles in the rightmost region; `topFam` is the family of
  products of their images.
* `localCorner_topFam`: the products form a local corner (`LocalCorner.mul`, twice).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation GradedWalk
open QuiverHecke (upWord hObj homPiece heCorner)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [Field k]
  {Sc : Scalars D k} (cs : CScalars Sc) (sy : Symmetrizer D) (hc : Sc.Homogeneous)

/-! ## Bubbles in the rightmost region -/

/-- The endomorphisms of `1_μ` of degree `γ.1` and parity `γ.2`. -/
def bubPiece (μ : X) (γ : Deg) : Submodule k (End ((pres D Sc).obj (ob D μ []))) :=
  (pres D Sc).homDeg (gdeg D sy) (ob D μ []) (ob D μ []) γ.1 ⊓ homPar D Sc μ [] [] γ.2

include cs sy in
theorem homPar_disjoint (μ : X) (a b : List (Letter I)) {p q : ZMod 2} (h : p ≠ q)
    {f : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)}
    (hp : f ∈ homPar D Sc μ a b p) (hq : f ∈ homPar D Sc μ a b q) : f = 0 := by
  rw [homPar_eq_homDeg sy cs] at hp hq
  exact Submodule.disjoint_def.1
    ((DirectSum.IsInternal.submodule_iSupIndep (Supercategory.isInternal
      (R := k) (C := (pres D Sc).Presented) _ _)).pairwiseDisjoint h) f hp hq

include cs hc in
theorem bubPiece_eq_bot (μ : X) {γ : Deg} (hγ : γ.1 < 0) : bubPiece (Sc := Sc) sy μ γ = ⊥ := by
  rw [bubPiece, homDeg_endOne_eq_bot cs sy hc μ hγ, bot_inf_eq]

include cs hc in
theorem bubPiece_zero_one (μ : X) : bubPiece (Sc := Sc) sy μ ((0, 1) : Deg) = ⊥ := by
  refine eq_bot_iff.2 fun f hf => ?_
  obtain ⟨c, rfl⟩ := homDeg_endOne_zero cs sy hc μ hf.1
  have h0 : c • 𝟙 ((pres D Sc).obj (ob D μ [])) ∈ homPar D Sc μ [] [] 0 :=
    Submodule.smul_mem _ c (by rw [← cl_nil]; exact cl_mem_homPar' μ [] [] [])
  rw [Submodule.mem_bot]
  exact homPar_disjoint cs sy μ [] [] (by decide) h0 hf.2

include cs hc in
/-- **The bubbles form a local corner** with radical zero. -/
theorem localCorner_bubPiece (μ : X) :
    LocalCorner (bubPiece (Sc := Sc) sy μ) 1 ⊥ 1 0 where
  mul_le γ δ := by
    refine Submodule.mul_le.2 fun x hx y hy => ⟨?_, ?_⟩
    · have := Presentation.comp_mem_homDeg hy.1 hx.1
      rwa [add_comm] at this
    · have := comp_mem_homPar hy.2 hx.2
      rwa [Prod.snd_add, add_comm]
  unit_mem := ⟨Presentation.id_mem_homDeg (pres D Sc) (gdeg D sy) _, by
    change 𝟙 _ ∈ _; rw [← cl_nil]; exact cl_mem_homPar' μ [] [] []⟩
  unit_mul _ x _ := one_mul x
  mul_unit _ x _ := mul_one x
  rad_le := bot_le
  mul_rad := by rw [Submodule.mul_bot]
  rad_mul := by rw [Submodule.bot_mul]
  rad_pow := pow_one _
  residue x hx := by
    obtain ⟨c, hc'⟩ := homDeg_endOne_zero cs sy hc μ hx.1
    exact ⟨c, by rw [Submodule.mem_bot, sub_eq_zero]; exact hc'⟩
  pair_le γ hγ := by
    rcases lt_trichotomy γ.1 0 with h | h | h
    · rw [bubPiece_eq_bot cs sy hc μ h, Submodule.bot_mul]
    · have h2 : γ.2 = 1 := by
        rcases (show ∀ q : ZMod 2, q = 0 ∨ q = 1 by decide) γ.2 with h' | h'
        · exact absurd (Prod.ext h h') hγ
        · exact h'
      have : γ = ((0, 1) : Deg) := Prod.ext h h2
      rw [this, bubPiece_zero_one cs sy hc μ, Submodule.bot_mul]
    · rw [bubPiece_eq_bot cs sy hc μ (γ := -γ) (by simpa using h), Submodule.mul_bot]
  eq_bot γ hγ := bubPiece_eq_bot cs sy hc μ (by simpa using hγ)

/-! ## The three families on `E_s F_t 1_{-ν}` -/

theorem ksign_comm (p q : ZMod 2) : ksign p q = ksign q p := by
  fin_cases p <;> fin_cases q <;> decide

theorem ksign_mul_self (p q : ZMod 2) : ksign p q * ksign p q = 1 := by
  fin_cases p <;> fin_cases q <;> decide

/-- The identification of the endomorphisms of `E_s` in the graded copy of `H`. -/
def castE (s : List I) : End (hObj D Sc sy hc s) →ₗ[k] End (hO Sc s) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The upward placement on `E_s F_t 1_{-ν}`. -/
def upMap (ν : X) (s t : List I) :
    End (hObj D Sc sy hc s) →ₗ[k] End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t))) :=
  (upE Sc (-ν) s (dnWord t)).comp (castE sy hc s)

/-- The downward placement on `E_s F_t 1_{-ν}`. -/
def dnMap (ν : X) (s t : List I) :
    End (hObj D Sc sy hc t) →ₗ[k] End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t))) :=
  (dnE Sc ν (upWord s) t).comp (castE sy hc t)

/-- Bubbles in the rightmost region of `E_s F_t 1_{-ν}`. -/
def bubMap (ν : X) (s t : List I) :
    End ((pres D Sc).obj (ob D (-ν) [])) →ₗ[k]
      End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t))) where
  toFun β := bubAt D Sc (-ν) (upWord s ++ dnWord t) β
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _

/-- The products `α′(y) α(x) β` of the top step. -/
def topFam (ν : X) (s t : List I) (z : End (hObj D Sc sy hc s))
    (z' : End (hObj D Sc sy hc t)) (γ : Deg) :
    Submodule k (End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t)))) :=
  prodFam (prodFam (mapFam (dnMap sy hc ν s t) (heCorner z'))
    (mapFam (upMap sy hc ν s t) (heCorner z))) (mapFam (bubMap ν s t) (bubPiece sy (-ν))) γ

variable {sy hc}

theorem upMap_mul (ν : X) (s t : List I) (x y : End (hObj D Sc sy hc s)) :
    upMap sy hc ν s t x * upMap sy hc ν s t y = upMap sy hc ν s t (x * y) :=
  (upE_mul Sc (-ν) s (dnWord t) x y).symm

theorem dnMap_mul (ν : X) (s t : List I) {γ δ : Deg} {z' x y : End (hObj D Sc sy hc t)}
    (hx : x ∈ heCorner z' γ) (hy : y ∈ heCorner z' δ) :
    dnMap sy hc ν s t x * dnMap sy hc ν s t y = ksign γ.2 δ.2 • dnMap sy hc ν s t (y * x) :=
  dnE_mul Sc ν (upWord s) t hx.1.2 hy.1.2

theorem bubMap_mul (ν : X) (s t : List I) (x y : End ((pres D Sc).obj (ob D (-ν) []))) :
    bubMap ν s t x * bubMap ν s t y = bubMap ν s t (x * y) :=
  (bubAt_comp (-ν) (upWord s ++ dnWord t) y x).symm

include cs in
theorem superComm_dn_up (ν : X) (s t : List I) (z : End (hObj D Sc sy hc s))
    (z' : End (hObj D Sc sy hc t)) :
    SuperComm (mapFam (dnMap sy hc ν s t) (heCorner z'))
      (mapFam (upMap sy hc ν s t) (heCorner z)) := by
  refine SuperComm.map _ _ fun {γ δ y x} hy hx => ?_
  have h := upE_comp_dnE Sc sy cs ν s t hx.1.2 hy.1.2
  change dnMap sy hc ν s t y ≫ upMap sy hc ν s t x =
    ksign γ.2 δ.2 • (upMap sy hc ν s t x ≫ dnMap sy hc ν s t y)
  change upMap sy hc ν s t x ≫ dnMap sy hc ν s t y =
    ksign δ.2 γ.2 • (dnMap sy hc ν s t y ≫ upMap sy hc ν s t x) at h
  rw [h, smul_smul, ksign_comm δ.2, ksign_mul_self, one_smul]

theorem superComm_bub {ν : X} {s t : List I} {R' : Type*} [Ring R'] [Algebra k R']
    {E : Deg → Submodule k R'}
    (Φ : R' →ₗ[k] End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t))))
    (hΦ : ∀ {γ : Deg} {x : R'}, x ∈ E γ →
      Φ x ∈ homPar D Sc (-ν) (upWord s ++ dnWord t) (upWord s ++ dnWord t) γ.2) :
    SuperComm (mapFam Φ E) (mapFam (bubMap ν s t) (bubPiece sy (-ν))) := by
  refine SuperComm.map _ _ fun {γ δ x β} hx hβ => ?_
  change Φ x ≫ bubAt D Sc (-ν) _ β = ksign γ.2 δ.2 • (bubAt D Sc (-ν) _ β ≫ Φ x)
  rw [comp_bubAt (hΦ hx) hβ.2, zsign_mul_smul]

include cs in
/-- **The products `α′(y) α(x) β` form a local corner**, with identity `α′(z′) α(z)`, given local
corners of `z H z` and `z′ H z′`. -/
theorem localCorner_topFam (ν : X) (s t : List I) {z : End (hObj D Sc sy hc s)}
    {z' : End (hObj D Sc sy hc t)} {NE NE' : Submodule k _} {a a' lo lo' : ℕ}
    (hE : LocalCorner (heCorner z) z NE a lo) (hE' : LocalCorner (heCorner z') z' NE' a' lo') :
    ∃ (N : Submodule k _) (b lo'' : ℕ), LocalCorner (topFam sy hc ν s t z z')
      (dnMap sy hc ν s t z' * upMap sy hc ν s t z * bubMap ν s t 1) N b lo'' := by
  have h1 := (hE'.mapAnti (dnMap sy hc ν s t) fun hx hy => dnMap_mul ν s t hx hy).mul
    (hE.map (upMap sy hc ν s t) fun _ _ => upMap_mul ν s t _ _) (superComm_dn_up cs ν s t z z')
  have h2 := h1.mul ((localCorner_bubPiece cs sy hc (-ν)).map (bubMap ν s t)
      fun _ _ => bubMap_mul ν s t _ _)
    (SuperComm.prodFam (superComm_bub (E := heCorner z') (dnMap sy hc ν s t)
        fun hx => dnE_mem_homPar Sc sy cs ν (upWord s) t hx.1.2)
      (superComm_bub (E := heCorner z) (upMap sy hc ν s t)
        fun hx => upE_mem_homPar Sc sy cs (-ν) s (dnWord t) hx.1.2))
  exact ⟨_, _, _, h2⟩

end OddMath.SKM
