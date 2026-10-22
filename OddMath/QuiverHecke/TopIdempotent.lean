/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.TopCorner
import OddMath.QuiverHecke.TopLocal

/-!
# The top idempotent is local modulo shorter words

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. Let `z`, `z′` be even degree-zero idempotents of `E_s`, `E_t` in `H` whose corners are
local, and `ε = α′(z′) α(z)` on `E_s F_t 1_λ`. Every endomorphism `f` of `E_s F_t 1_λ` of degree
zero and parity zero with `ε f ε = f` is nilpotent modulo the maps through shorter words, or
invertible in `ε End ε` modulo them (`top_localMod`).

The proof: by the U-turn spanning (`udSpan_sup_shortSpan`), `f` is a combination of products
`α′(y) α(x) β` modulo shorter words; projecting to degree zero keeps the products of total
degree zero and the maps through shorter words (`proj0_mem_span_shortHom`); conjugating by `ε`
moves such a product into the local corner `topFam 0` (`eps_mul_gen_mul_eps`), and
`LocalCorner.nilpotent_or_inverse_mod` applies.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation GradedWalk
open QuiverHecke (upWord hObj homPiece heCorner upLayers)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [Field k]
  {Sc : Scalars D k} (cs : CScalars Sc) {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-! ## Rearranging products -/

theorem mul_rearrange {R : Type*} [Ring R] {A B Y Z C : R} (h₁ : B * Y = Y * B)
    (h₂ : Z * A = A * Z) (h₃ : B * A = A * B) (h₄ : C * A = A * C) (h₅ : C * B = B * C) :
    A * B * (Y * Z * C) * (A * B) = A * Y * A * (B * Z * B) * C :=
  calc A * B * (Y * Z * C) * (A * B) = A * (B * Y) * Z * (C * A) * B := by noncomm_ring
    _ = A * (Y * B) * Z * (A * C) * B := by rw [h₁, h₄]
    _ = A * Y * B * (Z * A) * (C * B) := by noncomm_ring
    _ = A * Y * B * (A * Z) * (B * C) := by rw [h₂, h₅]
    _ = A * Y * (B * A) * Z * B * C := by noncomm_ring
    _ = A * Y * (A * B) * Z * B * C := by rw [h₃]
    _ = A * Y * A * (B * Z * B) * C := by noncomm_ring

theorem up_dn_inj : ∀ (s s' t t' : List I),
    upWord s ++ dnWord t = upWord s' ++ dnWord t' → s = s' ∧ t = t'
  | [], [], t, t', h => by
    refine ⟨rfl, ?_⟩
    simp only [dnWord_eq_map] at h
    exact List.map_injective_iff.2 (fun a b hab => (Prod.mk.inj hab).2) (by simpa using h)
  | [], i :: s', t, t', h => by
    simp only [dnWord_eq_map] at h
    cases t with
    | nil => simp [upWord] at h
    | cons j t => simp [upWord] at h
  | i :: s, [], t, t', h => by
    simp only [dnWord_eq_map] at h
    cases t' with
    | nil => simp [upWord] at h
    | cons j t' => simp [upWord] at h
  | i :: s, j :: s', t, t', h => by
    simp only [upWord, List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨hij, h⟩ := h
    obtain ⟨hs, ht⟩ := up_dn_inj s s' t t' h
    exact ⟨by rw [(Prod.mk.inj hij).2, hs], ht⟩

/-! ## Commuting the three families -/

section Comm

variable (ν : X) (s t : List I)

include cs in
theorem dn_up_comm_of_up {q : ZMod 2} {x : End (hObj D Sc sy hc s)}
    {y : End (hObj D Sc sy hc t)}
    (hx : x ∈ Supercategory.parity (R := k) (hO Sc s) (hO Sc s) 0)
    (hy : y ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) q) :
    dnMap sy hc ν s t y * upMap sy hc ν s t x = upMap sy hc ν s t x * dnMap sy hc ν s t y := by
  have h := upE_comp_dnE Sc sy cs ν s t hx hy
  rw [ksign_zero_left, one_smul] at h
  exact h

include cs in
theorem dn_up_comm_of_dn {p : ZMod 2} {x : End (hObj D Sc sy hc s)}
    {y : End (hObj D Sc sy hc t)}
    (hx : x ∈ Supercategory.parity (R := k) (hO Sc s) (hO Sc s) p)
    (hy : y ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) 0) :
    dnMap sy hc ν s t y * upMap sy hc ν s t x = upMap sy hc ν s t x * dnMap sy hc ν s t y := by
  have h := upE_comp_dnE Sc sy cs ν s t hx hy
  rw [ksign_zero_right, one_smul] at h
  exact h

theorem bub_comm_of_even {γ : Deg} {β : End ((pres D Sc).obj (ob D (-ν) []))}
    (hβ : β ∈ bubPiece sy (-ν) γ)
    {f : End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t)))}
    (hf : f ∈ homPar D Sc (-ν) (upWord s ++ dnWord t) (upWord s ++ dnWord t) 0) :
    bubMap ν s t β * f = f * bubMap ν s t β := by
  have h := comp_bubAt hf hβ.2
  rw [zsign_mul_smul, ksign_zero_left, one_smul] at h
  exact h

end Comm

/-! ## Conjugating the products by the top idempotent -/

section Conj

variable {ν : X} {s t : List I}

/-- The idempotent `α′(z′) α(z)` of `E_s F_t 1_{-ν}`. -/
abbrev topEps (sy : Symmetrizer D) (hc : Sc.Homogeneous) (ν : X) (s t : List I)
    (z : End (hObj D Sc sy hc s)) (z' : End (hObj D Sc sy hc t)) :
    End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t))) :=
  dnMap sy hc ν s t z' * upMap sy hc ν s t z

theorem homPiece_mul_mem {s : List I} {n m : ℤ} {p q : ZMod 2} {x y : End (hObj D Sc sy hc s)}
    (hx : x ∈ homPiece D Sc sy hc s s n p) (hy : y ∈ homPiece D Sc sy hc s s m q) :
    x * y ∈ homPiece D Sc sy hc s s (n + m) (p + q) := by
  refine ⟨?_, ?_⟩
  · have := GradedSupercategory.comp_mem_degree hy.1 hx.1
    rwa [add_comm] at this
  · have := Supercategory.comp_mem hy.2 hx.2
    rwa [add_comm] at this

theorem sandwich_mem_heCorner {s : List I} {z y : End (hObj D Sc sy hc s)} (hz : z ≫ z = z)
    (hz0 : z ∈ homPiece D Sc sy hc s s 0 0) {n : ℤ} {p : ZMod 2}
    (hy : y ∈ homPiece D Sc sy hc s s n p) : z * y * z ∈ heCorner z ((n, p) : Deg) := by
  refine ⟨?_, ?_⟩
  · have := homPiece_mul_mem (homPiece_mul_mem hz0 hy) hz0
    simpa using this
  · change z ≫ (z ≫ (y ≫ z)) ≫ z = z ≫ (y ≫ z)
    simp only [Category.assoc, hz]
    rw [← Category.assoc z z, hz]

include cs in
/-- **Conjugating a product by the top idempotent** moves its factors into the corners. -/
theorem eps_mul_gen_mul_eps {z : End (hObj D Sc sy hc s)} {z' : End (hObj D Sc sy hc t)}
    (hz0 : z ∈ homPiece D Sc sy hc s s 0 0) (hz0' : z' ∈ homPiece D Sc sy hc t t 0 0)
    {n m : ℤ} {p q : ZMod 2} {γ : Deg} {y : End (hObj D Sc sy hc t)}
    {x : End (hObj D Sc sy hc s)} {β : End ((pres D Sc).obj (ob D (-ν) []))}
    (hy : y ∈ homPiece D Sc sy hc t t n p) (hx : x ∈ homPiece D Sc sy hc s s m q)
    (hβ : β ∈ bubPiece sy (-ν) γ) :
    topEps sy hc ν s t z z' * (dnMap sy hc ν s t y * upMap sy hc ν s t x * bubMap ν s t β) *
        topEps sy hc ν s t z z' =
      dnMap sy hc ν s t (z' * y * z') * upMap sy hc ν s t (z * x * z) * bubMap ν s t β := by
  rw [topEps, mul_rearrange (dn_up_comm_of_up cs ν s t hz0.2 hy.2).symm
    (dn_up_comm_of_dn cs ν s t hx.2 hz0'.2).symm (dn_up_comm_of_up cs ν s t hz0.2 hz0'.2).symm
    (bub_comm_of_even ν s t hβ (dnE_mem_homPar Sc sy cs ν (upWord s) t hz0'.2))
    (bub_comm_of_even ν s t hβ (upE_mem_homPar Sc sy cs (-ν) s (dnWord t) hz0.2))]
  have hyz : y * z' ∈ Supercategory.parity (R := k) (hO Sc t) (hO Sc t) p := by
    have := Supercategory.comp_mem hz0'.2 hy.2
    rwa [zero_add] at this
  have e₁ : dnMap sy hc ν s t z' * dnMap sy hc ν s t y * dnMap sy hc ν s t z' =
      dnMap sy hc ν s t (z' * y * z') := by
    change dnE Sc ν (upWord s) t z' * dnE Sc ν (upWord s) t y * dnE Sc ν (upWord s) t z' =
      dnE Sc ν (upWord s) t (z' * y * z')
    rw [dnE_mul Sc ν (upWord s) t hz0'.2 hy.2, ksign_zero_left, one_smul,
      dnE_mul Sc ν (upWord s) t hyz hz0'.2, ksign_zero_right, one_smul, mul_assoc]
  rw [e₁, upMap_mul, upMap_mul]

/-- The conjugate of a product of total degree zero lies in the local corner `topFam 0`. -/
theorem mem_topFam_zero {z : End (hObj D Sc sy hc s)} {z' : End (hObj D Sc sy hc t)}
    (hz : z ≫ z = z) (hz' : z' ≫ z' = z') (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
    (hz0' : z' ∈ homPiece D Sc sy hc t t 0 0)
    {n m : ℤ} {p q : ZMod 2} {γ : Deg} {y : End (hObj D Sc sy hc t)}
    {x : End (hObj D Sc sy hc s)} {β : End ((pres D Sc).obj (ob D (-ν) []))}
    (hy : y ∈ homPiece D Sc sy hc t t n p) (hx : x ∈ homPiece D Sc sy hc s s m q)
    (hβ : β ∈ bubPiece sy (-ν) γ) (htot : ((n, p) : Deg) + (m, q) + γ = 0) :
    dnMap sy hc ν s t (z' * y * z') * upMap sy hc ν s t (z * x * z) * bubMap ν s t β ∈
      topFam sy hc ν s t z z' 0 := by
  have h₁ : dnMap sy hc ν s t (z' * y * z') * upMap sy hc ν s t (z * x * z) ∈
      prodFam (mapFam (dnMap sy hc ν s t) (heCorner z')) (mapFam (upMap sy hc ν s t) (heCorner z))
        (((n, p) : Deg) + (m, q)) :=
    Submodule.subset_span ⟨(n, p), _, Submodule.mem_map_of_mem
      (sandwich_mem_heCorner hz' hz0' hy), _, by
        rw [add_sub_cancel_left]
        exact Submodule.mem_map_of_mem (sandwich_mem_heCorner hz hz0 hx), rfl⟩
  refine Submodule.subset_span ⟨((n, p) : Deg) + (m, q), _, h₁, _, ?_, rfl⟩
  rw [zero_sub, neg_eq_of_add_eq_zero_right htot]
  exact Submodule.mem_map_of_mem hβ

end Conj

/-! ## Spanning by products of homogeneous factors -/

section Span

variable (sy hc) (ν : X) (s t : List I)

/-- The products `α′(y) α(x) β` with homogeneous factors. -/
def topGen : Set (End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t)))) :=
  {f | ∃ (n m : ℤ) (p q : ZMod 2) (γ : Deg) (y : End (hObj D Sc sy hc t))
    (x : End (hObj D Sc sy hc s)) (β : End ((pres D Sc).obj (ob D (-ν) []))),
    y ∈ homPiece D Sc sy hc t t n p ∧ x ∈ homPiece D Sc sy hc s s m q ∧
    β ∈ bubPiece sy (-ν) γ ∧ f = dnMap sy hc ν s t y * upMap sy hc ν s t x * bubMap ν s t β}

/-- The products `α′(y) α(x) β` with homogeneous factors of total degree zero. -/
def topGenZ : Set (End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t)))) :=
  {f | ∃ (n m : ℤ) (p q : ZMod 2) (γ : Deg) (y : End (hObj D Sc sy hc t))
    (x : End (hObj D Sc sy hc s)) (β : End ((pres D Sc).obj (ob D (-ν) []))),
    y ∈ homPiece D Sc sy hc t t n p ∧ x ∈ homPiece D Sc sy hc s s m q ∧
    β ∈ bubPiece sy (-ν) γ ∧ ((n, p) : Deg) + (m, q) + γ = 0 ∧
    f = dnMap sy hc ν s t y * upMap sy hc ν s t x * bubMap ν s t β}

variable {sy hc ν s t}

theorem hD_mem_homPiece {s s' : List I} {M : List (QuiverHecke.LayerData I)}
    (h : QuiverHecke.SChain s M s') :
    ∃ (n : ℤ) (p : ZMod 2), hD Sc M h ∈ homPiece D Sc sy hc s s' n p :=
  ⟨_, _, (QuiverHecke.pres D Sc).diag_mem_homDeg (deg := QuiverHecke.gdeg D sy) _,
    (QuiverHecke.pres D Sc).diag_mem_homDeg (deg := parityDeg (QuiverHecke.sig D)) _⟩

include cs in
theorem udSpan_le_span_topGen :
    UDSpan Sc cs (-ν) s t (upWord s ++ dnWord t) ≤
      Submodule.span k (topGen (Sc := Sc) sy hc ν s t) := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨s', t', M, N, hM, hN, hw, β, -, rfl⟩
  obtain ⟨rfl, rfl⟩ := up_dn_inj s' s t' t hw
  rw [cl_udLayers Sc ν s' t' hM hN]
  obtain ⟨n, p, hy⟩ := hD_mem_homPiece (Sc := Sc) (sy := sy) (hc := hc) hN
  obtain ⟨m, q, hx⟩ := hD_mem_homPiece (Sc := Sc) (sy := sy) (hc := hc) hM
  have hDU : dnE Sc ν (upWord s') t' (hD Sc N hN) * upE Sc (-ν) s' (dnWord t') (hD Sc M hM) ∈
      homPar D Sc (-ν) (upWord s' ++ dnWord t') (upWord s' ++ dnWord t') (q + p) :=
    comp_mem_homPar (upE_mem_homPar Sc sy cs (-ν) s' (dnWord t') hx.2)
      (dnE_mem_homPar Sc sy cs ν (upWord s') t' hy.2)
  refine (pres D Sc).hom_induction (p := fun β => (omegaC D k (upLayers N) •
      (dnE Sc ν (upWord s') t' (hD Sc N hN) * upE Sc (-ν) s' (dnWord t') (hD Sc M hM))) ≫
      bubAt D Sc (-ν) (upWord s' ++ dnWord t') β ∈ _) ?_ ?_ ?_ ?_ β
  · intro d
    have hd : (pres D Sc).diag d ∈ bubPiece sy (-ν)
        (Diagram.degree (gdeg D sy) d, Diagram.degree (parityDeg (sig D)) d) := by
      refine ⟨(pres D Sc).diag_mem_homDeg _, ?_⟩
      rw [homPar_eq_homDeg sy cs]
      exact (pres D Sc).diag_mem_homDeg _
    rw [Linear.smul_comp, comp_bubAt hDU hd.2, smul_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, m, p, q, _, _, _, _, hy, hx, hd, ?_⟩)
    rfl
  · rw [map_zero, Limits.comp_zero]; exact Submodule.zero_mem _
  · intro f₁ f₂ h₁ h₂
    rw [map_add, Preadditive.comp_add]; exact Submodule.add_mem _ h₁ h₂
  · intro r f hf
    rw [map_smul, Linear.comp_smul]; exact Submodule.smul_mem _ r hf

include cs in
/-- The degree and parity of a product `α′(y) α(x) β`. -/
theorem gen_mem_homDeg {n m : ℤ} {p q : ZMod 2} {γ : Deg} {y : End (hObj D Sc sy hc t)}
    {x : End (hObj D Sc sy hc s)} {β : End ((pres D Sc).obj (ob D (-ν) []))}
    (hy : y ∈ homPiece D Sc sy hc t t n p) (hx : x ∈ homPiece D Sc sy hc s s m q)
    (hβ : β ∈ bubPiece sy (-ν) γ) :
    dnMap sy hc ν s t y * upMap sy hc ν s t x * bubMap ν s t β ∈
        (pres D Sc).homDeg (gdeg D sy) _ _ (γ.1 + (m + n)) ∧
      dnMap sy hc ν s t y * upMap sy hc ν s t x * bubMap ν s t β ∈
        (pres D Sc).homDeg (parityDeg (sig D)) _ _ (γ.2 + (q + p)) := by
  refine ⟨comp_mem_homDeg (bubAt_mem_gdeg sy _ hβ.1)
    (comp_mem_homDeg (upE_mem_gdeg sy (-ν) s (dnWord t) hx.1)
      (dnE_mem_gdeg sy ν (upWord s) t hy.1)), ?_⟩
  rw [← homPar_eq_homDeg sy cs]
  exact comp_mem_homPar (bubAt_mem_parity _ hβ.2)
    (comp_mem_homPar (upE_mem_homPar Sc sy cs (-ν) s (dnWord t) hx.2)
      (dnE_mem_homPar Sc sy cs ν (upWord s) t hy.2))

include cs in
/-- **Projecting the products to degree zero** keeps those of total degree zero. -/
theorem proj0_span_topGen {f : End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t)))}
    (hf : f ∈ Submodule.span k (topGen (Sc := Sc) sy hc ν s t)) :
    proj0 sy hc (-ν) _ _ f ∈ Submodule.span k (topGenZ (Sc := Sc) sy hc ν s t) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, m, p, q, γ, y, x, β, hy, hx, hβ, rfl⟩ := hf
    obtain ⟨h₁, h₂⟩ := gen_mem_homDeg cs hy hx hβ
    by_cases h0 : γ.1 + (m + n) = 0 ∧ γ.2 + (q + p) = 0
    · rw [proj0_of_mem (h0.1 ▸ h₁) (h0.2 ▸ h₂)]
      refine Submodule.subset_span ⟨n, m, p, q, γ, y, x, β, hy, hx, hβ, ?_, rfl⟩
      refine Prod.ext ?_ ?_
      · change n + m + γ.1 = 0; linarith [h0.1]
      · change p + q + γ.2 = 0; rw [← h0.2]; abel
    · rw [proj0_eq_zero h₁ h₂ (not_and_or.mp h0)]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

include cs in
/-- **Conjugating the degree-zero products by the top idempotent** lands in `topFam 0`. -/
theorem eps_span_topGenZ {z : End (hObj D Sc sy hc s)} {z' : End (hObj D Sc sy hc t)}
    (hz : z ≫ z = z) (hz' : z' ≫ z' = z') (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
    (hz0' : z' ∈ homPiece D Sc sy hc t t 0 0)
    {f : End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t)))}
    (hf : f ∈ Submodule.span k (topGenZ (Sc := Sc) sy hc ν s t)) :
    topEps sy hc ν s t z z' * f * topEps sy hc ν s t z z' ∈ topFam sy hc ν s t z z' 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, m, p, q, γ, y, x, β, hy, hx, hβ, htot, rfl⟩ := hf
    rw [eps_mul_gen_mul_eps cs hz0 hz0' hy hx hβ]
    exact mem_topFam_zero hz hz' hz0 hz0' hy hx hβ htot
  | zero => rw [mul_zero, zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add, add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hx

end Span

/-! ## Degrees in the top family -/

section Degrees

variable {ν : X} {s t : List I}

/-- Endomorphisms of `E_s F_t 1_{-ν}` of degree `γ.1` and parity `γ.2`. -/
abbrev topPiece (sy : Symmetrizer D) (ν : X) (s t : List I) (γ : Deg) :
    Submodule k (End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t)))) :=
  (pres D Sc).homDeg (gdeg D sy) _ _ γ.1 ⊓ (pres D Sc).homDeg (parityDeg (sig D)) _ _ γ.2

theorem topPiece_mul {γ δ : Deg} {x y : End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t)))}
    (hx : x ∈ topPiece (Sc := Sc) sy ν s t γ) (hy : y ∈ topPiece (Sc := Sc) sy ν s t δ) :
    x * y ∈ topPiece (Sc := Sc) sy ν s t (γ + δ) := by
  refine ⟨?_, ?_⟩
  · have := comp_mem_homDeg hy.1 hx.1
    rwa [add_comm] at this
  · have := comp_mem_homDeg hy.2 hx.2
    rwa [add_comm] at this

theorem prodFam_le_topPiece {E F : Deg → Submodule k _}
    (hE : ∀ γ, E γ ≤ topPiece (Sc := Sc) sy ν s t γ) (hF : ∀ γ, F γ ≤ topPiece sy ν s t γ)
    (γ : Deg) : prodFam E F γ ≤ topPiece sy ν s t γ := by
  refine Submodule.span_le.mpr ?_
  rintro r ⟨δ, x, hx, y, hy, rfl⟩
  have := topPiece_mul (hE _ hx) (hF _ hy)
  rwa [add_sub_cancel] at this

include cs in
/-- **The top family is graded**: `topFam γ` has degree `γ.1` and parity `γ.2`. -/
theorem topFam_le_topPiece (z : End (hObj D Sc sy hc s)) (z' : End (hObj D Sc sy hc t))
    (γ : Deg) : topFam sy hc ν s t z z' γ ≤ topPiece sy ν s t γ := by
  refine prodFam_le_topPiece (prodFam_le_topPiece ?_ ?_) ?_ γ
  · rintro δ _ ⟨y, hy, rfl⟩
    refine ⟨dnE_mem_gdeg sy ν (upWord s) t hy.1.1, ?_⟩
    rw [← homPar_eq_homDeg sy cs]
    exact dnE_mem_homPar Sc sy cs ν (upWord s) t hy.1.2
  · rintro δ _ ⟨x, hx, rfl⟩
    refine ⟨upE_mem_gdeg sy (-ν) s (dnWord t) hx.1.1, ?_⟩
    rw [← homPar_eq_homDeg sy cs]
    exact upE_mem_homPar Sc sy cs (-ν) s (dnWord t) hx.1.2
  · rintro δ _ ⟨β, hβ, rfl⟩
    refine ⟨bubAt_mem_gdeg sy _ hβ.1, ?_⟩
    rw [← homPar_eq_homDeg sy cs]
    exact bubAt_mem_parity _ hβ.2

end Degrees

/-! ## The top idempotent is local modulo shorter words -/

section Local

variable {ν : X} {s t : List I}

include cs in
/-- **The top idempotent is local modulo shorter words** (BE2, arXiv:1701.04133v2, proof of
Theorem 11.7). Let `z`, `z′` be even degree-zero idempotents with local corners and
`ε = α′(z′) α(z)`. An endomorphism `f` of `E_s F_t 1_{-ν}` of degree zero and parity zero with
`ε f ε = f` is nilpotent modulo the maps through shorter words, or has an inverse of degree zero
and parity zero in `ε End ε` modulo them. -/
theorem top_localMod {z : End (hObj D Sc sy hc s)} {z' : End (hObj D Sc sy hc t)}
    (hz : z ≫ z = z) (hz' : z' ≫ z' = z') (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
    (hz0' : z' ∈ homPiece D Sc sy hc t t 0 0) {NE NE' : Submodule k _} {a a' lo lo' : ℕ}
    (hE : LocalCorner (heCorner z) z NE a lo) (hE' : LocalCorner (heCorner z') z' NE' a' lo')
    {f : End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t)))}
    (hf : f ∈ topPiece sy ν s t 0)
    (hεf : topEps sy hc ν s t z z' * f * topEps sy hc ν s t z z' = f) :
    (∃ N, f ^ (N + 1) ∈ ShortSpan Sc (-ν) (upWord s ++ dnWord t) (upWord s ++ dnWord t)) ∨
      ∃ w ∈ topPiece sy ν s t 0, topEps sy hc ν s t z z' * w * topEps sy hc ν s t z z' = w ∧
        f * w - topEps sy hc ν s t z z' ∈ ShortSpan Sc (-ν) _ _ ∧
        w * f - topEps sy hc ν s t z z' ∈ ShortSpan Sc (-ν) _ _ := by
  set ε := topEps sy hc ν s t z z'
  set T : Submodule k (End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t)))) :=
    ShortSpan Sc (-ν) (upWord s ++ dnWord t) (upWord s ++ dnWord t)
  have hTl : ∀ r x, x ∈ T → r * x ∈ T := fun r _ hx => shortSpan_mul_left Sc _ _ r hx
  have hTr : ∀ x r, x ∈ T → x * r ∈ T := fun _ r hx => shortSpan_mul_right Sc _ _ r hx
  have hb : LSorted (upWord s ++ dnWord t) :=
    lSorted_of_sorted ⟨s, t, by rw [dnWord_eq_map]; rfl⟩
  have htop := udSpan_sup_shortSpan Sc cs (-ν) s t hb rfl
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := f))
  set pu : End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t))) :=
    proj0 sy hc (-ν) _ _ u with hpu
  set pv : End ((pres D Sc).obj (ob D (-ν) (upWord s ++ dnWord t))) :=
    proj0 sy hc (-ν) _ _ v with hpv
  have hfp : f = pu + pv := by
    have := (proj0 sy hc (-ν) (upWord s ++ dnWord t) (upWord s ++ dnWord t)).map_add u v
    rw [huv, proj0_of_mem hf.1 hf.2] at this
    exact this
  have hx := eps_span_topGenZ cs hz hz' hz0 hz0'
    (proj0_span_topGen cs (udSpan_le_span_topGen cs hu))
  have ht : ε * pv * ε ∈ T := hTr _ _ (hTl _ _ (proj0_mem_shortSpan hv))
  have hfxt : f = ε * pu * ε + ε * pv * ε := by
    conv_lhs => rw [← hεf, hfp]
    rw [mul_add, add_mul]
  obtain ⟨N, b, lo'', hL⟩ := localCorner_topFam cs ν s t hE hE'
  have h1 : bubMap ν s t (1 : End ((pres D Sc).obj (ob D (-ν) []))) = 1 :=
    bubAt_id (-ν) (upWord s ++ dnWord t)
  rw [h1, mul_one] at hL
  rcases hL.nilpotent_or_inverse_mod hTl hTr hx ht with h | ⟨w, hw, hw₁, hw₂⟩
  · refine Or.inl ⟨b, ?_⟩
    rw [hfxt]
    exact hTr _ _ h
  · refine Or.inr ⟨w, topFam_le_topPiece cs z z' 0 hw, ?_, ?_, ?_⟩
    · have e₁ : ε * w = w := hL.unit_mul 0 w hw
      have e₂ : w * ε = w := hL.mul_unit 0 w hw
      rw [e₁, e₂]
    · rwa [hfxt]
    · rwa [hfxt]

end Local

end OddMath.SKM
