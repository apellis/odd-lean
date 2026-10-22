/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SerreComplex
import OddMath.QuiverHecke.SplitComplexK0
import OddMath.QuiverHecke.EnvelopeDividedPowers

/-!
# Proposition 11.2 with its shifts, in `K₀(Ḣ_{q,π})`

Brundan–Ellis, arXiv:1701.04133v2, Proposition 11.2 (Hill–Wang, arXiv:1202.2769v2,
Theorem 5.9), with the degree and parity shifts of the printed statement. For `i ≠ j` and
`M = d_ij + 1`, `OddMath.QuiverHecke.SerreComplex` gives the maps `upMap a`, `downMap a` between
the words `i^a j i^{M-a}` and the splitting identities. Here:

* the block idempotents `e_a` are homogeneous of degree `0` and even, `upMap a` has degree
  `d_j d_ji - 2 a d_i` and parity `|i||j| + a|i|`, and `downMap a` has degree
  `d_i d_ij - 2(M - a - 1) d_i` and parity `|i||j| + (M - a - 1)|i|` (`upMap_mem`,
  `downMap_mem`, for the integer grading and for the parity at once);
* `term a` is the summand `Q^{sh a} Π^{par a} (i^a j i^{M-a}, e_a)` of `Ḣ_{q,π}` with
  `sh a = d_i (a(a-1)/2 + (M-a)(M-a-1)/2)` and `par a = r(r-1)/2 |i| + r |i||j|`, `r = M - a`:
  the projective `Π^{par a} P(i^{(a)} j i^{(M-a)})` of BE2, whose degree normalization
  `Q^{-d_i a(a-1)/2 - d_i r(r-1)/2}` appears with the opposite sign because the envelope is
  contravariant in the shift (`OddMath.QuiverHecke.EnvelopeDividedPowers`);
* with these shifts the maps are even of degree zero (`sh_sub_succ`, `par_add_succ`, ...), so
  they give a split complex in `Ḣ_{q,π}` (`isSplitK`), and
  `∑_{a ≤ M} (-1)^a [term a] = 0` in `K₀(Ḣ_{q,π})` (`class_alternating_sum`); equivalently the
  even and odd terms have the same total class (`class_even_eq_odd`).

So the printed shifts are the right ones: no correction beyond ERRATA [BE2] 14 is needed. The
comparison of `e_a` with the idempotents of Lemma 11.1 (`evenCornerProjector`,
`oddCornerProjector`) is not made here.
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke.SerreComplex
open CategoryTheory StringDiagrams OddMath.QuiverHecke
open SignedNilHecke
open Categorification.KLR.KL2.NH (wp Wb chL chR)
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

/-! ## Homogeneity -/

section Degrees

variable {G : Type*} [AddCommMonoid G] (δ : (sig D).Gen → G)

/-- The morphisms `t → t'` of `H` that are homogeneous of degree `d` for the generator
degrees `δ` (the integer grading or the parity). -/
abbrev piece (t t' : List I) (d : G) := (pres D Sc).homDeg δ (ob D t) (ob D t') d

theorem degree_mkD {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t') :
    Diagram.degree δ (mkD D ls h) = (ls.map fun x => δ x.2.1).sum := by
  simp only [Diagram.degree, layers_mkD, layList, List.map_map]
  rfl

variable {D Sc δ}

theorem cl_mem {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t') :
    cl D Sc t t' gs h ∈ piece D Sc δ t t' ((pl t gs).map fun x => δ x.2.1).sum :=
  Presentation.diag_mem_homDeg' (degree_mkD D δ _ h)

theorem pl_cross_of {t : List I} {p : ℕ} {x y : I} (hx : t[p]? = some x)
    (hy : t[p + 1]? = some y) :
    pl t [.cross p] = [(t.take p, Shape.cross x y, t.drop (p + 2))] := by
  obtain ⟨hp, rfl⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨hp1, rfl⟩ := List.getElem?_eq_some_iff.mp hy
  have e : t.drop p = t[p] :: t[p + 1] :: t.drop (p + 2) := by
    rw [List.drop_eq_getElem_cons hp, List.drop_eq_getElem_cons hp1]
  simp only [pl_cons, pl_nil, List.append_nil, PG.ld, e]

theorem pl_dot_of {t : List I} {p : ℕ} {x : I} (hx : t[p]? = some x) :
    pl t [.dot p] = [(t.take p, Shape.dot x, t.drop (p + 1))] := by
  obtain ⟨hp, rfl⟩ := List.getElem?_eq_some_iff.mp hx
  have e : t.drop p = t[p] :: t.drop (p + 1) := List.drop_eq_getElem_cons hp
  simp only [pl_cons, pl_nil, List.append_nil, PG.ld, e]

theorem cl_cross_mem {t t' : List I} {p : ℕ} {x y : I} (hx : t[p]? = some x)
    (hy : t[p + 1]? = some y) (h : SChain t (pl t [.cross p]) t') :
    cl D Sc t t' [.cross p] h ∈ piece D Sc δ t t' (δ (.cross x y)) := by
  have := cl_mem (D := D) (Sc := Sc) (δ := δ) [.cross p] h
  rwa [pl_cross_of hx hy, List.map_singleton, List.sum_singleton] at this

theorem crossE_mem {w : List I} {p : ℕ} {x : I} (hx : w[p]? = some x)
    (hx' : w[p + 1]? = some x) :
    crossE D Sc w p ∈ piece D Sc δ w w (δ (.cross x x)) := by
  unfold crossE genE
  split_ifs with h
  · exact cl_cross_mem hx hx' h
  · exact Submodule.zero_mem _

theorem dotE_mem {w : List I} {p : ℕ} {x : I} (hx : w[p]? = some x) :
    dotE D Sc w p ∈ piece D Sc δ w w (δ (.dot x)) := by
  unfold dotE genE
  split_ifs with h
  · have := cl_mem (D := D) (Sc := Sc) (δ := δ) [.dot p] h
    rwa [pl_dot_of hx, List.map_singleton, List.sum_singleton] at this
  · exact Submodule.zero_mem _

theorem wp_mem {w : List I} {T : ℕ → End ((pres D Sc).obj (ob D w))} {d : G} :
    ∀ {ρ : List ℕ}, (∀ j ∈ ρ, T j ∈ piece D Sc δ w w d) →
      wp T ρ ∈ piece D Sc δ w w (ρ.length • d)
  | [], _ => by
    rw [List.length_nil, zero_smul]
    exact (pres D Sc).id_mem_homDeg δ _
  | j :: ρ, h => by
    rw [List.length_cons, succ_nsmul]
    change wp (B := End ((pres D Sc).obj (ob D w))) T ρ ≫ T j ∈ _
    exact Presentation.comp_mem_homDeg (wp_mem fun l hl => h l (List.mem_cons_of_mem _ hl))
      (h j List.mem_cons_self)

theorem dem_mem {w : List I} {ε : ℤˣ} {s n : ℕ} {X T : ℕ → End ((pres D Sc).obj (ob D w))}
    {dc dd : G} (hsum : dd + dc = 0)
    (hT : ∀ j, s ≤ j → j + 1 < s + n → T j ∈ piece D Sc δ w w dc)
    (hX : ∀ j, s ≤ j → j + 1 < s + n → X (j + 1) ∈ piece D Sc δ w w dd) (j : ℕ) :
    dem (B := End ((pres D Sc).obj (ob D w))) ε s n X T j ∈ piece D Sc δ w w 0 := by
  unfold dem
  split_ifs with h
  · refine neg_mem (zsmul_mem ?_ _)
    change X (j + 1) ≫ T j ∈ _
    rw [← hsum]
    exact Presentation.comp_mem_homDeg (hX j h.1 h.2) (hT j h.1 h.2)
  · exact Submodule.zero_mem _

theorem idem_mem {w : List I} {ε : ℤˣ} {s n : ℕ} {X T : ℕ → End ((pres D Sc).obj (ob D w))}
    {dc dd : G} (hsum : dd + dc = 0)
    (hT : ∀ j, s ≤ j → j + 1 < s + n → T j ∈ piece D Sc δ w w dc)
    (hX : ∀ j, s ≤ j → j + 1 < s + n → X (j + 1) ∈ piece D Sc δ w w dd) (s' n' : ℕ) :
    idem (B := End ((pres D Sc).obj (ob D w))) ε s n X T s' n' ∈ piece D Sc δ w w 0 := by
  have := wp_mem (δ := δ) (T := dem (B := End ((pres D Sc).obj (ob D w))) ε s n X T) (d := 0)
    (ρ := (Categorification.NilHecke.w0Word n').map (s' + ·))
    (fun j _ => dem_mem hsum hT hX j)
  rwa [smul_zero] at this

end Degrees

section MapDegrees

variable {G : Type*} [AddCommMonoid G] {δ : (sig D).Gen → G}
variable {D Sc} {i j : I} {M : ℕ}

theorem eIdem_mem (hδ : δ (.dot i) + δ (.cross i i) = 0) (a : ℕ) :
    eIdem D Sc i j M a ∈ piece D Sc δ (word i j M a) (word i j M a) 0 := by
  have hl : lIdem D Sc i j M a ∈ piece D Sc δ (word i j M a) (word i j M a) 0 :=
    idem_mem hδ (fun p _ hp => crossE_mem (word_lt (by omega)) (word_lt (by omega)))
      (fun p _ hp => dotE_mem (word_lt (by omega))) 0 a
  have hr : rIdem D Sc i j M a ∈ piece D Sc δ (word i j M a) (word i j M a) 0 :=
    idem_mem hδ
      (fun p hp hp' => crossE_mem (word_gt (by omega) (by omega)) (word_gt (by omega) (by omega)))
      (fun p hp hp' => dotE_mem (word_gt (by omega) (by omega))) (a + 1) (M - a)
  have := Presentation.comp_mem_homDeg hr hl
  rwa [add_zero] at this

theorem up_mem {a : ℕ} (ha : a < M) :
    up D Sc i j M ha ∈ piece D Sc δ (word i j M a) (word i j M (a + 1)) (δ (.cross j i)) :=
  cl_cross_mem (word_self a) (word_gt (by omega) (by omega)) _

theorem down_mem {a : ℕ} (ha : a < M) :
    down D Sc i j M ha ∈ piece D Sc δ (word i j M (a + 1)) (word i j M a) (δ (.cross i j)) :=
  cl_cross_mem (word_lt (by omega)) (word_self (a + 1)) _

theorem chL_up_mem (a : ℕ) :
    chL (B := End (wobj D Sc i j M (a + 1))) (tw D Sc i j M (a + 1)) 0 a ∈
      piece D Sc δ (word i j M (a + 1)) (word i j M (a + 1)) (a • δ (.cross i i)) := by
  have := wp_mem (δ := δ) (T := tw D Sc i j M (a + 1)) (d := δ (.cross i i))
    (ρ := List.range' 0 a) (fun p hp => by
      rw [List.mem_range'_1] at hp
      exact crossE_mem (word_lt (by omega)) (word_lt (by omega)))
  rwa [List.length_range'] at this

theorem chR_down_mem {a : ℕ} (ha : a < M) :
    chR (B := End (wobj D Sc i j M a)) (tw D Sc i j M a) (a + 1) (M - (a + 1)) ∈
      piece D Sc δ (word i j M a) (word i j M a) ((M - (a + 1)) • δ (.cross i i)) := by
  have := wp_mem (δ := δ) (T := tw D Sc i j M a) (d := δ (.cross i i))
    (ρ := (List.range' (a + 1) (M - (a + 1))).reverse) (fun p hp => by
      rw [List.mem_reverse, List.mem_range'_1] at hp
      exact crossE_mem (word_gt (by omega) (by omega)) (word_gt (by omega) (by omega)))
  rwa [List.length_reverse, List.length_range'] at this

theorem upMap_mem (hδ : δ (.dot i) + δ (.cross i i) = 0) {a : ℕ} (ha : a < M) :
    upMap D Sc i j M ha ∈ piece D Sc δ (word i j M a) (word i j M (a + 1))
      (δ (.cross j i) + a • δ (.cross i i)) := by
  have := Presentation.comp_mem_homDeg (eIdem_mem (j := j) (M := M) hδ a)
    (Presentation.comp_mem_homDeg (up_mem ha) (chL_up_mem (D := D) (Sc := Sc) (j := j) a))
  rwa [zero_add] at this

theorem downMap_mem (hδ : δ (.dot i) + δ (.cross i i) = 0) {a : ℕ} (ha : a < M) :
    downMap D Sc i j M ha ∈ piece D Sc δ (word i j M (a + 1)) (word i j M a)
      (δ (.cross i j) + (M - (a + 1)) • δ (.cross i i)) := by
  have := Presentation.comp_mem_homDeg (eIdem_mem (j := j) (M := M) hδ (a + 1))
    (Presentation.comp_mem_homDeg (down_mem ha) (chR_down_mem (D := D) (Sc := Sc) ha))
  rwa [zero_add] at this

end MapDegrees

/-! ## The splitting identities in `H` with one family of scalars -/

section Scalars

variable {D Sc} {i j : I} {M : ℕ}

theorem single_inj {a b : Word I (M + 1)} {f g : wordObj D Sc b ⟶ wordObj D Sc a}
    (h : (Hn.single a b f : DividedPowerModules.ModuleRing D Sc (M + 1)) = Hn.single a b g) :
    f = g := by
  have h' : Hn.single a b f = Hn.single a b g := Unitization.inr_injective h
  unfold Hn.single FiniteHomMatrix.single at h'
  simpa using DFunLike.congr_fun h' (a, b)

open DividedPowerModules in
/-- HW Theorem 5.9 in `H`, with the scalars `c⁻` eliminated: one family `c` with
`e_0 = c_0 f_0 g_0`, `e_{a+1} = c_{a+1} f_{a+1} g_{a+1} + c_a g_a f_a` and
`e_M = c_{M-1} g_{M-1} f_{M-1}` (composites in diagrammatic order). -/
theorem exists_scalars (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    ∃ c : ℕ → k,
      eIdem D Sc i j M 0 = c 0 • (upMap D Sc i j M (by omega : 0 < M) ≫
        downMap D Sc i j M (by omega : 0 < M)) ∧
      (∀ a (h : a + 1 < M), eIdem D Sc i j M (a + 1) =
        c (a + 1) • (upMap D Sc i j M h ≫ downMap D Sc i j M h) +
          c a • (downMap D Sc i j M (Nat.lt_of_succ_lt h) ≫
            upMap D Sc i j M (Nat.lt_of_succ_lt h))) ∧
      (∀ a (h : a + 1 = M), eIdem D Sc i j M (a + 1) =
        c a • (downMap D Sc i j M (by omega : a < M) ≫ upMap D Sc i j M (by omega : a < M))) := by
  obtain ⟨cp, cm, hs⟩ := isSplit (D := D) (Sc := Sc) hij hM
  refine ⟨cp, ?_, fun a h => ?_, fun a h => ?_⟩
  · have e := hs.split' 0 (Nat.zero_le M)
    rw [ite_eq_right (lt_irrefl 0), add_zero, ← Unitization.inr_mul, gH_mul_fH (by omega),
      eH, dite_eq_left (Nat.zero_le M), ← Unitization.inr_smul,
      ← FiniteHomMatrix.single_smul] at e
    exact single_inj e
  · have e := hs.split' (a + 1) h.le
    rw [ite_eq_left (Nat.succ_pos a), Nat.add_sub_cancel, ← Unitization.inr_mul,
      ← Unitization.inr_mul, gH_mul_fH h, fH_mul_gH (Nat.lt_of_succ_lt h), eH,
      dite_eq_left h.le, ← Unitization.inr_smul, ← Unitization.inr_smul,
      ← Unitization.inr_add, ← single_comb] at e
    exact single_inj e
  · have e := hs.split' (a + 1) h.le
    rw [ite_eq_left (Nat.succ_pos a), Nat.add_sub_cancel, hs.g_top (a + 1) h.ge,
      zero_mul, smul_zero, zero_add, ← Unitization.inr_mul, fH_mul_gH (by omega), eH,
      dite_eq_left h.le, ← Unitization.inr_smul, ← FiniteHomMatrix.single_smul] at e
    exact single_inj e

end Scalars

/-! ## Shifted terms in the envelope -/

section Lift

open GradedSupercategory OddMath.SKM.Summands

variable {A : Type*} [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
  [GradedSupercategory k A]

/-- A homogeneous morphism `g : f → f'` as an even degree-zero morphism between the shifts
`Q^m Π^p f → Q^n Π^{p'} f'`. -/
def hlift {f f' : A} {m n : ℤ} {p p' : ZMod 2} (g : f ⟶ f')
    (hd : g ∈ degree (R := k) f f' (m - n))
    (hp : g ∈ Supercategory.parity (R := k) f f' (p + p')) :
    shifted (k := k) f m p ⟶ shifted (k := k) f' n p' :=
  ⟨⟨g, by change g ∈ degree (R := k) _ _ (0 + (m - n)); simpa using hd⟩,
    by change g ∈ Supercategory.parity (R := k) _ _ (0 + (p + p')); simpa using hp⟩

theorem base_ext {f f' : A} {m n : ℤ} {p p' : ZMod 2}
    {x y : shifted (k := k) f m p ⟶ shifted (k := k) f' n p'} (h : x.1.1 = y.1.1) : x = y :=
  Subtype.ext (Subtype.ext h)

end Lift

theorem parityDeg_eq (g : Shape I) : Presentation.parityDeg (sig D) g = g.parity D := by
  simp only [Presentation.parityDeg, sig]
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (g.parity D) with h | h <;> simp [h]

section Envelope

open GradedSupercategory OddMath.SKM.Summands CategoryTheory.Idempotents

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
variable {D Sc} {i j : I} {M : ℕ}

theorem rIdem_eq_one {a : ℕ} (h : M ≤ a) : rIdem D Sc i j M a = 1 := by
  unfold rIdem
  rw [show M - a = 0 by omega]
  simp [idem, Wb, Categorification.NilHecke.w0Word]

theorem eIdem_idem_all (a : ℕ) :
    eIdem D Sc i j M a * eIdem D Sc i j M a = eIdem D Sc i j M a := by
  by_cases ha : a ≤ M
  · exact eIdem_idem a ha
  · rw [eIdem, rIdem_eq_one (by omega), mul_one, lIdem_idem]

variable (i j M) in
/-- The degree shift `d_i (a(a-1)/2 + (M-a)(M-a-1)/2)` of the term `a`. -/
def sh (a : ℕ) : ℤ := sy.d i * ((a.choose 2 : ℕ) + ((M - a).choose 2 : ℕ) : ℤ)

variable (D i j M) in
/-- The parity shift `r(r-1)/2 |i| + r |i||j|`, `r = M - a`, of the term `a`. -/
def par (a : ℕ) : ZMod 2 :=
  (((M - a).choose 2 : ℕ) : ZMod 2) * D.parity i +
    ((M - a : ℕ) : ZMod 2) * (D.parity i * D.parity j)

theorem gdeg_dot_add_cross (i : I) : gdeg D sy (.dot i) + gdeg D sy (.cross i i) = 0 := by
  simp only [gdeg, D.d_self]; ring

theorem parityDeg_dot_add_cross (i : I) :
    Presentation.parityDeg (sig D) (.dot i) + Presentation.parityDeg (sig D) (.cross i i) = 0 := by
  rw [parityDeg_eq, parityDeg_eq]
  simp only [Shape.parity]
  generalize D.parity i = x
  revert x; decide

theorem eIdem_degree (a : ℕ) :
    (eIdem D Sc i j M a : hObj D Sc sy hc (word i j M a) ⟶ hObj D Sc sy hc (word i j M a)) ∈
      degree (R := k) (C := HGr D Sc sy hc) _ _ 0 :=
  eIdem_mem (gdeg_dot_add_cross sy i) a

theorem eIdem_even (a : ℕ) :
    (eIdem D Sc i j M a : hObj D Sc sy hc (word i j M a) ⟶ hObj D Sc sy hc (word i j M a)) ∈
      Supercategory.parity (R := k) (C := HGr D Sc sy hc) _ _ 0 :=
  eIdem_mem (parityDeg_dot_add_cross i) a

variable (i j M) in
/-- **BE2 Proposition 11.2, the terms**: `Q^{sh a} Π^{par a} (i^a j i^{M-a}, e_a)` in
`Ḣ_{q,π}`, the projective `Π^{par a} P(i^{(a)} j i^{(M-a)})` of BE2 (in the envelope the shift is
contravariant, see `OddMath.QuiverHecke.EnvelopeDividedPowers`). -/
def term (a : ℕ) : HKar D Sc sy hc :=
  raw (f := hObj D Sc sy hc (word i j M a)) (eIdem_idem_all a) (eIdem_degree sy hc a)
    (eIdem_even sy hc a) (sh sy i M a) (par D i j M a)

end Envelope

/-! ### The shifts match the degrees and parities of the maps -/

section Shifts

variable (sy : SKM.Symmetrizer D)
variable {D} {i j : I} {M : ℕ}

theorem sh_sub_succ (hij : i ≠ j) (hM : M = D.dn i j + 1) {a : ℕ} (ha : a < M) :
    sh sy i M a - sh sy i M (a + 1) = gdeg D sy (.cross j i) + a • gdeg D sy (.cross i i) := by
  obtain ⟨n, rfl⟩ : ∃ n, M = a + 1 + n := ⟨M - (a + 1), by omega⟩
  have hd : D.d i j = a + n := by rw [← D.dn_cast hij]; omega
  simp only [sh, gdeg, D.d_self, nsmul_eq_mul, show a + 1 + n - a = n + 1 by omega,
    show a + 1 + n - (a + 1) = n by omega, Nat.choose_succ_succ', Nat.choose_one_right]
  push_cast
  linear_combination sy.symm i j - sy.d i * hd

theorem sh_succ_sub (hij : i ≠ j) (hM : M = D.dn i j + 1) {a : ℕ} (ha : a < M) :
    sh sy i M (a + 1) - sh sy i M a =
      gdeg D sy (.cross i j) + (M - (a + 1)) • gdeg D sy (.cross i i) := by
  obtain ⟨n, rfl⟩ : ∃ n, M = a + 1 + n := ⟨M - (a + 1), by omega⟩
  have hd : D.d i j = a + n := by rw [← D.dn_cast hij]; omega
  simp only [sh, gdeg, D.d_self, nsmul_eq_mul, show a + 1 + n - a = n + 1 by omega,
    show a + 1 + n - (a + 1) = n by omega, Nat.choose_succ_succ', Nat.choose_one_right]
  push_cast
  linear_combination -(sy.d i) * hd

theorem parity_d_mul (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    ((M - 1 : ℕ) : ZMod 2) * D.parity i = 0 := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (D.parity i) with h | h
  · rw [h, mul_zero]
  · rw [h, mul_one]
    obtain ⟨r, hr⟩ := D.even_d_of_odd h j
    have : M - 1 = r.toNat + r.toNat := by
      have := D.dn_cast hij; omega
    rw [this, Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem par_add_succ (hij : i ≠ j) (hM : M = D.dn i j + 1) {a : ℕ} (ha : a < M) :
    par D i j M a + par D i j M (a + 1) =
      Presentation.parityDeg (sig D) (.cross j i) +
        a • Presentation.parityDeg (sig D) (.cross i i) := by
  have hev := parity_d_mul hij hM
  obtain ⟨n, rfl⟩ : ∃ n, M = a + 1 + n := ⟨M - (a + 1), by omega⟩
  simp only [par, parityDeg_eq, Shape.parity, nsmul_eq_mul, show a + 1 + n - a = n + 1 by omega,
    show a + 1 + n - (a + 1) = n by omega, show a + 1 + n - 1 = a + n by omega,
    Nat.choose_succ_succ', Nat.choose_one_right] at hev ⊢
  push_cast at hev ⊢
  generalize (a : ZMod 2) = x at *
  generalize (n : ZMod 2) = y at *
  generalize ((n.choose 2 : ℕ) : ZMod 2) = z
  generalize D.parity i = p at *
  generalize D.parity j = q
  revert x y z p q; decide

theorem par_succ_add {a : ℕ} (ha : a < M) :
    par D i j M (a + 1) + par D i j M a =
      Presentation.parityDeg (sig D) (.cross i j) +
        (M - (a + 1)) • Presentation.parityDeg (sig D) (.cross i i) := by
  obtain ⟨n, rfl⟩ : ∃ n, M = a + 1 + n := ⟨M - (a + 1), by omega⟩
  simp only [par, parityDeg_eq, Shape.parity, nsmul_eq_mul, show a + 1 + n - a = n + 1 by omega,
    show a + 1 + n - (a + 1) = n by omega, Nat.choose_succ_succ', Nat.choose_one_right]
  push_cast
  generalize (n : ZMod 2) = y
  generalize ((n.choose 2 : ℕ) : ZMod 2) = z
  generalize D.parity i = p
  generalize D.parity j = q
  revert y z p q; decide

end Shifts

/-! ### The complex in the envelope -/

section KComplex

open GradedSupercategory OddMath.SKM.Summands CategoryTheory.Idempotents

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
variable {D Sc} {i j : I} {M : ℕ} (hij : i ≠ j) (hM : M = D.dn i j + 1)
include hij hM

theorem upMap_degree {a : ℕ} (ha : a < M) :
    (upMap D Sc i j M ha :
      hObj D Sc sy hc (word i j M a) ⟶ hObj D Sc sy hc (word i j M (a + 1))) ∈
      degree (R := k) (C := HGr D Sc sy hc) _ _ (sh sy i M a - sh sy i M (a + 1)) := by
  rw [sh_sub_succ sy hij hM ha]
  exact upMap_mem (gdeg_dot_add_cross sy i) ha

theorem upMap_parity {a : ℕ} (ha : a < M) :
    (upMap D Sc i j M ha :
      hObj D Sc sy hc (word i j M a) ⟶ hObj D Sc sy hc (word i j M (a + 1))) ∈
      Supercategory.parity (R := k) (C := HGr D Sc sy hc) _ _
        (par D i j M a + par D i j M (a + 1)) := by
  rw [par_add_succ hij hM ha]
  exact upMap_mem (parityDeg_dot_add_cross i) ha

theorem downMap_degree {a : ℕ} (ha : a < M) :
    (downMap D Sc i j M ha :
      hObj D Sc sy hc (word i j M (a + 1)) ⟶ hObj D Sc sy hc (word i j M a)) ∈
      degree (R := k) (C := HGr D Sc sy hc) _ _ (sh sy i M (a + 1) - sh sy i M a) := by
  rw [sh_succ_sub sy hij hM ha]
  exact downMap_mem (gdeg_dot_add_cross sy i) ha

omit hij hM in
theorem downMap_parity {a : ℕ} (ha : a < M) :
    (downMap D Sc i j M ha :
      hObj D Sc sy hc (word i j M (a + 1)) ⟶ hObj D Sc sy hc (word i j M a)) ∈
      Supercategory.parity (R := k) (C := HGr D Sc sy hc) _ _
        (par D i j M (a + 1) + par D i j M a) := by
  rw [par_succ_add ha]
  exact downMap_mem (parityDeg_dot_add_cross i) ha

/-- The map `c_a • upMap a : term a → term (a + 1)` (zero for `a ≥ M`). -/
def fK (c : ℕ → k) (a : ℕ) : term sy hc i j M a ⟶ term sy hc i j M (a + 1) :=
  if h : a < M then
    ⟨(Mat_.embedding _).map (hlift (c a • (upMap D Sc i j M h :
        hObj D Sc sy hc (word i j M a) ⟶ hObj D Sc sy hc (word i j M (a + 1))))
      (Submodule.smul_mem _ _ (upMap_degree sy hc hij hM h))
      (Submodule.smul_mem _ _ (upMap_parity sy hc hij hM h))), by
      change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply base_ext
      change eIdem D Sc i j M a ≫ (c a • upMap D Sc i j M h) ≫ eIdem D Sc i j M (a + 1) =
        c a • upMap D Sc i j M h
      rw [Linear.smul_comp, Linear.comp_smul]
      rw [← Category.assoc, eIdem_comp_upMap, upMap_comp_eIdem]⟩
  else 0

/-- The map `downMap a : term (a + 1) → term a` (zero for `a ≥ M`). -/
def gK (a : ℕ) : term sy hc i j M (a + 1) ⟶ term sy hc i j M a :=
  if h : a < M then
    ⟨(Mat_.embedding _).map (hlift (downMap D Sc i j M h :
        hObj D Sc sy hc (word i j M (a + 1)) ⟶ hObj D Sc sy hc (word i j M a))
      (downMap_degree sy hc hij hM h) (downMap_parity sy hc h)), by
      change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply base_ext
      change eIdem D Sc i j M (a + 1) ≫ downMap D Sc i j M h ≫ eIdem D Sc i j M a =
        downMap D Sc i j M h
      rw [← Category.assoc, eIdem_comp_downMap, downMap_comp_eIdem]⟩
  else 0

theorem isSplitK (c : ℕ → k)
    (h0 : eIdem D Sc i j M 0 = c 0 • (upMap D Sc i j M (by omega : 0 < M) ≫
        downMap D Sc i j M (by omega : 0 < M)))
    (hs : ∀ a (h : a + 1 < M), eIdem D Sc i j M (a + 1) =
        c (a + 1) • (upMap D Sc i j M h ≫ downMap D Sc i j M h) +
          c a • (downMap D Sc i j M (Nat.lt_of_succ_lt h) ≫
            upMap D Sc i j M (Nat.lt_of_succ_lt h)))
    (ht : ∀ a (h : a + 1 = M), eIdem D Sc i j M (a + 1) =
        c a • (downMap D Sc i j M (by omega : a < M) ≫ upMap D Sc i j M (by omega : a < M))) :
    SplitComplex.IsSplitK M (term sy hc i j M) (fK sy hc hij hM c) (gK sy hc hij hM) where
  ff a := by
    by_cases h : a + 1 < M
    · unfold fK
      rw [dite_eq_left (Nat.lt_of_succ_lt h), dite_eq_left h]
      apply Karoubi.hom_ext
      change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = 0
      rw [← Functor.map_comp, ← Functor.map_zero (Mat_.embedding _)]
      congr 1
      apply base_ext
      change (c a • upMap D Sc i j M (Nat.lt_of_succ_lt h)) ≫ (c (a + 1) • upMap D Sc i j M h) = 0
      rw [Linear.smul_comp, Linear.comp_smul, upMap_comp_upMap h, smul_zero, smul_zero]
    · rw [show fK sy hc hij hM c (a + 1) = 0 from dite_eq_right h, Limits.comp_zero]
  gg a := by
    by_cases h : a + 1 < M
    · unfold gK
      rw [dite_eq_left (Nat.lt_of_succ_lt h), dite_eq_left h]
      apply Karoubi.hom_ext
      change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = 0
      rw [← Functor.map_comp, ← Functor.map_zero (Mat_.embedding _)]
      congr 1
      apply base_ext
      change downMap D Sc i j M h ≫ downMap D Sc i j M (Nat.lt_of_succ_lt h) = 0
      rw [downMap_comp_downMap h]
    · rw [show gK sy hc hij hM (a + 1) = 0 from dite_eq_right h, Limits.zero_comp]
  f_top := dite_eq_right (lt_irrefl M)
  split_zero := by
    unfold fK gK
    rw [dite_eq_left (by omega : 0 < M), dite_eq_left (by omega : 0 < M)]
    apply Karoubi.hom_ext
    change (Mat_.embedding _).map _ = (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _
    rw [← Functor.map_comp]
    congr 1
    apply base_ext
    change eIdem D Sc i j M 0 = (c 0 • upMap D Sc i j M _) ≫ downMap D Sc i j M _
    rw [Linear.smul_comp, h0]
  split_succ a ha := by
    rcases Nat.lt_or_ge (a + 1) M with h | h
    · unfold fK gK
      rw [dite_eq_left h, dite_eq_left h, dite_eq_left (Nat.lt_of_succ_lt h),
        dite_eq_left (Nat.lt_of_succ_lt h)]
      apply Karoubi.hom_ext
      change (Mat_.embedding _).map _ = (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ +
        (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add]
      congr 1
      apply base_ext
      change eIdem D Sc i j M (a + 1) = (c (a + 1) • upMap D Sc i j M h) ≫ downMap D Sc i j M h +
        downMap D Sc i j M _ ≫ (c a • upMap D Sc i j M _)
      rw [Linear.smul_comp, Linear.comp_smul, hs a h]
    · have hM' : a + 1 = M := by omega
      rw [show fK sy hc hij hM c (a + 1) = 0 from dite_eq_right (by omega), Limits.zero_comp,
        zero_add]
      unfold fK gK
      rw [dite_eq_left (by omega : a < M), dite_eq_left (by omega : a < M)]
      apply Karoubi.hom_ext
      change (Mat_.embedding _).map _ = (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _
      rw [← Functor.map_comp]
      congr 1
      apply base_ext
      change eIdem D Sc i j M (a + 1) = downMap D Sc i j M _ ≫ (c a • upMap D Sc i j M _)
      rw [Linear.comp_smul, ht a hM']

end KComplex

/-! ### Proposition 11.2 in `K₀(Ḣ_{q,π})` -/

section Headline

open CategoryTheory.Idempotents

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
variable {D Sc} {i j : I} {M : ℕ}

/-- **BE2 Proposition 11.2** (HW Theorem 5.9) in `K₀(Ḣ_{q,π})`: for `i ≠ j` and
`M = d_ij + 1`, the classes of the shifted projectives
`Π^{r(r-1)/2 |i| + r |i||j|} P(i^{(M-r)} j i^{(r)})` (`term a`, `a = M - r`) satisfy
`∑_{a ≤ M} (-1)^a [term a] = 0`. -/
theorem class_alternating_sum (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    ∑ a ∈ Finset.range (M + 1), ((-1 : ℤ) ^ a) • K₀.mk (term sy hc i j M a) = 0 := by
  obtain ⟨c, h0, hs, ht⟩ := exists_scalars (D := D) (Sc := Sc) hij hM
  exact (isSplitK sy hc hij hM c h0 hs ht).alternating_sum_eq_zero

/-- **BE2 Proposition 11.2**, "in particular", in `K₀(Ḣ_{q,π})`: the classes of the terms with
`a` even and with `a` odd have the same sum. -/
theorem class_even_eq_odd (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    ∑ a ∈ SplitComplex.terms M true, K₀.mk (term sy hc i j M a) =
      ∑ a ∈ SplitComplex.terms M false, K₀.mk (term sy hc i j M a) := by
  have h := class_alternating_sum sy hc hij hM
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (M + 1)) (fun a => Even a)] at h
  have e₁ : ∑ a ∈ (Finset.range (M + 1)).filter (fun a => Even a),
      ((-1 : ℤ) ^ a) • K₀.mk (term sy hc i j M a) =
      ∑ a ∈ SplitComplex.terms M true, K₀.mk (term sy hc i j M a) := by
    refine Finset.sum_congr (by ext a; simp [SplitComplex.terms]) fun a ha => ?_
    rw [(of_decide_eq_true (Finset.mem_filter.mp ha).2).neg_one_pow, one_smul]
  have e₂ : ∑ a ∈ (Finset.range (M + 1)).filter (fun a => ¬ Even a),
      ((-1 : ℤ) ^ a) • K₀.mk (term sy hc i j M a) =
      -∑ a ∈ SplitComplex.terms M false, K₀.mk (term sy hc i j M a) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr (by ext a; simp [SplitComplex.terms]) fun a ha => ?_
    rw [(Nat.not_even_iff_odd.mp (of_decide_eq_false (Finset.mem_filter.mp ha).2)).neg_one_pow,
      neg_one_smul]
  rw [e₁, e₂, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h

end Headline

end OddMath.QuiverHecke.SerreComplex
