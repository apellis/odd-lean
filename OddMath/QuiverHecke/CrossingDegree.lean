/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HomDimension
import Categorification.KLR.GradedBasis
import OddMath.QuiverHecke.CentreFinite

/-!
# Degrees of normal forms of the quiver Hecke supercategory

The normal form `x^l ψ_w : t → t'` of `H` (Brundan–Ellis, arXiv:1701.04133v2, §11;
`OddMath.QuiverHecke.Basis`) uses the canonical reduced word of `w`. For any reduced word `ρ` of
`w`, the crossings of `ρ` take the word `t` to `t ∘ w⁻¹`, and the crossings that occur are exactly
the inversions of `w` (`tgt_cw_and_sum_pl_cw`), as in Khovanov–Lauda, arXiv:0803.4121v2, §2.4.
Hence the degree and parity of `x^l ψ_w` are those of its dots plus the sums over the inversions
of `w` (`NFIdx.deg_eq_sum_invSet`, `NFIdx.par_eq_sum_invSet`), and the normal forms of degree
`z` are indexed by the permutations `w` with `t' = t ∘ w⁻¹` together with the dot counts on the
strands completing `deg(ψ_w)` to `z` (`sum_fiber_nf`).
-/

noncomputable section

namespace OddMath.QuiverHecke

open Categorification.TypeA

universe u

variable {I : Type u}

theorem drop_eq_cons_cons {α : Type*} (l : List α) {j : ℕ} (hj : j + 1 < l.length) :
    l.drop j = l[j] :: l[j + 1] :: l.drop (j + 2) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons hj]

/-- A crossing at strands `j, j + 1` permutes the word by `s_j`. -/
theorem act_cross_ofFn {n : ℕ} (g : Fin n → I) {j : ℕ} (hj : j + 1 < n) :
    (PG.cross j).act (List.ofFn g) = List.ofFn (g ∘ sadj n j) := by
  have hl : j + 1 < (List.ofFn g).length := by simpa using hj
  simp only [PG.act, drop_eq_cons_cons _ hl]
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.length_ofFn] at h₂
  simp only [List.getElem_ofFn, Function.comp_apply]
  have hs := sadj_val_of_lt hj ⟨i, h₂⟩
  rcases swapNat_cases j i with ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨h1, h2, e⟩
  · rw [e] at hs
    rw [List.getElem_append_right (by simp)]
    simp only [List.length_take, List.length_ofFn, show i - min i n = 0 by omega,
      List.getElem_cons_zero]
    congr 1
    exact Fin.ext hs.symm
  · rw [e] at hs
    rw [List.getElem_append_right (by simp)]
    simp only [List.length_take, List.length_ofFn, show j + 1 - min j n = 0 + 1 by omega,
      List.getElem_cons_succ, List.getElem_cons_zero]
    congr 1
    exact Fin.ext hs.symm
  · rw [e] at hs
    have : sadj n j ⟨i, h₂⟩ = ⟨i, h₂⟩ := Fin.ext hs
    rw [this]
    rcases lt_or_gt_of_ne h1 with hi | hi
    · rw [List.getElem_append_left (by simp; omega)]
      simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_take, List.length_ofFn, show i - min j n = (i - j - 2) + 1 + 1 by omega,
        List.getElem_cons_succ, List.getElem_drop, List.getElem_ofFn]
      congr 2
      omega

theorem sum_ld_cross_ofFn {M : Type*} [AddCommMonoid M] (f : Shape I → M) {n : ℕ}
    (g : Fin n → I) {j : ℕ} (hj : j + 1 < n) :
    (((PG.cross j).ld (List.ofFn g)).map fun x => f x.2.1).sum =
      f (.cross (g ⟨j, by omega⟩) (g ⟨j + 1, hj⟩)) := by
  have hl : j + 1 < (List.ofFn g).length := by simpa using hj
  simp [PG.ld, drop_eq_cons_cons _ hl]

/-- **The crossings of a reduced word are the inversions of its permutation**: for a reduced
word `ρ` with permutation `w`, the crossings `cw ρ` take `t` to `t ∘ w⁻¹`, and summing any
function of the generators over them gives the sum over the inversions `a < b`, `w b < w a`
of its value on the crossing of `t_a` and `t_b`. -/
theorem tgt_cw_and_sum_pl_cw {M : Type*} [AddCommMonoid M] (f : Shape I → M) (t : List I)
    {ρ : List ℕ} (hρ : IsReduced t.length ρ) :
    tgt t (cw ρ) = List.ofFn (fun i => t.get ((wordProd t.length ρ)⁻¹ i)) ∧
      ((pl t (cw ρ)).map fun x => f x.2.1).sum =
        ∑ p ∈ invSet t.length (wordProd t.length ρ), f (.cross (t.get p.1) (t.get p.2)) := by
  induction ρ with
  | nil =>
    have : invSet t.length 1 = ∅ := Finset.card_eq_zero.1 (invCount_one t.length)
    simp [cw, this, wordProd]
  | cons j ρ ih =>
    obtain ⟨hρ', hj, hlt⟩ := hρ.tail_and_lt
    obtain ⟨ih1, ih2⟩ := ih hρ'
    have hcw : cw (j :: ρ) = cw ρ ++ [PG.cross j] := by simp [cw]
    rw [hcw, tgt_append, pl_append, ih1, wordProd_cons, invSet_sadj_mul_eq_insert hj hlt,
      Finset.sum_insert (fun h => by
        have := (mem_invSet.1 h).2
        simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at this
        exact absurd this (by simp [Fin.lt_def]))]
    refine ⟨?_, ?_⟩
    · rw [tgt_cons, tgt_nil, act_cross_ofFn _ hj]
      congr 1
      funext i
      simp [mul_inv_rev]
    · rw [List.map_append, List.sum_append, ih2, pl_cons, pl_nil, List.append_nil,
        sum_ld_cross_ofFn _ _ hj, add_comm]

/-- Summing a function of the generators over dots on the strands of `l`. -/
theorem sum_pl_dots {M : Type*} [AddCommMonoid M] (f : Shape I → M) (t : List I) (l : List ℕ)
    (hl : ∀ x ∈ l, x < t.length) :
    ((pl t (l.map PG.dot)).map fun x => f x.2.1).sum =
      ∑ r : Fin t.length, l.count (r : ℕ) • f (.dot (t.get r)) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp : p < t.length := hl p (by simp)
    rw [List.map_cons, pl_cons, show (PG.dot p).act t = t from rfl, List.map_append,
      List.sum_append, ih fun x hx => hl x (by simp [hx])]
    have hld : (PG.dot p).ld t = [(t.take p, Shape.dot t[p], t.drop (p + 1))] := by
      have h := List.drop_eq_getElem_cons hp
      simp only [PG.ld, h]
    rw [hld]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.count_cons, add_smul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    rw [Finset.sum_eq_single ⟨p, hp⟩ (fun r _ hr => by
      have : (p == (r : ℕ)) = false := by
        simpa using fun h : p = r => hr (Fin.ext h.symm)
      rw [this]; simp) (by simp)]
    simp

variable {X : Type*} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)

/-- The crossings of a normal form `x^l ψ_w : t → t'` take `t` to `t ∘ w⁻¹`. -/
theorem NFIdx.tgt_eq_ofFn {t t' : List I} (i : NFIdx t t') :
    t' = List.ofFn (fun a => t.get (i.1.2⁻¹ a)) := by
  have h := (tgt_cw_and_sum_pl_cw (fun _ => (0 : ℕ)) t (isReduced_canWord t.length i.1.2)).1
  rw [wordProd_canWord, NFIdx.tgt_cw] at h
  exact h

/-- **The degree of a normal form** `x^l ψ_w`: its dots, plus `deg(ψ_w)`, the sum of the
crossing degrees over the inversions of `w`. -/
theorem NFIdx.deg_eq_sum_invSet {t t' : List I} (i : NFIdx t t') :
    i.deg D sy = gsum D sy (pl t (i.1.1.map PG.dot)) +
      ∑ p ∈ invSet t.length i.1.2, gdeg D sy (.cross (t.get p.1) (t.get p.2)) := by
  rw [NFIdx.deg_eq]
  have h := (tgt_cw_and_sum_pl_cw (gdeg D sy) t (isReduced_canWord t.length i.1.2)).2
  rw [wordProd_canWord] at h
  rw [← h]

/-- **The parity of a normal form** `x^l ψ_w`: its dots, plus the parities of the crossings
over the inversions of `w`. -/
theorem NFIdx.par_eq_sum_invSet {t t' : List I} (i : NFIdx t t') :
    i.par D = ((pl t (i.1.1.map PG.dot)).map fun x => x.2.1.parity D).sum +
      ∑ p ∈ invSet t.length i.1.2, (Shape.cross (t.get p.1) (t.get p.2)).parity D := by
  have h := (tgt_cw_and_sum_pl_cw (fun s : Shape I => s.parity D) t
    (isReduced_canWord t.length i.1.2)).2
  rw [wordProd_canWord] at h
  rw [NFIdx.par, NFIdx.gens, pl_append, tgt_map_dot, List.map_append, List.sum_append, h]

theorem pairwise_dotList (n : ℕ) (m : ℕ → ℕ) : (dotList n m).Pairwise (· ≤ ·) := by
  rw [dotList, List.pairwise_flatMap]
  refine ⟨fun a _ => List.pairwise_replicate_of_refl, ?_⟩
  refine List.Pairwise.imp (fun {a b} (h : a < b) x hx y hy => ?_) List.pairwise_lt_range
  rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
  exact h.le

theorem mem_dotList_lt {n : ℕ} {m : ℕ → ℕ} {x : ℕ} (hx : x ∈ dotList n m) : x < n := by
  rw [dotList, List.mem_flatMap] at hx
  obtain ⟨a, ha, hx⟩ := hx
  rw [List.eq_of_mem_replicate hx]
  exact List.mem_range.1 ha

/-- An increasing list is determined by its counts. -/
theorem eq_dotList_of_pairwise {n : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < n)
    (hs : l.Pairwise (· ≤ ·)) : l = dotList n fun p => l.count p :=
  List.Perm.eq_of_pairwise' hs (pairwise_dotList _ _) (perm_dotList hl)

/-- The crossing degree `deg(ψ_w)` on the word `t`. -/
def crossDeg (t : List I) (w : Equiv.Perm (Fin t.length)) : ℤ :=
  ∑ p ∈ invSet t.length w, gdeg D sy (.cross (t.get p.1) (t.get p.2))

/-- The crossing parity of `ψ_w` on the word `t`. -/
def crossPar (t : List I) (w : Equiv.Perm (Fin t.length)) : ZMod 2 :=
  ∑ p ∈ invSet t.length w, (Shape.cross (t.get p.1) (t.get p.2)).parity D

/-- The degree of `c_r` dots on the strands `r` of `t`. -/
def dotDeg (t : List I) (c : Fin t.length → ℕ) : ℤ :=
  ∑ r, c r • gdeg D sy (.dot (t.get r))

/-- The parity of `c_r` dots on the strands `r` of `t`. -/
def dotPar (t : List I) (c : Fin t.length → ℕ) : ZMod 2 :=
  ∑ r, c r • (Shape.dot (t.get r)).parity D

theorem finite_dotDeg_eq (t : List I) (z : ℤ) :
    {c : Fin t.length → ℕ | dotDeg D sy t c = z}.Finite := by
  refine (Set.finite_Iic (fun _ : Fin t.length => z.toNat)).subset fun c hc => ?_
  change dotDeg D sy t c = z at hc
  intro r
  have hpos : ∀ r, (0 : ℤ) ≤ c r • gdeg D sy (.dot (t.get r)) := fun r => by
    have := sy.pos (t.get r)
    simp only [gdeg, nsmul_eq_mul]
    positivity
  have hle : c r • gdeg D sy (.dot (t.get r)) ≤ z := by
    rw [← hc, dotDeg]
    exact Finset.single_le_sum (fun r _ => hpos r) (Finset.mem_univ r)
  have := sy.pos (t.get r)
  simp only [gdeg, nsmul_eq_mul] at hle
  change c r ≤ z.toNat
  have : (c r : ℤ) ≤ c r * (2 * sy.d (t.get r)) := by nlinarith
  omega

/-- **Graded superdimension of `Hom_H(t, t')` in degree `z`**, as a sum over permutations `w`
with `t' = t ∘ w⁻¹` of the dot configurations completing `ψ_w` to degree `z`: the normal forms
`x^l ψ_w` are indexed by `w` and the dot counts on the strands. -/
theorem sum_fiber_nf [DecidableEq I] {k : Type*} [CommRing k] (π : k) (t t' : List I) (z : ℤ) :
    ∑ i ∈ (finite_deg_eq D sy t t' z).toFinset, π ^ (i.par D).val =
      ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin t.length) =>
          t' = List.ofFn fun a => t.get (w⁻¹ a)),
        ∑ c ∈ (finite_dotDeg_eq D sy t (z - crossDeg D sy t w)).toFinset,
          π ^ (crossPar D t w + dotPar D t c).val := by
  classical
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun i _ => ⟨i.1.2, fun r => i.1.1.count (r : ℕ)⟩) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Set.Finite.mem_toFinset] at hi
    change i.deg D sy = z at hi
    rw [Finset.mem_sigma, Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨Finset.mem_univ _, i.tgt_eq_ofFn⟩, ?_⟩
    change dotDeg D sy t _ = _
    rw [← hi, NFIdx.deg_eq_sum_invSet, gsum, sum_pl_dots _ t _ i.2.2.1]
    simp [dotDeg, crossDeg]
  · intro i _ j _ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨hw, hc⟩ := h
    have hc' : ∀ p, i.1.1.count p = j.1.1.count p := by
      intro p
      by_cases hp : p < t.length
      · exact congrFun (eq_of_heq hc) ⟨p, hp⟩
      · rw [List.count_eq_zero_of_not_mem (fun h => hp (i.2.2.1 p h)),
          List.count_eq_zero_of_not_mem (fun h => hp (j.2.2.1 p h))]
    apply Subtype.ext
    apply Prod.ext _ hw
    rw [eq_dotList_of_pairwise i.2.2.1 i.2.1, eq_dotList_of_pairwise j.2.2.1 j.2.1]
    simp only [hc']
  · intro ⟨w, c⟩ hwc
    rw [Finset.mem_sigma, Finset.mem_filter, Set.Finite.mem_toFinset] at hwc
    obtain ⟨⟨-, hw⟩, hc⟩ := hwc
    change dotDeg D sy t c = _ at hc
    let m : ℕ → ℕ := fun p => if h : p < t.length then c ⟨p, h⟩ else 0
    have hl : ∀ x ∈ dotList t.length m, x < t.length := fun x hx => mem_dotList_lt hx
    have hchain : SChain t (pl t ((dotList t.length m).map PG.dot ++
        cw (canWord t.length w))) t' := by
      have := sChain_pl t ((dotList t.length m).map PG.dot ++ cw (canWord t.length w))
      rwa [tgt_append, tgt_map_dot,
        (tgt_cw_and_sum_pl_cw (fun _ => (0 : ℕ)) t (isReduced_canWord t.length w)).1,
        wordProd_canWord, ← hw] at this
    have hcount : (fun r : Fin t.length => (dotList t.length m).count (r : ℕ)) = c := by
      funext r
      rw [count_dotList]
      simp [m]
    let i : NFIdx t t' := ⟨(dotList t.length m, w), pairwise_dotList _ _, hl, hchain⟩
    refine ⟨i, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      change i.deg D sy = z
      rw [NFIdx.deg_eq_sum_invSet, gsum, sum_pl_dots _ t _ hl]
      change dotDeg D sy t (fun r => (dotList t.length m).count (r : ℕ)) +
        crossDeg D sy t w = z
      rw [hcount, hc]
      ring
    · change (⟨w, fun r => (dotList t.length m).count (r : ℕ)⟩ :
        (_ : Equiv.Perm (Fin t.length)) × (Fin t.length → ℕ)) = ⟨w, c⟩
      rw [hcount]
  · intro i _
    congr 2
    rw [NFIdx.par_eq_sum_invSet, sum_pl_dots _ t _ i.2.2.1, add_comm]
    rfl

end OddMath.QuiverHecke
