/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SerreDividedPowers
import OddMath.QuiverHecke.SplitComplexOpposite
import OddMath.SKM.ChevalleyWhiskering

/-!
# BE2 Lemma 11.6: the negative Serre relation with divided powers

Brundan–Ellis, arXiv:1701.04133v2, Lemma 11.6 (third identity). The proof applies
`α'_{n,λ} = ω ∘ α_{n,λ}` (11.8) to the split Serre complex of Proposition 11.2; here this is the
image of the complex of `SerreClassUp` under the Chevalley involution `ω` on hom categories
(`SKM.chevHom`), a graded superfunctor into the super-opposite.

* `class_alternating_sum_down`: the image complex is split (`SplitComplex.ShiftedData.opp`), so
  `∑_{a ≤ M} (-1)^a [Q^{-sh a} Π^{par a} (F_i^a F_j F_i^{M-a} 1_{-ν}, ω α(e_a))] = 0`.
* `ω` carries horizontal composites of even 2-morphisms to horizontal composites
  (`chevHom_hcomp_heq`), so each term is the product `[F_i^{(a)}][F_j][F_i^{(M-a)} 1_{-ν}]`
  (`class_termDown`), with `F_i^{(n)} = Q^{-d_i n(n-1)/2} (F_i^n, α'(1_{i^{(n)}}))`, the
  corrected divided power of Lemma 11.5 (no parity shift).
* `serre_F`: `∑_{r ≤ M} (-1)^r π_i^{r|j| + r(r-1)/2} [F_i^{(M-r)} F_j F_i^{(r)} 1_λ] = 0`,
  `M = d_ij + 1`, as printed, with `π_i^e` acting as `Π^{|i| e}`.
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : SKM.Datum I X} {k : Type w}
  [CommRing k] {Sc : SKM.Scalars D k} (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-! ### `ω` on horizontal composites -/

theorem heq_conj₂ {C : Type*} [Category C] {X X' Y Y' Z : C} (p : X = X') (q : Y' = Y)
    (f : X' ⟶ Z) (g : Z ⟶ Y') : HEq (eqToHom p ≫ f ≫ g ≫ eqToHom q) (f ≫ g) := by
  subst p q; simp

theorem chevHom_heq {a b : SKM.UGr D Sc sy hc} {f f' : a ⟶ b} (h : f = f') {x : f ⟶ f}
    {x' : f' ⟶ f'} (hx : HEq x x') :
    HEq (SOp.unsop ((SKM.chevHom a b).map x)) (SOp.unsop ((SKM.chevHom a b).map x')) := by
  subst h; obtain rfl := eq_of_heq hx; rfl

theorem hcomp_heq_left {a b c : SKM.UGr D Sc sy hc} {f f' : a ⟶ b} {g : b ⟶ c} (h : f = f')
    {x : f ⟶ f} {x' : f' ⟶ f'} (hx : HEq x x') (y : g ⟶ g) :
    HEq (TwoSupercategory.hcomp x y) (TwoSupercategory.hcomp x' y) := by
  subst h; obtain rfl := eq_of_heq hx; rfl

theorem chevHom_mem {a b : SKM.UGr D Sc sy hc} {f g : a ⟶ b} {x : f ⟶ g} {p : ZMod 2}
    (hx : x ∈ Supercategory.parity (R := k) f g p) :
    SOp.unsop ((SKM.chevHom a b).map x) ∈ Supercategory.parity (R := k) _ _ p :=
  SOp.mem_parity_iff.mp (Supercategory.IsSuperfunctor.map_mem (R := k) (F := SKM.chevHom a b) hx)

/-- **`ω` of a horizontal composite of even 2-morphisms** is the horizontal composite of their
images. -/
theorem chevHom_hcomp_heq {a b c : SKM.UGr D Sc sy hc} {f : a ⟶ b} {g : b ⟶ c} (x : f ⟶ f)
    (y : g ⟶ g) (hx : x ∈ Supercategory.parity (R := k) f f 0)
    (hy : y ∈ Supercategory.parity (R := k) g g 0) :
    HEq (SOp.unsop ((SKM.chevHom a c).map (TwoSupercategory.hcomp x y)))
      (TwoSupercategory.hcomp (SOp.unsop ((SKM.chevHom a b).map x))
        (SOp.unsop ((SKM.chevHom b c).map y))) := by
  have e := SplitComplex.unsop_map_comp (SKM.chevHom a c)
    (TwoSupercategory.whiskerRight_mem g hx) (TwoSupercategory.whiskerLeft_mem f hy)
  rw [mul_zero, Supercategory.sign_zero, one_smul] at e
  rw [TwoSupercategory.hcomp, TwoSupercategory.hcomp, ← e, SKM.chevHom_whiskerLeft,
    SKM.chevHom_whiskerRight, TwoSupercategory.whisker_exchange_of_even_left (R := k)
      (chevHom_mem sy hc hx)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact heq_conj₂ _ _ _ _

namespace SerreComplex

open SKM.K0Relations

variable {i j : I} {M : ℕ} (ν : X)

/-- The summand `Q^m Π^p (ω f, ω e)` of `𝔘̇_{q,π}(𝔤)`, for an even idempotent `e` of degree `0`
on a 1-morphism `f`. -/
abbrev chevSummand {a b : SKM.UGr D Sc sy hc} {f : a ⟶ b} {e : f ⟶ f} (he : e ≫ e = e)
    (hd : e ∈ GradedSupercategory.degree (R := k) f f 0)
    (hp : e ∈ Supercategory.parity (R := k) f f 0) (m : ℤ) (p : ZMod 2) :=
  SKM.Summands.raw (f := SKM.chevHomObj f) (SplitComplex.unsop_map_idem (SKM.chevHom a b) he hp)
    (GradedSupercategory.IsGradedSuperfunctor.map_mem_degree (R := k) (F := SKM.chevHom a b) hd)
    (chevHom_mem sy hc hp) m p

variable (i) in
/-- The class of `Q^m Π^p (F_i^n 1_{-ν}, α'(1_{i^{(n)}}))`, from `-ν` to `-μ`, in the split
Grothendieck ring of `𝔘̇_{q,π}(𝔤)` with BE2's multiplication order: the image under `ω` of the
summand `(E_i^n 1_ν, α(1_{i^{(n)}}))` of `Edp`. BE2's divided power `F_i^{(n)} 1_{-ν}` is
`m = p = 0`; the corrected one of Lemma 11.5 is `m = -d_i n(n-1)/2`, `p = 0`. -/
def Fdp (n : ℕ) (μ ν : X) (hs : SKM.wt D ν (upWord (List.replicate n i)) = μ) (m : ℤ)
    (p : ZMod 2) : Grothendieck Sc sy hc :=
  MulOpposite.op (K₀Ring.mk (B := SKM.UDot D Sc sy hc) (a := weight Sc sy hc (-μ))
    (b := weight Sc sy hc (-ν))
    (chevSummand sy hc (dpProj_idem sy hc n μ ν hs)
      (alpha_mem_degree D Sc sy ν (dpIdem_degree sy hc n))
      (alpha_mem_parity D Sc ν (dpIdem_even sy hc n)) m p))

theorem Fdp_congr {n n' : ℕ} {μ μ' ν ν' : X} {m m' : ℤ} {p p' : ZMod 2} (hn : n = n')
    (hμ : μ = μ') (hν : ν = ν') (hm : m = m') (hp : p = p')
    (hs : SKM.wt D ν (upWord (List.replicate n i)) = μ)
    (hs' : SKM.wt D ν' (upWord (List.replicate n' i)) = μ') :
    Fdp sy hc i n μ ν hs m p = Fdp sy hc i n' μ' ν' hs' m' p' := by
  subst hn hμ hν hm hp; rfl

variable (i j M) in
/-- `Q^n Π^p (F_i^a F_j F_i^{M-a} 1_{-ν}, ω α(e_a))`. -/
abbrev termDownShift (a : ℕ) (ha : a ≤ M) (n : ℤ) (p : ZMod 2) :=
  chevSummand sy hc (f := wordHom D Sc sy hc i j M ν a ha) (eIdem_up_idem ν a)
    (alpha_mem_degree D Sc sy ν (eIdem_degree sy hc a))
    (alpha_mem_parity D Sc ν (eIdem_even sy hc a)) n p

/-- **The Serre complex under `ω`**: for `i ≠ j`, `M = d_ij + 1` and any weight `ν`,
`∑_{a ≤ M} (-1)^a [Q^{-sh a} Π^{par a} (F_i^a F_j F_i^{M-a} 1_{-ν}, ω α(e_a))] = 0`. -/
theorem class_alternating_sum_down (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    ∑ a : Fin (M + 1), ((-1 : ℤ) ^ (a : ℕ)) •
      K₀.mk (termDownShift sy hc i j M ν a (Nat.le_of_lt_succ a.2) (-sh sy i M a)
        (par D i j M a)) = 0 := by
  obtain ⟨c, h0, hs, ht⟩ := exists_scalars (D := D) (Sc := Sc) hij hM
  exact ((split_up sy hc hij hM ν c (split sy hc hij hM c h0 hs ht)).opp
    (SKM.chevHom _ _)).alternating_sum_eq_zero

/-- **The terms of the image complex are products of divided powers**: with BE2's
multiplication order, `[Q^n Π^p (F_i^a F_j F_i^{M-a} 1_{-ν}, ω α(e_a))] =
[Q^{m_L} Π^{p_L} F_i^{(a)}] [F_j] [Q^{m_R} Π^{p_R} F_i^{(M-a)} 1_{-ν}]` whenever the shifts
add up. -/
theorem class_termDown {a : ℕ} (ha : a ≤ M) (n : ℤ) (p : ZMod 2) (mL mR : ℤ) (pL pR : ZMod 2)
    (hm : mL + 0 + mR = n) (hp : pL + 0 + pR = p) :
    (MulOpposite.op (K₀Ring.mk (B := SKM.UDot D Sc sy hc)
        (a := weight Sc sy hc (-((M • D.α i + D.α j) + ν))) (b := weight Sc sy hc (-ν))
        (termDownShift sy hc i j M ν a ha n p)) : Grothendieck Sc sy hc) =
      Fdp sy hc i a ((M • D.α i + D.α j) + ν) (wtL D ν i j M a) (wt_left ν ha) mL pL *
        Fdp sy hc j 1 (wtL D ν i j M a) (wtR D ν i M a) rfl 0 0 *
        Fdp sy hc i (M - a) (wtR D ν i M a) ν rfl mR pR := by
  rw [Fdp, Fdp, Fdp, ← MulOpposite.op_mul, ← MulOpposite.op_mul,
    SKM.Summands.mk_raw_mul_mk_raw, SKM.Summands.mk_raw_mul_mk_raw]
  congr 2
  rw [hm, hp]
  have hJ : dpProj sy hc j 1 (wtL D ν i j M a) (wtR D ν i M a) rfl = 𝟙 _ :=
    (alpha D Sc _).map_id _
  have hL : projL sy hc i j M ν a ha ∈ Supercategory.parity (R := k) _ _ 0 :=
    alpha_mem_parity D Sc (wtL D ν i j M a) (dpIdem_even sy hc (i := i) a)
  have hLM := TwoSupercategory.hcomp_mem (R := k) hL
    (Supercategory.id_mem (R := k) (midHom sy hc i j M ν a))
  rw [add_zero] at hLM
  refine raw_congr ((congrArg SKM.chevHomObj (wordHom_eq_comp sy hc ν ha)).trans
    (by rw [SKM.chevHomObj_comp, SKM.chevHomObj_comp]; rfl)) ?_ _ _ _ _ _ _ _ _
  refine (chevHom_heq sy hc (wordHom_eq_comp sy hc ν ha) (alpha_eIdem_heq sy hc ν ha)).trans ?_
  refine (chevHom_hcomp_heq sy hc _ _ hLM
    (alpha_mem_parity D Sc ν (dpIdem_even sy hc (i := i) (M - a)))).trans ?_
  refine hcomp_heq_left sy hc (SKM.chevHomObj_comp _ _) ?_ _
  refine (chevHom_hcomp_heq sy hc _ _ hL (Supercategory.id_mem (R := k) _)).trans ?_
  rw [hJ]
  rfl

/-! ### Lemma 11.6, negative Serre relation -/

section Serre

variable (hij : i ≠ j) (hM : M = D.dn i j + 1)
include hij hM

variable (D i j) in
omit hij hM in
/-- The parity shift `π_i^{r|j| + r(r-1)/2}` of the printed coefficient. -/
abbrev parF (r : ℕ) : ZMod 2 :=
  D.parity i * ((r : ZMod 2) * D.parity j + ((r.choose 2 : ℕ) : ZMod 2))

omit hij hM in
theorem term_eq_down {a r : ℕ} (h : a + r = M) (ha : a ≤ M) :
    Fdp sy hc i a ((M • D.α i + D.α j) + ν) (wtL D ν i j M a) (wt_left ν ha)
        (-(sy.d i * (a.choose 2 : ℕ))) 0 *
      Fdp sy hc j 1 (wtL D ν i j M a) (wtR D ν i M a) rfl 0 0 *
      Fdp sy hc i (M - a) (wtR D ν i M a) ν rfl (-(sy.d i * ((M - a).choose 2 : ℕ)))
        (parF D i j (M - a)) =
    Fdp sy hc i a (ν + (M • D.α i + D.α j)) (ν + r • D.α i + D.α j) (wt_left' ν h)
        (-(sy.d i * (a.choose 2 : ℕ))) 0 *
      Fdp sy hc j 1 (ν + r • D.α i + D.α j) (ν + r • D.α i) (wt_mid ν r) 0 0 *
      Fdp sy hc i r (ν + r • D.α i) ν (wt_rep ν r) (-(sy.d i * (r.choose 2 : ℕ)))
        (parF D i j r) := by
  have hr : M - a = r := by omega
  congr 1; congr 1
  · exact Fdp_congr sy hc rfl (add_comm _ _) (wtL_eq ν h) rfl rfl _ _
  · exact Fdp_congr sy hc rfl (wtL_eq ν h) (wtR_eq ν h) rfl rfl _ _
  · exact Fdp_congr sy hc hr (wtR_eq ν h) rfl (by rw [hr]) (by rw [hr]) _ _

/-- **BE2 Lemma 11.6, the negative Serre relation**, for `i ≠ j` and `M = d_ij + 1`: in the
split Grothendieck ring of `𝔘̇_{q,π}(𝔤)`,
`∑_{r=0}^{M} (-1)^r π_i^{r|j| + r(r-1)/2} [F_i^{(M-r)} F_j F_i^{(r)} 1_λ] = 0`, at `λ = -ν`
(the 1-morphisms run from `-ν` to `-ν - M α_i - α_j`).

The divided powers are those of Lemma 11.5 in its corrected form,
`F_i^{(n)} = Q^{-d_i n(n-1)/2} (F_i^n, α'(1_{i^{(n)}}))` (`Fdp`, see `class_corrected_down`).
The coefficient `π_i^e` acts on classes as the parity shift `Π^{|i| e}`, placed on the right
factor (`parF`). -/
theorem serre_F :
    ∑ r : Fin (M + 1), ((-1 : ℤ) ^ (r : ℕ)) •
      (Fdp sy hc i (M - r) (ν + (M • D.α i + D.α j)) (ν + (r : ℕ) • D.α i + D.α j)
          (wt_left' ν (Nat.sub_add_cancel (Nat.le_of_lt_succ r.2)))
          (-(sy.d i * ((M - r).choose 2 : ℕ))) 0 *
        Fdp sy hc j 1 (ν + (r : ℕ) • D.α i + D.α j) (ν + (r : ℕ) • D.α i) (wt_mid ν r) 0 0 *
        Fdp sy hc i r (ν + (r : ℕ) • D.α i) ν (wt_rep ν r) (-(sy.d i * ((r : ℕ).choose 2 : ℕ)))
          (parF D i j r)) = 0 := by
  have h := class_alternating_sum_down sy hc ν hij hM
  have h2 := congrArg (fun x => (MulOpposite.op (K₀Ring.of
    (weight Sc sy hc (-((M • D.α i + D.α j) + ν))) (weight Sc sy hc (-ν)) x) :
      Grothendieck Sc sy hc)) h
  simp only [map_sum, map_zsmul, Finset.op_sum, MulOpposite.op_smul, map_zero,
    MulOpposite.op_zero] at h2
  have h3 : ∑ a : Fin (M + 1), ((-1 : ℤ) ^ (a : ℕ)) •
      (Fdp sy hc i a ((M • D.α i + D.α j) + ν) (wtL D ν i j M a)
          (wt_left ν (Nat.le_of_lt_succ a.2)) (-(sy.d i * ((a : ℕ).choose 2 : ℕ))) 0 *
        Fdp sy hc j 1 (wtL D ν i j M a) (wtR D ν i M a) rfl 0 0 *
        Fdp sy hc i (M - a) (wtR D ν i M a) ν rfl (-(sy.d i * ((M - a).choose 2 : ℕ)))
          (parF D i j (M - a))) = 0 := by
    rw [← h2]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    refine (class_termDown sy hc ν (Nat.le_of_lt_succ a.2) _ _ _ _ _ _ ?_ ?_).symm
    · rw [sh]; ring
    · rw [par]; ring
  rw [← Equiv.sum_comp Fin.revPerm] at h3
  have h4 : ∀ r : Fin (M + 1), ((Fin.revPerm r : Fin (M + 1)) : ℕ) + r = M := fun r => by
    simp only [Fin.revPerm_apply, Fin.val_rev]; omega
  calc _ = ∑ r : Fin (M + 1), ((-1 : ℤ) ^ M) • ((-1 : ℤ) ^ ((Fin.revPerm r : Fin (M + 1)) : ℕ) •
      (Fdp sy hc i (Fin.revPerm r) ((M • D.α i + D.α j) + ν) (wtL D ν i j M (Fin.revPerm r))
          (wt_left ν (Nat.le_of_lt_succ (Fin.revPerm r).2))
          (-(sy.d i * (((Fin.revPerm r : Fin (M + 1)) : ℕ).choose 2 : ℕ))) 0 *
        Fdp sy hc j 1 (wtL D ν i j M (Fin.revPerm r)) (wtR D ν i M (Fin.revPerm r)) rfl 0 0 *
        Fdp sy hc i (M - (Fin.revPerm r : Fin (M + 1))) (wtR D ν i M (Fin.revPerm r)) ν rfl
          (-(sy.d i * ((M - (Fin.revPerm r : Fin (M + 1))).choose 2 : ℕ)))
          (parF D i j (M - (Fin.revPerm r : Fin (M + 1)))))) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        have hr := h4 r
        have hs : ((-1 : ℤ) ^ (r : ℕ)) =
            (-1) ^ M * (-1) ^ ((Fin.revPerm r : Fin (M + 1)) : ℕ) := by
          rw [neg_one_pow_eq (by omega : (r : ℕ) ≤ M),
            show M - (r : ℕ) = ((Fin.revPerm r : Fin (M + 1)) : ℕ) by omega]
        rw [smul_smul, ← hs, term_eq_down sy hc ν hr (by omega)]
        have hn : M - (r : ℕ) = ((Fin.revPerm r : Fin (M + 1)) : ℕ) := by omega
        congr 3
        exact Fdp_congr sy hc hn rfl rfl (by rw [hn]) rfl _ _
    _ = 0 := by rw [← Finset.smul_sum, h3, smul_zero]

end Serre

end SerreComplex

end OddMath.QuiverHecke
