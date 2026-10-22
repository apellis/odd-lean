/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SplitComplexShifted
import StringDiagrams.Super.SOpGraded

/-!
# Split complexes along contravariant superfunctors

The `K₀` step of Brundan–Ellis, arXiv:1701.04133v2, Lemma 11.6 (third identity), where the Serre
complex is carried to `𝔘̇_{q,π}(𝔤)` by `α' = ω ∘ α` (11.8), whose source is a super-opposite.

For a graded superfunctor `G : A ⥤ B^{sop}` and `S : ShiftedData k A M`, `S.opp G` is the
`ShiftedData` on `B` with objects `G (W a)`, idempotents `G (e a)`, maps up `G (d a)`, maps down
`(-1)^{par a + par (a+1)} G (u a)`, shifts `-sh a` and parities `par a`. The sign corrects the
super-opposite composition law `G(f) G(g) = (-1)^{|f||g|} G(g f)`, so that a splitting of `S`
gives one of `S.opp G` (`Split.opp`); hence
`∑_{a ≤ M} (-1)^a [Q^{-sh a} Π^{par a} (G (W a), G (e a))] = 0`.
-/

noncomputable section
namespace OddMath.QuiverHecke.SplitComplex
open CategoryTheory StringDiagrams GradedSupercategory Supercategory

variable {k : Type*} [CommRing k] {A : Type*} [Category A] [Preadditive A] [Linear k A]
  [Supercategory k A] [GradedSupercategory k A] {B : Type*} [Category B] [Preadditive B]
  [Linear k B] [Supercategory k B] [GradedSupercategory k B]
  (G : A ⥤ SOp k B) [G.Additive] [G.Linear k] [IsGradedSuperfunctor k G]

/-- The super-opposite composition law of `G`. -/
theorem unsop_map_comp {x y z : A} {f : x ⟶ y} {g : y ⟶ z} {p q : ZMod 2}
    (hf : f ∈ parity (R := k) x y p) (hg : g ∈ parity (R := k) y z q) :
    SOp.unsop (G.map g) ≫ SOp.unsop (G.map f) = sign k (p * q) • SOp.unsop (G.map (f ≫ g)) := by
  rw [G.map_comp, SOp.comp_of_mem (f := G.map f) (g := G.map g)
    (IsSuperfunctor.map_mem (R := k) (F := G) hf) (IsSuperfunctor.map_mem (R := k) (F := G) hg),
    smul_smul, sign_mul_self, one_smul]

theorem unsop_map_idem {x : A} {e : x ⟶ x} (he : e ≫ e = e) (hp : e ∈ parity (R := k) x x 0) :
    SOp.unsop (G.map e) ≫ SOp.unsop (G.map e) = SOp.unsop (G.map e) := by
  rw [unsop_map_comp G hp hp, he, mul_zero, sign_zero, one_smul]

private theorem zmod2_mul_self (p : ZMod 2) : p * p = p := by fin_cases p <;> rfl

private theorem sign_coef (p p' : ZMod 2) :
    sign k (p + p') * sign k ((p + p') * (p' + p)) = 1 := by
  rw [add_comm p' p, zmod2_mul_self, sign_mul_self]

private theorem sign_coef' (p p' : ZMod 2) :
    sign k (p + p') * sign k ((p' + p) * (p + p')) = 1 := by
  rw [mul_comm (p' + p), sign_coef]

namespace ShiftedData

variable {M : ℕ} (S : ShiftedData k A M)

/-- The image of `S` under the contravariant superfunctor `G`. -/
@[simps]
def opp : ShiftedData k B M where
  W a h := (G.obj (S.W a h)).unop
  e a h := SOp.unsop (G.map (S.e a h))
  u a h := SOp.unsop (G.map (S.d a h))
  d a h := sign k (S.par a + S.par (a + 1)) • SOp.unsop (G.map (S.u a h))
  sh a := -S.sh a
  par := S.par
  e_idem a h := unsop_map_idem G (S.e_idem a h) (S.e_even a h)
  e_degree a h := IsGradedSuperfunctor.map_mem_degree (R := k) (F := G) (S.e_degree a h)
  e_even a h := IsSuperfunctor.map_mem (R := k) (F := G) (S.e_even a h)
  u_degree a h := by
    rw [neg_sub_neg]
    exact IsGradedSuperfunctor.map_mem_degree (R := k) (F := G) (S.d_degree a h)
  u_parity a h := by
    rw [add_comm (S.par a)]
    exact IsSuperfunctor.map_mem (R := k) (F := G) (S.d_parity a h)
  d_degree a h := by
    rw [neg_sub_neg]
    exact Submodule.smul_mem _ _
      (IsGradedSuperfunctor.map_mem_degree (R := k) (F := G) (S.u_degree a h))
  d_parity a h := by
    rw [add_comm (S.par (a + 1))]
    exact Submodule.smul_mem _ _ (IsSuperfunctor.map_mem (R := k) (F := G) (S.u_parity a h))
  e_u a h := by
    rw [← Category.assoc, unsop_map_comp G (S.d_parity a h) (S.e_even a h.le), Linear.smul_comp,
      unsop_map_comp G (S.e_even (a + 1) h) (comp_mem (S.d_parity a h) (S.e_even a h.le)), S.e_d]
    simp only [mul_zero, zero_mul, sign_zero, one_smul]
  e_d a h := by
    rw [Linear.smul_comp, Linear.comp_smul]
    congr 1
    rw [← Category.assoc, unsop_map_comp G (S.u_parity a h) (S.e_even (a + 1) h), Linear.smul_comp,
      unsop_map_comp G (S.e_even a h.le) (comp_mem (S.u_parity a h) (S.e_even (a + 1) h)), S.e_u]
    simp only [mul_zero, zero_mul, sign_zero, one_smul]

end ShiftedData

namespace ShiftedData

variable {M : ℕ} {S : ShiftedData k A M}

theorem Split.opp (hS : S.Split) : (S.opp G).Split where
  pos := hS.pos
  uu a h := by
    simp only [opp_u]
    rw [unsop_map_comp G (S.d_parity (a + 1) h) (S.d_parity a (Nat.lt_of_succ_lt h)), hS.dd,
      G.map_zero, SOp.unsop_zero, smul_zero]
  dd a h := by
    simp only [opp_d]
    rw [Linear.smul_comp, Linear.comp_smul,
      unsop_map_comp G (S.u_parity a (Nat.lt_of_succ_lt h)) (S.u_parity (a + 1) h), hS.uu,
      G.map_zero, SOp.unsop_zero, smul_zero, smul_zero, smul_zero]
  split_zero := by
    simp only [opp_e, opp_u, opp_d]
    rw [Linear.comp_smul, unsop_map_comp G (S.u_parity 0 hS.pos) (S.d_parity 0 hS.pos), smul_smul,
      sign_coef, one_smul, ← hS.split_zero]
  split_succ a h := by
    simp only [opp_e, opp_u, opp_d]
    rw [Linear.comp_smul, unsop_map_comp G (S.u_parity (a + 1) h) (S.d_parity (a + 1) h),
      smul_smul, sign_coef, one_smul, Linear.smul_comp,
      unsop_map_comp G (S.d_parity a (Nat.lt_of_succ_lt h)) (S.u_parity a (Nat.lt_of_succ_lt h)),
      smul_smul, sign_coef', one_smul, ← SOp.unsop_add, ← G.map_add, ← hS.split_succ]
  split_top a h hat := by
    simp only [opp_e, opp_u, opp_d]
    rw [Linear.smul_comp, unsop_map_comp G (S.d_parity a h) (S.u_parity a h), smul_smul,
      sign_coef', one_smul, ← hS.split_top a h hat]

end ShiftedData

end OddMath.QuiverHecke.SplitComplex
