/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SerreClass
import OddMath.QuiverHecke.CategoricalDividedPowers

/-!
# The Serre complex in `𝔘̇_{q,π}(𝔤)`

Brundan–Ellis, arXiv:1701.04133v2, proof of Lemma 11.6 (second identity): the split complex of
Proposition 11.2 (`OddMath.QuiverHecke.SerreClass`), written with the idempotents `e_a`, is
carried by the homomorphism `α_{M+1,ν}` of (11.7) (`OddMath.QuiverHecke.alpha`, weight labelling
with rightmost weight `ν`) to a split complex of summands of the 1-morphisms
`E_i^a E_j E_i^{M-a} 1_ν` of `𝔘̇_{q,π}(𝔤)`. All of them run from `ν` to the same weight
`ν + M α_i + α_j` (`wt_word`), so they lie in one hom category `UHom D Sc sy hc μ ν`.

* `termUp a = Q^{sh a} Π^{par a} (E_i^a E_j E_i^{M-a} 1_ν, α(e_a))`, with the shifts of
  `SerreClass.term`;
* `class_alternating_sum_up`: `∑_{a ≤ M} (-1)^a [termUp a] = 0` in the split Grothendieck group of
  the hom category.

Identifying `termUp a` with the composite `E_i^{(a)} E_j E_i^{(M-a)} 1_ν` of divided powers, which
gives Lemma 11.6 as printed, is not done here.
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke.SerreComplex
open CategoryTheory StringDiagrams OddMath.QuiverHecke GradedSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : SKM.Datum I X} {k : Type w}
  [CommRing k] {Sc : SKM.Scalars D k} (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-! ### The weights -/

theorem wt_eq_sum (μ : X) (t : List (SKM.Letter I)) :
    SKM.wt D μ t = (t.map (SKM.sh D)).sum + μ := by
  induction t with
  | nil => simp
  | cons l t ih => rw [SKM.wt_cons, ih, List.map_cons, List.sum_cons, add_assoc]

variable {i j : I} {M : ℕ}

theorem wt_word (ν : X) {a : ℕ} (ha : a ≤ M) :
    SKM.wt D ν (upWord (word i j M a)) = (M • D.α i + D.α j) + ν := by
  rw [wt_eq_sum]
  congr 1
  obtain ⟨n, rfl⟩ : ∃ n, M = a + n := ⟨M - a, by omega⟩
  simp only [word, upWord, List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, show a + n - a = n by omega, add_smul]
  simp [SKM.up, SKM.sh]
  abel

/-! ### The words as 1-morphisms of `𝔘(𝔤)` -/

variable (D Sc)

/-- The hom category of `𝔘(𝔤)` from `ν` to `μ` (1-morphisms run from the left weight `μ` to the
right weight `ν`). -/
abbrev UHom (μ ν : X) :=
  (show SKM.UGr D Sc sy hc from ⟨μ⟩) ⟶ (show SKM.UGr D Sc sy hc from ⟨ν⟩)

variable (i j M) in
/-- The 1-morphism `E_i^a E_j E_i^{M-a} 1_ν`. -/
def wordHom (ν : X) (a : ℕ) (ha : a ≤ M) : UHom D Sc sy hc ((M • D.α i + D.α j) + ν) ν :=
  ⟨SKM.ob D ν (upWord (word i j M a)), wt_word ν ha, SKM.ok_wd D ν _, SKM.ob_endR D ν _⟩

variable {D Sc} (hij : i ≠ j) (hM : M = D.dn i j + 1) (ν : X)
include hij hM

/-- The Serre complex carried to `𝔘(𝔤)` by `α_{M+1,ν}`. -/
def dataUp (c : ℕ → k) :
    SplitComplex.ShiftedData k (UHom D Sc sy hc ((M • D.α i + D.α j) + ν) ν) M where
  W := wordHom D Sc sy hc i j M ν
  e a _ := (alpha D Sc ν).map (eIdem D Sc i j M a)
  u a h := (alpha D Sc ν).map (c a • upMap D Sc i j M h)
  d a h := (alpha D Sc ν).map (downMap D Sc i j M h)
  sh := sh sy i M
  par := par D i j M
  e_idem a _ := by
    change (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _ = _
    rw [← Functor.map_comp]
    exact congrArg _ (eIdem_idem_all a)
  e_degree a _ := alpha_mem_degree D Sc sy ν (eIdem_degree sy hc a)
  e_even a _ := alpha_mem_parity D Sc ν (eIdem_even sy hc a)
  u_degree _ h := alpha_mem_degree D Sc sy ν
    (Submodule.smul_mem _ _ (upMap_degree sy hc hij hM h))
  u_parity _ h := alpha_mem_parity D Sc ν
    (Submodule.smul_mem _ _ (upMap_parity sy hc hij hM h))
  d_degree a h := alpha_mem_degree D Sc sy ν (a := ob D (word i j M (a + 1)))
    (b := ob D (word i j M a)) (downMap_degree sy hc hij hM h)
  d_parity a h := alpha_mem_parity D Sc ν (a := ob D (word i j M (a + 1)))
    (b := ob D (word i j M a)) (downMap_parity sy hc h)
  e_u a h := by
    change (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _ = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ ((data sy hc hij hM c).e_u a h)
  e_d a h := by
    change (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _ = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ ((data sy hc hij hM c).e_d a h)

theorem split_up (c : ℕ → k) (hS : (data sy hc hij hM c).Split) :
    (dataUp sy hc hij hM ν c).Split where
  pos := hS.pos
  uu a h := by
    change (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _ = 0
    rw [← Functor.map_comp]
    exact ((congrArg _ (hS.uu a h)).trans (Functor.map_zero _ _ _))
  dd a h := by
    change (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _ = 0
    rw [← Functor.map_comp]
    exact ((congrArg _ (hS.dd a h)).trans (Functor.map_zero _ _ _))
  split_zero := by
    change (alpha D Sc ν).map _ = (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _
    rw [← Functor.map_comp]
    exact congrArg _ hS.split_zero
  split_succ a h := by
    change (alpha D Sc ν).map _ = (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _ +
      (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add]
    exact congrArg _ (hS.split_succ a h)
  split_top a h hat := by
    change (alpha D Sc ν).map _ = (alpha D Sc ν).map _ ≫ (alpha D Sc ν).map _
    rw [← Functor.map_comp]
    exact congrArg _ (hS.split_top a h hat)

omit hij hM in
theorem eIdem_up_idem (a : ℕ) :
    ((alpha D Sc ν).map (eIdem D Sc i j M a) : (alpha D Sc ν).obj _ ⟶ _) ≫
      (alpha D Sc ν).map (eIdem D Sc i j M a) = (alpha D Sc ν).map (eIdem D Sc i j M a) := by
  rw [← Functor.map_comp]
  exact congrArg _ (eIdem_idem_all a)

variable (i j M) in
omit hij hM in
/-- **The terms in `𝔘̇_{q,π}(𝔤)`**: `Q^{sh a} Π^{par a} (E_i^a E_j E_i^{M-a} 1_ν, α(e_a))`. -/
def termUp (a : ℕ) (ha : a ≤ M) :
    CategoryTheory.Idempotents.Karoubi
      (Mat_ (SKM.Summands.Base k (UHom D Sc sy hc ((M • D.α i + D.α j) + ν) ν))) :=
  SKM.Summands.raw (f := wordHom D Sc sy hc i j M ν a ha) (eIdem_up_idem ν a)
    (alpha_mem_degree D Sc sy ν (eIdem_degree sy hc a))
    (alpha_mem_parity D Sc ν (eIdem_even sy hc a)) (sh sy i M a) (par D i j M a)

/-- **BE2 Lemma 11.6, the Serre complex in `𝔘̇_{q,π}(𝔤)`**: for `i ≠ j`, `M = d_ij + 1` and any
weight `ν`, `∑_{a ≤ M} (-1)^a [termUp a] = 0` in the split Grothendieck group of the hom category
from `ν` to `ν + M α_i + α_j`. -/
theorem class_alternating_sum_up :
    ∑ a : Fin (M + 1), ((-1 : ℤ) ^ (a : ℕ)) •
      K₀.mk (termUp sy hc i j M ν a (Nat.le_of_lt_succ a.2)) = 0 := by
  obtain ⟨c, h0, hs, ht⟩ := exists_scalars (D := D) (Sc := Sc) hij hM
  exact (split_up sy hc hij hM ν c (split sy hc hij hM c h0 hs ht)).alternating_sum_eq_zero

end OddMath.QuiverHecke.SerreComplex
