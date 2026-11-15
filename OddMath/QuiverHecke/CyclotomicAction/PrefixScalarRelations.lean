import OddMath.SKM.ELVScalarParity
import StringDiagrams.Super.BoxProductMonoidal
import OddMath.QuiverHecke.CyclotomicAction.LastStrand
import OddMath.QuiverHecke.CyclotomicAction.SignedIntertwiner
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerChains
import OddMath.QuiverHecke.CyclotomicAction.PrependCoordinates
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRight
import OddMath.QuiverHecke.CyclotomicAction.CoefficientTransport

/-!
# Prefix scalar relations

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Ordinary specialization of the signed ELV coefficient category

The coefficient evaluation of `InvertibleDotProbe.md` §1 is a superfunctor:
odd homogeneous coefficients vanish, so the target coefficient category is
BoxUnit. Applying the existing box-product map and left unitor constructs the
literal specialization a tensor f ↦ eval(a) • f, preserving signed composition.
No old-strand cyclotomic relation is killed by this module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.SKM.SYM
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (values : I × ℕ → k)
  (hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0)

def elvCoefficientScalarFunctor :
    Superfunctor k (SuperalgebraCat (elvCoefficientParity (k := k) D cutoff))
      (BoxUnit.{u,u} k) :=
  Superfunctor.ofLinearMaps (fun _ => BoxUnit.star)
    (fun _ _ => (elvScalarEvaluation D cutoff values hvalues).toLinearMap)
    (fun _ => by
      change elvScalarEvaluation D cutoff values hvalues 1 = 1
      exact map_one _)
    (fun f g => by
      change elvScalarEvaluation D cutoff values hvalues
          (SuperalgebraCat.toElem g * SuperalgebraCat.toElem f) =
        elvScalarEvaluation D cutoff values hvalues (SuperalgebraCat.toElem g) *
          elvScalarEvaluation D cutoff values hvalues (SuperalgebraCat.toElem f)
      exact map_mul _ _ _)
    (by
      intro A B p f hf
      rcases parity_eq_zero_or_one p with rfl | rfl
      · exact BoxUnit.mem_parity_zero _
      · change elvScalarEvaluation D cutoff values hvalues
          (SuperalgebraCat.toElem f) ∈ trivialGrading k 1
        rw [trivialGrading_one, Submodule.mem_bot]
        exact elvScalarEvaluation_odd_zero D cutoff values hvalues
          ((SuperalgebraCat.mem_parity_iff (elvCoefficientParity D cutoff)).mp hf))

/-- Actual scalar specialization of the signed coefficient category, built
from existing superfunctorial tensor and unitor comparisons. -/
def elvAffineScalarSpecialization :
    Superfunctor k (ELVCoefficientCategory D Sc cutoff) (H D Sc) :=
  (BoxProd.map (elvCoefficientScalarFunctor D cutoff values hvalues)
    (Superfunctor.id k (H D Sc))).comp (BoxProd.lunit (H D Sc))

theorem elvAffineScalarSpecialization_tmul
    {A B : ELVCoefficientCategory D Sc cutoff}
    (c : A.fst ⟶ B.fst) (f : A.snd ⟶ B.snd) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map (BoxProd.tmulHom c f) =
      elvScalarEvaluation D cutoff values hvalues (SuperalgebraCat.toElem c) • f := by
  change (BoxProd.lunit (H D Sc)).map
    ((BoxProd.map (elvCoefficientScalarFunctor D cutoff values hvalues)
      (Superfunctor.id k (H D Sc))).map (BoxProd.tmulHom c f)) = _
  rw [BoxProd.map_tmulHom, BoxProd.lunit_map_tmulHom]
  rfl

/-- Full source coefficient insertion specializes by the chosen scalar
evaluation, with the affine diagram left unchanged. -/
theorem elvAffineScalarSpecialization_source {s t : List I}
    (c : SKM.SYM D k) (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (sourceCoefficientHom D Sc c f)) =
        scalarEvaluation D values c • f := by
  rw [elvQuotientMap_source]
  change (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
    (BoxProd.tmulHom
      (X := elvQuotientObj D Sc cutoff (coefficientObj D Sc s))
      (Y := elvQuotientObj D Sc cutoff (coefficientObj D Sc t))
      (SuperalgebraCat.ofElem (elvCoefficientQuotient D cutoff c)) f) = _
  rw [elvAffineScalarSpecialization_tmul, SuperalgebraCat.toElem_ofElem,
    elvScalarEvaluation_quotient]

/-- Affine Homs are reached by inserting coefficient one. Surjectivity here
does not concern the cyclotomic quotient or assert faithfulness. -/
theorem elvAffineScalarSpecialization_surjective (s t : List I) :
    Function.Surjective
      ((elvAffineScalarSpecialization D Sc cutoff values hvalues).map :
        (elvQuotientObj D Sc cutoff (coefficientObj D Sc s) ⟶
          elvQuotientObj D Sc cutoff (coefficientObj D Sc t)) →
        ((pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t))) := by
  intro f
  refine ⟨BoxProd.tmulHom (SuperalgebraCat.ofElem 1) f, ?_⟩
  rw [elvAffineScalarSpecialization_tmul, SuperalgebraCat.toElem_ofElem, map_one, one_smul]

end OddMath.QuiverHecke
end

end

section

/-!
# The distinct-colour step of the all-prefix QP induction

`docs/Nondegeneracy/DeformedGlobalQP.md`, §3, case `ν_n ≠ i` (the deformed form of
Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Theorem 8.5, (8.14)–(8.16)). Write
`Vₙ = moveHom i [] ν` and `Tₙ = lastToFirstHom i ν`. For a final letter `x ≠ i`,

    T_(n+1) V_(n+1) = Q_ix(x₁, x_(n+2)) ≫ ((Vₙ ≫ Tₙ) ⊗ 1_x)

as endomorphisms of `i :: (ν ++ [x])`, with the KLR polynomial `Q_ix` (`qPoly`) evaluated
at the dot on the moving strand and the dot on the new spectator. The local factor is
`τₙ gₙ = Q_ix(xₙ, x_(n+1))`; it is transported through `Vₙ ⊗ 1_x`.

The transport signs are trivial: by the scalar parity conditions of the datum, an odd
colour enters every monomial of `Q_ix` to an even power (`Sc.s_eq_zero`,
`Datum.even_d_of_odd`). Arbitrary colours, parities and words; `d_ix = 0` is included.

* `qPoly`: the polynomial `Q_ix(a, b)` in two commuting-free endomorphisms;
* `cross_cross_qPoly`: the double crossing on two strands of different colours is `qPoly`;
* `comp_qPoly`: `qPoly` is transported along a morphism moving both dots with signs that
  are trivial on the monomials that occur;
* `moveHom_lastToFirstHom_append_ne`: the displayed recursion.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) [CommRing k]
  (Sc : SKM.Scalars D k)

/-- The KLR polynomial `Q_ix(a, b)` of relation (1.7), in two endomorphisms. -/
def qPoly {A : (pres D Sc).Presented} (a b : End A) (i x : I) : End A :=
  if D.d i x = 0 then (Sc.t i x : k) • 1 else
    (∑ p ∈ Finset.range (D.dn i x), ∑ q ∈ Finset.range (D.dn x i),
        Sc.s i x p q • (a ^ p * b ^ q)) +
      ((Sc.t i x : k) • a ^ D.dn i x + (Sc.t x i : k) • b ^ D.dn x i)

/-- (1.7): the double crossing on strands of different colours is `Q_ix` in their dots. -/
theorem cross_cross_qPoly (l r : List I) {i x : I} (hix : i ≠ x)
    (h : SChain (l ++ [i, x] ++ r) (pl _ [.cross l.length, .cross l.length])
      (l ++ [i, x] ++ r)) :
    cl D Sc _ _ [.cross l.length, .cross l.length] h =
      qPoly D Sc (dotE D Sc (l ++ [i, x] ++ r) l.length)
        (dotE D Sc (l ++ [i, x] ++ r) (l.length + 1)) i x := by
  unfold qPoly
  split_ifs with hd
  · rw [cross_cross_ne_zero D Sc l r hix hd h]
    rfl
  · exact cross_cross_ne D Sc l r hix hd h

/-- Two transported classes compose to the class of the concatenated word. -/
@[reassoc]
theorem eqToHom_cl_eqToHom_cl {t₀ t t₁ t₂ t₃ : List I} {gs gs' : List PG} (e : t₀ = t)
    (e' : t₁ = t₂) (h₁ : SChain t (pl t gs) t₁) (h₂ : SChain t₂ (pl t₂ gs') t₃) :
    eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e) ≫ cl D Sc t t₁ gs h₁ ≫
        eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e') ≫ cl D Sc t₂ t₃ gs' h₂ =
      cl D Sc t₀ t₃ (gs ++ gs') (by subst e e'; exact sChain_append_of h₁ h₂) := by
  subst e e'
  simp only [eqToHom_refl, Category.id_comp]
  exact cl_comp D Sc gs gs' h₁ h₂

/-- The double crossing on a word given up to equality. -/
theorem cl_cross_cross_qPoly {w w' : List I} (l r : List I) {i x : I} (hix : i ≠ x)
    (hw : w = l ++ [i, x] ++ r) (hw' : w' = w) {gs : List PG}
    (hgs : gs = [.cross l.length, .cross l.length]) (h : SChain w (pl w gs) w') :
    cl D Sc w w' gs h =
      qPoly D Sc (dotE D Sc w l.length) (dotE D Sc w (l.length + 1)) i x ≫
        eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) hw'.symm) := by
  subst hw' hw hgs
  rw [eqToHom_refl, Category.comp_id]
  exact cross_cross_qPoly D Sc l r hix h

section Transport

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]

theorem comp_pow_of_signed {A B : C} (g : A ⟶ B) (a' : End A) (a : End B) (e : k)
    (h : g ≫ a = e • (a' ≫ g)) : ∀ n : ℕ, g ≫ a ^ n = e ^ n • ((a' ^ n : End A) ≫ g)
  | 0 => by simp [End.one_def]
  | n + 1 => by
    rw [pow_succ, End.mul_def, ← Category.assoc, h, Linear.smul_comp, Category.assoc,
      comp_pow_of_signed g a' a e h n, Linear.comp_smul, smul_smul, ← Category.assoc,
      pow_succ, pow_succ, End.mul_def, mul_comm]

theorem comp_monomial_of_signed {A B : C} (g : A ⟶ B) (a' b' : End A) (a b : End B)
    (ea eb : k) (ha : g ≫ a = ea • (a' ≫ g)) (hb : g ≫ b = eb • (b' ≫ g)) (p q : ℕ) :
    g ≫ (a ^ p * b ^ q) = (ea ^ p * eb ^ q) • ((a' ^ p * b' ^ q : End A) ≫ g) := by
  rw [End.mul_def, ← Category.assoc, comp_pow_of_signed g b' b eb hb, Linear.smul_comp,
    Category.assoc, comp_pow_of_signed g a' a ea ha, Linear.comp_smul, smul_smul,
    End.mul_def, Category.assoc, mul_comm]

end Transport

theorem zsign_pow (p : ZMod 2) : ∀ n : ℕ, SKM.zsign k p ^ n = SKM.zsign k ((n : ZMod 2) * p)
  | 0 => by simp [SKM.zsign]
  | n + 1 => by
    rw [pow_succ, zsign_pow p n, ← zsign_add_eq]
    congr 1
    push_cast
    ring

theorem zsign_pow_eq_one {p : ZMod 2} {n : ℕ} (h : (n : ZMod 2) * p = 0) :
    SKM.zsign k p ^ n = 1 := by
  rw [zsign_pow, h]
  simp [SKM.zsign]

theorem zmod_two_eq_zero_of_ne_one {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  fin_cases a
  · rfl
  · exact absurd rfl h

theorem dn_mul_parity (i x : I) : (D.dn i x : ZMod 2) * D.parity i = 0 := by
  by_cases hi : D.parity i = 1
  · by_cases hix : i = x
    · subst hix
      simp [SKM.Datum.dn, D.d_self]
    · obtain ⟨m, hm⟩ := D.even_d_of_odd hi x
      have hc : (D.dn i x : ℤ) = m + m := by rw [D.dn_cast hix, hm]
      have : D.dn i x = m.toNat + m.toNat := by omega
      rw [this, hi]
      push_cast
      ring_nf
      rw [show (2 : ZMod 2) = 0 from rfl, mul_zero]
  · rw [zmod_two_eq_zero_of_ne_one hi, mul_zero]

section EndAdditive

variable {C : Type*} [Category C] [Preadditive C]

theorem comp_end_add {A B : C} (g : A ⟶ B) (u v : End B) :
    g ≫ (u + v) = g ≫ u + g ≫ v :=
  Preadditive.comp_add _ _ _ _ _ _

theorem end_add_comp {A B : C} (g : A ⟶ B) (u v : End A) :
    (u + v) ≫ g = u ≫ g + v ≫ g :=
  Preadditive.add_comp _ _ _ _ _ _

theorem comp_end_sum {A B : C} {ι : Type*} (s : Finset ι) (g : A ⟶ B) (u : ι → End B) :
    g ≫ (∑ j ∈ s, u j) = ∑ j ∈ s, g ≫ u j :=
  Preadditive.comp_sum _ _ _

theorem end_sum_comp {A B : C} {ι : Type*} (s : Finset ι) (g : A ⟶ B) (u : ι → End A) :
    (∑ j ∈ s, u j) ≫ g = ∑ j ∈ s, u j ≫ g :=
  Preadditive.sum_comp _ _ _

theorem comp_smul_end [Linear k C] {A B : C} (g : A ⟶ B) (c : k) (u : End B) :
    g ≫ (c • u) = c • (g ≫ u) :=
  Linear.comp_smul _ _ _ _ _ _

theorem smul_end_comp [Linear k C] {A B : C} (g : A ⟶ B) (c : k) (u : End A) :
    (c • u) ≫ g = c • (u ≫ g) :=
  Linear.smul_comp _ _ _ _ _ _

end EndAdditive

/-- `Q_ix` is transported along `g` when the two dots move with signs `ea`, `eb` that are
trivial on even powers of an odd colour. -/
theorem comp_qPoly {A B : (pres D Sc).Presented} (g : A ⟶ B) (a' b' : End A) (a b : End B)
    (i x : I) (ea eb : k) (ha : g ≫ a = ea • (a' ≫ g)) (hb : g ≫ b = eb • (b' ≫ g))
    (hea : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 → ea ^ n = 1)
    (heb : ∀ n : ℕ, (n : ZMod 2) * D.parity x = 0 → eb ^ n = 1) :
    g ≫ qPoly D Sc a b i x = qPoly D Sc a' b' i x ≫ g := by
  unfold qPoly
  split_ifs with hd
  · rw [End.one_def, End.one_def, Linear.comp_smul, Linear.smul_comp, Category.comp_id,
      Category.id_comp]
  · simp only [comp_end_add, end_add_comp, comp_smul_end, smul_end_comp]
    erw [comp_end_sum, end_sum_comp]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      erw [comp_end_sum, end_sum_comp]
      refine Finset.sum_congr rfl fun q _ => ?_
      erw [comp_smul_end, smul_end_comp]
      by_cases hs : Sc.s i x p q = 0
      · rw [hs, zero_smul, zero_smul]
      · rw [comp_monomial_of_signed g a' b' a b ea eb ha hb p q,
          hea p (zmod_two_eq_zero_of_ne_one fun h => hs (Sc.s_eq_zero i x p q h)),
          heb q (zmod_two_eq_zero_of_ne_one fun h => hs (by
            rw [Sc.s_symm]; exact Sc.s_eq_zero x i q p h)), one_mul, one_smul]
    · rw [comp_pow_of_signed g a' a ea ha, comp_pow_of_signed g b' b eb hb,
        hea _ (dn_mul_parity D i x), heb _ (dn_mul_parity D x i), one_smul, one_smul]

/-- A dot on an appended strand is the left whiskering of the one-strand dot. -/
theorem whiskerLeft_dotE (w : List I) (x : I) {a : ℕ} (ha : a = w.length) :
    (pres D Sc).obj (ob D w) ◁ dotE D Sc [x] 0 = dotE D Sc (w ++ [x]) a := by
  subst ha
  rw [dotE_eq, cl_whiskerLeft, dotE_eq]
  exact cl_congr_gs D Sc (by simp) _ _

/-- The moving-strand dot through `Vₙ ⊗ 1_x`. -/
theorem moveHom_whiskerRight_comp_dot (i x : I) (ν : List I) :
    (moveHom D Sc i [] ν ▷ (pres D Sc).obj (ob D [x])) ≫
        dotE D Sc (ν ++ [i] ++ [x]) ν.length =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        (dotE D Sc (i :: (ν ++ [x])) 0 ≫ (moveHom D Sc i [] ν ▷ (pres D Sc).obj (ob D [x]))) := by
  have h := congrArg (· ▷ (pres D Sc).obj (ob D [x])) (dot_comp_moveHom D Sc i [] ν)
  simp only [MonoidalSupercategory.comp_whiskerRight (R := k),
    MonoidalSupercategory.smul_whiskerRight (R := k)] at h
  rw [dotE_whiskerRight D Sc _ _ _ (by simp),
    dotE_whiskerRight D Sc _ _ _ (by simp)] at h
  have h' := congrArg (SKM.zsign k (D.parity i * wordSumParity D ν) • ·) h
  simp only [smul_smul, zsign_mul_self, one_smul, List.length_nil, zero_add] at h'
  exact h'.symm

/-- The dot on the new spectator through `Vₙ ⊗ 1_x`, by super interchange. -/
theorem moveHom_whiskerRight_comp_last_dot (i x : I) (ν : List I) :
    (moveHom D Sc i [] ν ▷ (pres D Sc).obj (ob D [x])) ≫
        dotE D Sc (ν ++ [i] ++ [x]) (ν.length + 1) =
      SKM.zsign k (D.parity i * wordSumParity D ν * D.parity x) •
        (dotE D Sc (i :: (ν ++ [x])) (ν.length + 1) ≫
          (moveHom D Sc i [] ν ▷ (pres D Sc).obj (ob D [x]))) := by
  have e1 : dotE D Sc (ν ++ [i] ++ [x]) (ν.length + 1) =
      (pres D Sc).obj (ob D (ν ++ [i])) ◁ dotE D Sc [x] 0 :=
    (whiskerLeft_dotE D Sc (ν ++ [i]) x (by simp)).symm
  have e2 : dotE D Sc (i :: (ν ++ [x])) (ν.length + 1) =
      (pres D Sc).obj (ob D (i :: ν)) ◁ dotE D Sc [x] 0 :=
    (whiskerLeft_dotE D Sc (i :: ν) x (by simp)).symm
  rw [e1, e2]
  refine (MonoidalSupercategory.super_interchange (R := k) (moveHom_parity D Sc i [] ν)
      (positionedDot_parity D Sc [] [] x)).trans ?_
  unfold Supercategory.koszulSign SKM.zsign
  by_cases hp : D.parity i * wordSumParity D ν = 1 <;> by_cases hx : D.parity x = 1 <;>
    simp [hp, hx]

/-- The distinct-colour step: `T_(n+1) V_(n+1) = Q_ix(x₁, x_(n+2)) ((Tₙ Vₙ) ⊗ 1_x)`. -/
theorem moveHom_lastToFirstHom_append_ne {i x : I} (hix : i ≠ x) (ν : List I) :
    moveHom D Sc i [] (ν ++ [x]) ≫ lastToFirstHom D Sc i (ν ++ [x]) =
      qPoly D Sc (dotE D Sc (i :: (ν ++ [x])) 0) (dotE D Sc (i :: (ν ++ [x])) (ν.length + 1))
          i x ≫
        ((moveHom D Sc i [] ν ≫ lastToFirstHom D Sc i ν) ▷ (pres D Sc).obj (ob D [x])) := by
  rw [moveHom_append_singleton, lastToFirstHom_append_singleton,
    intertwinerHom_of_ne D Sc _ _ hix]
  simp only [Category.assoc]
  erw [eqToHom_cl_eqToHom_cl_assoc]
  rw [
    cl_cross_cross_qPoly D Sc ν [] hix (by simp [ob]) (by simp [ob]) (by simp)]
  erw [Category.id_comp]
  rw [MonoidalSupercategory.comp_whiskerRight (R := k), ← Category.assoc,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Category.assoc]
  erw [Category.comp_id]
  exact comp_qPoly D Sc _ _ _ _ _ i x _ _
    (moveHom_whiskerRight_comp_dot D Sc i x ν)
    (moveHom_whiskerRight_comp_last_dot D Sc i x ν)
    (fun n hn => by
      rw [zsign_pow_eq_one]
      rw [← mul_assoc, hn, zero_mul])
    (fun n hn => by
      rw [zsign_pow_eq_one]
      linear_combination (D.parity i * wordSumParity D ν) * hn)
  all_goals simp [ob]

end OddMath.QuiverHecke
end

end

section

/-!
# The repeated-colour step of the all-prefix QP induction

`docs/Nondegeneracy/DeformedGlobalQP.md`, §§2–3, case `ν_n = i` (the deformed form of
Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Theorem 8.5, (8.14)–(8.17)). Write
`Vₙ = moveHom i [] ν`, `Tₙ = lastToFirstHom i ν` and `W = ν ++ [i] ++ [i]`. On `W` let `u, v`
be the dots at positions `|ν|, |ν| + 1` (the moving strand and the new spectator), and on
`i :: (ν ++ [i])` let `u₀, v₀` be the dots at positions `0, |ν| + 1`. Put
`h = p(ν₁) + ⋯ + p(νₙ)` and `s = (-1)^(p(i) h)`.

* `moveHom_append_self`, `lastToFirstHom_append_self`: `V_(n+1) = (Vₙ ⊗ 1) g` and
  `T_(n+1) = (Tₙ ⊗ 1) τ` with `g` the same-colour intertwiner of `W` at `|ν|`
  (`sameIntertwiner`) and `τ` the crossing there.
* `moveHom_whiskerRight_comp_sameIntertwiner_odd`, `_even`: the expansion of
  `(Vₙ ⊗ 1) g` with its polynomial part moved in front of `Vₙ ⊗ 1`:
  `D V = V D₀` and `E V = s V E₀` for `E = v - u`, `D = v² - u²`. In the odd case
  `g = D E - D D τ` (in execution order); in the even case `g = E + E E τ`.
  These are the two terms of the relation (K) used in the induction.
* `moveHom_lastToFirstHom_append_self_odd`, `_even`: the recursion
  `V_(n+1) T_(n+1) = s D₀ E₀ (Vₙ ⊗ 1) T_(n+1)` for odd `i` and
  `V_(n+1) T_(n+1) = E₀ (Vₙ ⊗ 1) T_(n+1)` for even `i` (KKO (8.15): `τ g = τ E D`,
  resp. `τ E`).

Arbitrary words and parities.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory SignedNilHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) [CommRing k]
  (Sc : SKM.Scalars D k)

/-! ### Two-strand algebra -/

section TwoStrand

variable {B : Type*} [Ring B]

/-- The odd same-colour intertwiner with its polynomial factors on the right. -/
theorem OddTwo.element_eq_sub {x y T : B} (h : OddTwo x y T) :
    OddNilHecke.Intertwiner.element x y T =
      (y - x) * OddNilHecke.Intertwiner.squareDiff x y -
        T * OddNilHecke.Intertwiner.squareDiff x y * OddNilHecke.Intertwiner.squareDiff x y := by
  rw [h.element_identities.2.2.2.1]
  noncomm_ring

/-- The even same-colour intertwiner with its polynomial factors on the right. -/
theorem EvenTwo.gEven_eq_add {x y T : B} (h : EvenTwo x y T) :
    gEven x y T = (y - x) + T * (y - x) * (y - x) := by
  simp only [phiEven, gEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    h.tu', h.tv', h.vu, mul_one]
  noncomm_ring

end TwoStrand

/-! ### Signed transport of differences -/

section Transport

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]

theorem comp_end_sub {A B : C} (g : A ⟶ B) (a b : End B) :
    g ≫ (b - a) = g ≫ b - g ≫ a :=
  Preadditive.comp_sub _ _ _

theorem end_sub_comp {A B : C} (g : A ⟶ B) (a b : End A) :
    (b - a) ≫ g = b ≫ g - a ≫ g :=
  Preadditive.sub_comp _ _ _

theorem comp_sub_of_signed {A B : C} (g : A ⟶ B) (a' b' : End A) (a b : End B) (s : k)
    (ha : g ≫ a = s • (a' ≫ g)) (hb : g ≫ b = s • (b' ≫ g)) :
    g ≫ (b - a) = s • ((b' - a') ≫ g) := by
  rw [comp_end_sub, ha, hb, end_sub_comp, smul_sub]

theorem comp_squareDiff_of_signed {A B : C} (g : A ⟶ B) (a' b' : End A) (a b : End B)
    (s : k) (hs : s ^ 2 = 1) (ha : g ≫ a = s • (a' ≫ g)) (hb : g ≫ b = s • (b' ≫ g)) :
    g ≫ OddNilHecke.Intertwiner.squareDiff (A := End B) a b =
      OddNilHecke.Intertwiner.squareDiff (A := End A) a' b' ≫ g := by
  unfold OddNilHecke.Intertwiner.squareDiff
  rw [comp_end_sub, comp_pow_of_signed g a' a s ha, comp_pow_of_signed g b' b s hb, hs,
    one_smul, one_smul, end_sub_comp]

end Transport

theorem zmod_two_mul_self (p : ZMod 2) : p * p = p := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz p with rfl | rfl <;> rfl

/-! ### The last-letter recursions on `ν ++ [i]` -/

theorem eqToHom_sameIntertwiner_eqToHom {w w' w'' : List I} (e : w = w') (e' : w' = w'')
    (a : ℕ) (i : I) :
    eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) e) ≫
        sameIntertwiner D Sc w' a i ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) e') =
      sameIntertwiner D Sc w a i ≫
        eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (e.trans e')) := by
  subst e e'
  simp

/-- `Vₙ ⊗ 1_i`, typed between the words `i :: (ν ++ [i])` and `ν ++ [i] ++ [i]`. -/
def moveWhisker (i : I) (ν : List I) :
    (pres D Sc).obj (ob D (i :: (ν ++ [i]))) ⟶ (pres D Sc).obj (ob D (ν ++ [i] ++ [i])) :=
  moveHom D Sc i [] ν ▷ (pres D Sc).obj (ob D [i])

/-- `V_(n+1) = (Vₙ ⊗ 1_i) g` on `ν ++ [i]`, with `g` the same-colour intertwiner. -/
theorem moveHom_append_self (i : I) (ν : List I) :
    moveHom D Sc i [] (ν ++ [i]) =
      moveWhisker D Sc i ν ≫ sameIntertwiner D Sc (ν ++ [i] ++ [i]) ν.length i := by
  rw [moveHom_append_singleton, intertwinerHom_self, eqToHom_sameIntertwiner_eqToHom]
  · erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  all_goals simp [ob]

/-- `T_(n+1) = (Tₙ ⊗ 1_i) τ` on `ν ++ [i]`, with `τ` the crossing at `|ν|`. -/
theorem lastToFirstHom_append_self (i : I) (ν : List I) :
    lastToFirstHom D Sc i (ν ++ [i]) =
      crossE D Sc (ν ++ [i] ++ [i]) ν.length ≫
        (lastToFirstHom D Sc i ν ▷ (pres D Sc).obj (ob D [i])) := by
  rw [lastToFirstHom_append_singleton, crossE_eq_cl]

/-- The moving-strand dot through `Vₙ ⊗ 1_i`. -/
theorem moveWhisker_comp_dot (i : I) (ν : List I) :
    moveWhisker D Sc i ν ≫ dotE D Sc (ν ++ [i] ++ [i]) ν.length =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        (dotE D Sc (i :: (ν ++ [i])) 0 ≫ moveWhisker D Sc i ν) :=
  moveHom_whiskerRight_comp_dot D Sc i i ν

/-- The spectator dot through `Vₙ ⊗ 1_i`, with the same sign `s = (-1)^(p(i) h)`. -/
theorem moveWhisker_comp_last_dot (i : I) (ν : List I) :
    moveWhisker D Sc i ν ≫ dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) ≫ moveWhisker D Sc i ν) := by
  have h := moveHom_whiskerRight_comp_last_dot D Sc i i ν
  rw [mul_right_comm, zmod_two_mul_self] at h
  exact h

theorem zsign_sq (p : ZMod 2) : SKM.zsign k p ^ 2 = 1 := by
  rw [sq, zsign_mul_self]

/-- `D V = V D₀` for `D = v² - u²`. -/
theorem moveWhisker_comp_squareDiff (i : I) (ν : List I) :
    moveWhisker D Sc i ν ≫
        OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (ν ++ [i] ++ [i]) ν.length)
          (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1)) =
      OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
          (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫ moveWhisker D Sc i ν :=
  comp_squareDiff_of_signed _ _ _ _ _ _ (zsign_sq _) (moveWhisker_comp_dot D Sc i ν)
    (moveWhisker_comp_last_dot D Sc i ν)

/-- `E V = s V E₀` for `E = v - u`. -/
theorem moveWhisker_comp_sub (i : I) (ν : List I) :
    moveWhisker D Sc i ν ≫
        (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) - dotE D Sc (ν ++ [i] ++ [i]) ν.length) =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        ((dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
          moveWhisker D Sc i ν) :=
  comp_sub_of_signed _ _ _ _ _ _ (moveWhisker_comp_dot D Sc i ν)
    (moveWhisker_comp_last_dot D Sc i ν)

theorem moveWhisker_comp_squareDiff_assoc (i : I) (ν : List I) {Z : (pres D Sc).Presented}
    (h : (pres D Sc).obj (ob D (ν ++ [i] ++ [i])) ⟶ Z) :
    moveWhisker D Sc i ν ≫
        OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (ν ++ [i] ++ [i]) ν.length)
          (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1)) ≫ h =
      OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
          (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫ moveWhisker D Sc i ν ≫ h := by
  rw [← Category.assoc, moveWhisker_comp_squareDiff, Category.assoc]

theorem moveWhisker_comp_sub_assoc (i : I) (ν : List I) {Z : (pres D Sc).Presented}
    (h : (pres D Sc).obj (ob D (ν ++ [i] ++ [i])) ⟶ Z) :
    moveWhisker D Sc i ν ≫
        (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) - dotE D Sc (ν ++ [i] ++ [i]) ν.length) ≫ h =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        ((dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
          moveWhisker D Sc i ν ≫ h) := by
  rw [← Category.assoc, moveWhisker_comp_sub, Linear.smul_comp, Category.assoc]

theorem oddTwo_append_self (i : I) (hp : D.parity i = 1) (ν : List I) :
    OddTwo (dotE D Sc (ν ++ [i] ++ [i]) ν.length)
      (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1))
      (crossE D Sc (ν ++ [i] ++ [i]) ν.length) := by
  have e : ν ++ [i] ++ [i] = ν ++ [i, i] ++ [] := by simp
  rw [e]
  exact oddTwo_block D Sc ν [] i hp

theorem evenTwo_append_self (i : I) (hp : D.parity i = 0) (ν : List I) :
    EvenTwo (dotE D Sc (ν ++ [i] ++ [i]) ν.length)
      (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1))
      (crossE D Sc (ν ++ [i] ++ [i]) ν.length) := by
  have e : ν ++ [i] ++ [i] = ν ++ [i, i] ++ [] := by simp
  rw [e]
  exact evenTwo_block D Sc ν [] i hp

theorem zsign_parity_even (i : I) (hp : D.parity i = 0) (ν : List I) :
    SKM.zsign k (D.parity i * wordSumParity D ν) = 1 := by
  rw [hp, zero_mul]
  simp [SKM.zsign]

/-- Odd colour: `(Vₙ ⊗ 1) g = s D₀ E₀ (Vₙ ⊗ 1) - D₀ D₀ (Vₙ ⊗ 1) τ` (execution order). -/
theorem moveWhisker_comp_sameIntertwiner_odd (i : I) (hp : D.parity i = 1) (ν : List I) :
    moveWhisker D Sc i ν ≫ sameIntertwiner D Sc (ν ++ [i] ++ [i]) ν.length i =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
          (OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
              (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫
            (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
              moveWhisker D Sc i ν) -
        OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
            (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫
          OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
              (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫
            moveWhisker D Sc i ν ≫ crossE D Sc (ν ++ [i] ++ [i]) ν.length := by
  simp only [sameIntertwiner, hp, ↓reduceIte]
  rw [OddTwo.element_eq_sub (oddTwo_append_self D Sc i hp ν), comp_end_sub]
  simp only [End.mul_def]
  rw [moveWhisker_comp_squareDiff_assoc, moveWhisker_comp_sub, Linear.comp_smul,
    moveWhisker_comp_squareDiff_assoc, moveWhisker_comp_squareDiff_assoc, hp]

/-- Even colour: `(Vₙ ⊗ 1) g = E₀ (Vₙ ⊗ 1) + E₀ E₀ (Vₙ ⊗ 1) τ` (execution order). -/
theorem moveWhisker_comp_sameIntertwiner_even (i : I) (hp : D.parity i = 0) (ν : List I) :
    moveWhisker D Sc i ν ≫ sameIntertwiner D Sc (ν ++ [i] ++ [i]) ν.length i =
      (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
          moveWhisker D Sc i ν +
        (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
          (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
            moveWhisker D Sc i ν ≫ crossE D Sc (ν ++ [i] ++ [i]) ν.length := by
  have hp' : ¬D.parity i = 1 := by rw [hp]; decide
  simp only [sameIntertwiner, hp', ↓reduceIte]
  rw [EvenTwo.gEven_eq_add (evenTwo_append_self D Sc i hp ν)]
  simp only [End.mul_def, comp_end_add]
  rw [moveWhisker_comp_sub, moveWhisker_comp_sub_assoc, moveWhisker_comp_sub_assoc,
    zsign_parity_even D i hp ν]
  simp only [one_smul]

/-- KKO (8.15), odd colour: `V_(n+1) T_(n+1) = s D₀ E₀ (Vₙ ⊗ 1_i) T_(n+1)`. -/
theorem moveHom_lastToFirstHom_append_self_odd (i : I) (hp : D.parity i = 1) (ν : List I) :
    moveHom D Sc i [] (ν ++ [i]) ≫ lastToFirstHom D Sc i (ν ++ [i]) =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        (OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
            (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫
          (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
            moveWhisker D Sc i ν ≫ lastToFirstHom D Sc i (ν ++ [i])) := by
  have hg : sameIntertwiner D Sc (ν ++ [i] ++ [i]) ν.length i ≫
        crossE D Sc (ν ++ [i] ++ [i]) ν.length =
      OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (ν ++ [i] ++ [i]) ν.length)
          (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1)) ≫
        (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) - dotE D Sc (ν ++ [i] ++ [i]) ν.length) ≫
          crossE D Sc (ν ++ [i] ++ [i]) ν.length := by
    simp only [sameIntertwiner, hp, ↓reduceIte]
    rw [← End.mul_def, (oddTwo_append_self D Sc i hp ν).element_identities.2.2.2.2]
    simp only [End.mul_def]
  rw [moveHom_append_self, lastToFirstHom_append_self, Category.assoc,
    ← Category.assoc (sameIntertwiner _ _ _ _ _), hg]
  simp only [Category.assoc]
  rw [moveWhisker_comp_squareDiff_assoc, moveWhisker_comp_sub_assoc, Linear.comp_smul]

/-- KKO (8.15), even colour: `V_(n+1) T_(n+1) = E₀ (Vₙ ⊗ 1_i) T_(n+1)`. -/
theorem moveHom_lastToFirstHom_append_self_even (i : I) (hp : D.parity i = 0) (ν : List I) :
    moveHom D Sc i [] (ν ++ [i]) ≫ lastToFirstHom D Sc i (ν ++ [i]) =
      (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
        moveWhisker D Sc i ν ≫ lastToFirstHom D Sc i (ν ++ [i]) := by
  have hp' : ¬D.parity i = 1 := by rw [hp]; decide
  have hg : sameIntertwiner D Sc (ν ++ [i] ++ [i]) ν.length i ≫
        crossE D Sc (ν ++ [i] ++ [i]) ν.length =
      (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) - dotE D Sc (ν ++ [i] ++ [i]) ν.length) ≫
        crossE D Sc (ν ++ [i] ++ [i]) ν.length := by
    simp only [sameIntertwiner, hp', ↓reduceIte]
    rw [← End.mul_def, (evenTwo_append_self D Sc i hp ν).t_mul_gEven]
    rfl
  rw [moveHom_append_self, lastToFirstHom_append_self, Category.assoc,
    ← Category.assoc (sameIntertwiner _ _ _ _ _), hg]
  simp only [Category.assoc]
  rw [moveWhisker_comp_sub_assoc, zsign_parity_even D i hp ν, one_smul]

end OddMath.QuiverHecke
end

end

section

/-!
# Annihilators in the prescribed prepend target

`PrependKills z` says that the right ideal generated by `z` acts by zero on the
balanced target `B φ(1) ⊗ q`. It is closed under left multiplication, right
multiplication by the prepend image and by the first dot, and contains the
prepend images of the cyclotomic kernel. The square cancellation
`prependKills_of_sq_sub` removes a right factor `x₁² − φ(c)` for every old
element `c`; the even linear cancellation removes `φ(c) − x₁` when `p(i) = 0`.
These are the algebraic steps of the QP induction in `DeformedGlobalQP.md`.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

/-- The right ideal generated by `z` acts by zero on the prescribed target. -/
def PrependKills (z : Hn D Sc (n + 1 + 1)) : Prop :=
  ∀ (r : Hn D Sc (n + 1 + 1)) (b : (qCoefficient D Sc i β a ha n).toSVec),
    InductionAlong.Ind.tmul ((r * z) • InductionAlong.unitGen
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))) b = 0

variable {D Sc i β a ha n}

theorem PrependKills.zero : PrependKills D Sc i β a ha n 0 := by
  intro r b
  rw [mul_zero, zero_smul]
  exact InductionAlong.Ind.zero_tmul b

theorem PrependKills.add {z w : Hn D Sc (n + 1 + 1)} (hz : PrependKills D Sc i β a ha n z)
    (hw : PrependKills D Sc i β a ha n w) : PrependKills D Sc i β a ha n (z + w) := by
  intro r b
  rw [mul_add, add_smul, InductionAlong.Ind.add_tmul, hz r b, hw r b, add_zero]

theorem PrependKills.mul_left {z : Hn D Sc (n + 1 + 1)} (hz : PrependKills D Sc i β a ha n z)
    (y : Hn D Sc (n + 1 + 1)) : PrependKills D Sc i β a ha n (y * z) := by
  intro r b
  rw [← mul_assoc]
  exact hz _ b

theorem PrependKills.neg {z : Hn D Sc (n + 1 + 1)} (hz : PrependKills D Sc i β a ha n z) :
    PrependKills D Sc i β a ha n (-z) := by
  intro r b
  rw [mul_neg, ← neg_mul]
  exact hz _ b

theorem PrependKills.sub {z w : Hn D Sc (n + 1 + 1)} (hz : PrependKills D Sc i β a ha n z)
    (hw : PrependKills D Sc i β a ha n w) : PrependKills D Sc i β a ha n (z - w) := by
  rw [sub_eq_add_neg]
  exact hz.add hw.neg

theorem PrependKills.smul {z : Hn D Sc (n + 1 + 1)} (hz : PrependKills D Sc i β a ha n z)
    (c : k) : PrependKills D Sc i β a ha n (c • z) := by
  intro r b
  rw [mul_smul_comm, ← smul_mul_assoc]
  exact hz _ b

theorem PrependKills.of_eq {z w : Hn D Sc (n + 1 + 1)} (hz : PrependKills D Sc i β a ha n z)
    (h : z = w) : PrependKills D Sc i β a ha n w := h ▸ hz

section Morphism

variable (D Sc i β a ha n) in
/-- The endomorphism `Y` of `i :: w`, placed in its corner, generates a right ideal
acting by zero on the prescribed target. -/
def KillE (w : Word I (n + 1)) (Y : End (wordObj D Sc (prependWord i w))) : Prop :=
  PrependKills D Sc i β a ha n (FiniteHomMatrix.cornerMap (prependWord i w) Y)

variable {w : Word I (n + 1)}

theorem KillE.comp {Y : End (wordObj D Sc (prependWord i w))}
    (hY : KillE D Sc i β a ha n w Y) (g : End (wordObj D Sc (prependWord i w))) :
    KillE D Sc i β a ha n w (Y ≫ g) := by
  unfold KillE
  rw [← End.mul_def, map_mul]
  exact PrependKills.mul_left hY _

theorem KillE.add {Y Z : End (wordObj D Sc (prependWord i w))}
    (hY : KillE D Sc i β a ha n w Y) (hZ : KillE D Sc i β a ha n w Z) :
    KillE D Sc i β a ha n w (Y + Z) := by
  unfold KillE
  rw [map_add]
  exact PrependKills.add hY hZ

theorem KillE.neg {Y : End (wordObj D Sc (prependWord i w))}
    (hY : KillE D Sc i β a ha n w Y) : KillE D Sc i β a ha n w (-Y) := by
  unfold KillE
  rw [map_neg]
  exact PrependKills.neg hY

theorem KillE.sub {Y Z : End (wordObj D Sc (prependWord i w))}
    (hY : KillE D Sc i β a ha n w Y) (hZ : KillE D Sc i β a ha n w Z) :
    KillE D Sc i β a ha n w (Y - Z) := by
  rw [sub_eq_add_neg]
  exact KillE.add hY (KillE.neg hZ)

theorem KillE.smul {Y : End (wordObj D Sc (prependWord i w))}
    (hY : KillE D Sc i β a ha n w Y) (c : k) : KillE D Sc i β a ha n w (c • Y) := by
  unfold KillE
  change PrependKills D Sc i β a ha n (FiniteHomMatrix.single _ _ (c • Y))
  rw [FiniteHomMatrix.single_smul]
  exact PrependKills.smul hY c

theorem KillE.of_eq {Y Z : End (wordObj D Sc (prependWord i w))}
    (hY : KillE D Sc i β a ha n w Y) (h : Y = Z) : KillE D Sc i β a ha n w Z := h ▸ hY

theorem killE_zero : KillE D Sc i β a ha n w 0 := by
  unfold KillE
  rw [map_zero]
  exact PrependKills.zero

/-- Transport along an equality of words. -/
theorem KillE.transport {w' : Word I (n + 1)} (e : w = w')
    {Y : End (wordObj D Sc (prependWord i w))} (hY : KillE D Sc i β a ha n w Y) :
    KillE D Sc i β a ha n w' (eqToHom (by rw [e]) ≫ Y ≫ eqToHom (by rw [e])) := by
  subst e
  simpa using hY

end Morphism

end OddMath.QuiverHecke
end

end

section

/-!
# The relation-killing step (K) with a right context

`DeformedGlobalQP.md`, §2: after the strand of colour `i` has crossed the prefix
`μ ++ [i]` and the last old `i` has been brought back to the front, the first-position
relation `f_i(x₁)` lies in the old cyclotomic ideal. This file proves the version with an
arbitrary right context `σ`, which the all-prefix induction needs:

* `killE_whiskerLeft_comp`: precomposition by `1_i ⊗ g` kills when `g` lies in the old
  cyclotomic kernel;
* `killE_relation_context`: the identity (K) on the word `i :: (μ ++ [i] ++ σ)`.

Supporting whiskering identities: `twist_whiskerRight_obj` (the parity twist commutes with
right whiskering), `whiskerLeft_whiskerRight_cons`, `whiskerRight_whiskerRight_word`
(associativity of whiskering by words) and `whiskerLeft_dotE_cons`.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

section Whisker

/-- Right whiskering of a left whiskering by a letter, on words. -/
theorem whiskerLeft_whiskerRight_cons (i : I) {t t' : List I}
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) (σ : List I) :
    ((pres D Sc).obj (ob D [i]) ◁ g) ▷ (pres D Sc).obj (ob D σ) =
      ((pres D Sc).obj (ob D [i]) ◁ (g ▷ (pres D Sc).obj (ob D σ)) :
        (pres D Sc).obj (ob D (i :: (t ++ σ))) ⟶ (pres D Sc).obj (ob D (i :: (t' ++ σ)))) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D [i]))) g (𝟙 ((pres D Sc).obj (ob D σ)))
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  simpa using h

/-- Right whiskering by a word, as a homomorphism of `k`-algebras. -/
def whiskerWordAlgHom (w s : List I) :
    End ((pres D Sc).obj (ob D w)) →ₐ[k] End ((pres D Sc).obj (ob D (w ++ s))) where
  __ := whiskerWordRingHom D Sc w s
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change (c • 𝟙 _) ▷ _ = c • 𝟙 _
    rw [MonoidalSupercategory.smul_whiskerRight (R := k),
      MonoidalSupercategory.id_whiskerRight (R := k)]
    rfl

@[simp] theorem whiskerWordAlgHom_apply (w s : List I) (f : End ((pres D Sc).obj (ob D w))) :
    whiskerWordAlgHom D Sc w s f = f ▷ (pres D Sc).obj (ob D s) := rfl

end Whisker

variable [Fintype I] (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

section Killing

end Killing

end OddMath.QuiverHecke
end

end

section

/-!
# Right contexts in the old ELV coefficient category

For the relation-killing step of `DeformedGlobalQP.md` §2, adjoining an arbitrary
spectator word preserves the old cyclotomic ideal. The map fixes the full ELV
coefficient algebra and right-whiskers only the affine factor. In particular it
preserves signed composition and commutes with insertion of a strand on the left.

`rightContext_relation` preserves the colour-dependent ELV relation, with its odd
exterior coefficients and arbitrary cutoff, and `ideal_rightContext` extends this
to the two-sided old ideal. No finiteness condition on the colour set is needed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Adjoin identity strands on the right of an affine morphism. -/
def affineRightContext (σ v w : List I) :
    ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) →ₗ[k]
    ((pres D Sc).obj (ob D (v ++ σ)) ⟶ (pres D Sc).obj (ob D (w ++ σ))) where
  toFun f := f ▷ (pres D Sc).obj (ob D σ)
  map_add' f g := MonoidalSupercategory.add_whiskerRight (R := k) f g _
  map_smul' c f := MonoidalSupercategory.smul_whiskerRight (R := k) c f _

/-- Right extension fixes all polynomial and exterior coefficients. -/
def rightContext (σ v w : List I) : hom D Sc cutoff v w →ₗ[k]
    hom D Sc cutoff (v ++ σ) (w ++ σ) :=
  TensorProduct.map LinearMap.id (affineRightContext D Sc σ v w)

@[simp] theorem rightContext_tmul (σ : List I) {v w : List I}
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    rightContext D Sc cutoff σ v w (a ⊗ₜ[k] f) =
      a ⊗ₜ[k] affineRightContext D Sc σ v w f := rfl

private theorem rightContext_induction_hom {v w : List I}
    {P : hom D Sc cutoff v w → Prop} (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

/-- Right extension respects the signed coefficient-category composition. -/
theorem rightContext_comp (σ : List I) {v w z : List I}
    (f : hom D Sc cutoff v w) (g : hom D Sc cutoff w z) :
    rightContext D Sc cutoff σ v z (f ≫ g) =
      rightContext D Sc cutoff σ v w f ≫ rightContext D Sc cutoff σ w z g := by
  induction f using rightContext_induction_hom D Sc cutoff with
  | zero => simp only [Limits.zero_comp, map_zero]
  | add f f' hf hf' => simp only [Preadditive.add_comp, map_add, hf, hf']
  | tmul p q a f ha hf =>
    induction g using rightContext_induction_hom D Sc cutoff with
    | zero => simp only [Limits.comp_zero, map_zero]
    | add g g' hg hg' => simp only [Preadditive.comp_add, map_add, hg, hg']
    | tmul r s b g hb hg =>
      have hi : affineRightContext D Sc σ w z g ∈ parity (R := k) _ _ s :=
        MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D σ)) hg
      rw [BoxProd.tmulHom_comp_tmulHom ha f b hg, map_zsmul]
      change koszulSign p s • BoxProd.tmulHom
        (X := obj D Sc cutoff (v ++ σ)) (Y := obj D Sc cutoff (z ++ σ))
        (a ≫ b) (affineRightContext D Sc σ v z (f ≫ g)) =
        BoxProd.tmulHom (X := obj D Sc cutoff (v ++ σ))
          (Y := obj D Sc cutoff (w ++ σ)) a (affineRightContext D Sc σ v w f) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (w ++ σ))
          (Y := obj D Sc cutoff (z ++ σ)) b (affineRightContext D Sc σ w z g)
      rw [BoxProd.tmulHom_comp_tmulHom
        (X := obj D Sc cutoff (v ++ σ)) (Y := obj D Sc cutoff (w ++ σ))
        (Z := obj D Sc cutoff (z ++ σ)) ha _ b hi]
      congr 2
      exact MonoidalSupercategory.comp_whiskerRight (R := k) f g ((pres D Sc).obj (ob D σ))

/-- Left insertion and right extension commute, with coefficients unchanged. -/
theorem rightContext_insert (σ : List I) (i : I) {v w : List I}
    (f : hom D Sc cutoff v w) :
    rightContext D Sc cutoff σ (i :: v) (i :: w) (insert D Sc cutoff i v w f) =
      insert D Sc cutoff i (v ++ σ) (w ++ σ) (rightContext D Sc cutoff σ v w f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul a f =>
    exact congrArg (fun g => a ⊗ₜ[k] g) (whiskerLeft_whiskerRight_cons D Sc i f σ)

private theorem affineRightContext_firstDotPower (σ : List I) (j : I) (v : List I)
    (n : ℕ) :
    affineRightContext D Sc σ (j :: v) (j :: v) (firstDotPower D Sc (j :: v) n) =
      firstDotPower D Sc (j :: (v ++ σ)) n := by
  have hp (w : List I) : firstDotPower D Sc w n = dotE D Sc w 0 ^ n := by
    simp only [dotE_pow, firstDotPower, List.map_replicate]
  change whiskerWordRingHom D Sc (j :: v) σ (firstDotPower D Sc (j :: v) n) = _
  rw [hp, map_pow]
  have hd : whiskerWordRingHom D Sc (j :: v) σ (dotE D Sc (j :: v) 0) =
      dotE D Sc (j :: (v ++ σ)) 0 :=
    dotE_whiskerRight D Sc (j :: v) σ 0 (by simp)
  rw [hd]
  exact (hp (j :: (v ++ σ))).symm

/-- Right extension preserves every first-position polynomial with full source coefficients. -/
theorem rightContext_deformedCyclotomic (σ : List I) (j : I) (v : List I)
    (N : ℕ) (c : Fin (N + 1) → SKM.SYM D k) :
    rightContext D Sc cutoff σ (j :: v) (j :: v)
      ((elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (j :: v) N c)) =
      (elvQuotientFunctor D Sc cutoff).map
        (deformedCyclotomic D Sc (j :: (v ++ σ)) N c) := by
  change rightContext D Sc cutoff σ (j :: v) (j :: v)
    (elvQuotientMap D Sc cutoff _ _ (deformedCyclotomic D Sc (j :: v) N c)) =
    elvQuotientMap D Sc cutoff _ _ (deformedCyclotomic D Sc (j :: (v ++ σ)) N c)
  unfold deformedCyclotomic
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [elvQuotientMap_source, elvQuotientMap_source, rightContext_tmul,
    affineRightContext_firstDotPower]

/-- The odd ELV and even cyclotomic relations both retain their coefficients and cutoff. -/
theorem rightContext_relation (σ : List I) (j : I) (v : List I) :
    rightContext D Sc cutoff σ (j :: v) (j :: v) (relation D Sc cutoff j v) =
      relation D Sc cutoff j (v ++ σ) := by
  unfold relation
  split_ifs with hj
  · exact rightContext_deformedCyclotomic D Sc cutoff σ j v (cutoff j)
      (SKM.SYM.elvMonicCoefficient D k ⟨j, hj⟩ (cutoff j))
  · exact rightContext_deformedCyclotomic D Sc cutoff σ j v (cutoff j)
      (SKM.SYM.evenMonicCoefficient D k j (cutoff j))

/-- Adjoining an arbitrary spectator context preserves the two-sided old ideal. -/
theorem ideal_rightContext (σ : List I) {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ ideal D Sc cutoff v w) :
    rightContext D Sc cutoff σ v w f ∈ ideal D Sc cutoff (v ++ σ) (w ++ σ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, t, a, b, rfl⟩ := hf
    rw [rightContext_comp, rightContext_comp, rightContext_relation]
    exact Submodule.subset_span ⟨j, t ++ σ,
      rightContext D Sc cutoff σ v (j :: t) a,
      rightContext D Sc cutoff σ (j :: t) w b, rfl⟩
  | zero => simpa only [map_zero] using (ideal D Sc cutoff (v ++ σ) (w ++ σ)).zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [map_smul] using Submodule.smul_mem _ c hf

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Scalar images of the actual ELV dot polynomials

The polynomial below records the chosen scalar coefficient images. This module
computes the actual signed specialization on every strand. Identifying these
coefficients with the prescribed binomial probe remains a separate calculation.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.SKM.SYM
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (values : I × ℕ → k)
  (hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0)

/-- The ordinary polynomial whose coefficients are the chosen scalar images. -/
def scalarCoefficientPolynomial (N : ℕ) (c : Fin (N+1) → SKM.SYM D k) :
    Polynomial k :=
  ∑ j, Polynomial.C (scalarEvaluation D values (c j)) * Polynomial.X ^ j.val

theorem elvAffineScalarSpecialization_dotPolynomial
    (w : List I) (r N : ℕ) (c : Fin (N+1) → SKM.SYM D k) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (coefficientDotPolynomial D Sc w r N c)) =
        Polynomial.aeval (dotE D Sc w r)
          (scalarCoefficientPolynomial D values N c) := by
  simp only [coefficientDotPolynomial, scalarCoefficientPolynomial, map_sum, Functor.map_sum,
    elvAffineScalarSpecialization_source, map_mul, Polynomial.aeval_C, map_pow,
    Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- The odd first-strand generator maps to its literal ordinary scalar polynomial. -/
theorem elvAffineScalarSpecialization_elvCyclotomic
    (i : {i : I // D.parity i = 1}) (tail : List I) (N : ℕ) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (elvCyclotomic D Sc i tail N)) =
        Polynomial.aeval (dotE D Sc (i.1 :: tail) 0)
          (scalarCoefficientPolynomial D values N (elvMonicCoefficient D k i N)) := by
  rw [← elvDotPolynomial_first]
  exact elvAffineScalarSpecialization_dotPolynomial D Sc cutoff values hvalues
    (i.1 :: tail) 0 N (elvMonicCoefficient D k i N)

/-- The same scalar polynomial formula for the original first-dot presentation. -/
theorem elvAffineScalarSpecialization_deformedCyclotomic
    (w : List I) (N : ℕ) (c : Fin (N+1) → SKM.SYM D k) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (deformedCyclotomic D Sc w N c)) =
        Polynomial.aeval (dotE D Sc w 0)
          (scalarCoefficientPolynomial D values N c) := by
  have hp : deformedCyclotomic D Sc w N c = coefficientDotPolynomial D Sc w 0 N c := by
    unfold deformedCyclotomic coefficientDotPolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [dotE_pow, firstDotPower, List.map_replicate]
  rw [hp]
  exact elvAffineScalarSpecialization_dotPolynomial D Sc cutoff values hvalues w 0 N c

/-- The actual even-colour first-strand relation has the corresponding scalar image. -/
theorem elvAffineScalarSpecialization_evenCyclotomic
    (i : I) (tail : List I) (N : ℕ) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (evenCyclotomic D Sc i tail N)) =
        Polynomial.aeval (dotE D Sc (i :: tail) 0)
          (scalarCoefficientPolynomial D values N (evenMonicCoefficient D k i N)) :=
  elvAffineScalarSpecialization_deformedCyclotomic D Sc cutoff values hvalues
    (i :: tail) N (evenMonicCoefficient D k i N)

/-- Appending spectator strands commutes with actual scalar specialization.
This supplies the append-range compatibility before quotient descent. -/
theorem elvAffineScalarSpecialization_rightContext
    (σ v w : List I) (f : ELVOld.hom D Sc cutoff v w) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (ELVOld.rightContext D Sc cutoff σ v w f) =
        ELVOld.affineRightContext D Sc σ v w
          ((elvAffineScalarSpecialization D Sc cutoff values hvalues).map f) := by
  let F : ELVOld.hom D Sc cutoff v w →ₗ[k]
      ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :=
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).toFunctor.mapLinearMap k
  let G : ELVOld.hom D Sc cutoff (v ++ σ) (w ++ σ) →ₗ[k]
      ((pres D Sc).obj (ob D (v ++ σ)) ⟶ (pres D Sc).obj (ob D (w ++ σ))) :=
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).toFunctor.mapLinearMap k
  change G (ELVOld.rightContext D Sc cutoff σ v w f) =
    ELVOld.affineRightContext D Sc σ v w (F f)
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul a f =>
    change (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (BoxProd.tmulHom
        (X := ELVOld.obj D Sc cutoff (v ++ σ))
        (Y := ELVOld.obj D Sc cutoff (w ++ σ))
        (SuperalgebraCat.ofElem a) (ELVOld.affineRightContext D Sc σ v w f)) =
      ELVOld.affineRightContext D Sc σ v w
        ((elvAffineScalarSpecialization D Sc cutoff values hvalues).map
          (BoxProd.tmulHom
            (X := ELVOld.obj D Sc cutoff v) (Y := ELVOld.obj D Sc cutoff w)
            (SuperalgebraCat.ofElem a) f))
    rw [elvAffineScalarSpecialization_tmul, elvAffineScalarSpecialization_tmul]
    exact (map_smul (ELVOld.affineRightContext D Sc σ v w) _ _).symm

end OddMath.QuiverHecke
end

end
