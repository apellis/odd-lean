import OddMath.QuiverHecke.CyclotomicAction.ProbeScalarModules
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.MixedRelations
import OddMath.SKM.BWWPureNilpotent
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.CyclotomicAction.PrefixScalarRelations
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.Algebra.SupermoduleIsoOfBijectiveTotals
import OddMath.QuiverHecke.CyclotomicAction.ContentAppend

/-!
# Probe mixed

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Tensor formulas for the scalar quotient induction comparison
The canonical unit and counit formulas compute the already constructed
comparison. The exact module restriction equality contributes identity
in parity zero and zero in parity one.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u
section Components
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

theorem scalarModuleEqToHom_app {F G : Superfunctor k C (SVec k)} (h : F = G)
    (p : ZMod 2) (v : C) :
    (eqToHom h : F ⟶ G).app p v =
      if p = 0 then eqToHom (congrArg (fun N : Superfunctor k C (SVec k) => N.obj v) h) else 0 := by
  subst G
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp only [eqToHom_refl, Superfunctor.id_app_zero, ↓reduceIte]
  · simp only [eqToHom_refl, Superfunctor.id_app_one, one_ne_zero, ↓reduceIte]

private theorem scalarTensorIdentityAddZero
    {D' : Type u} [Category.{u} D'] [Preadditive D'] [Linear k D'] (J : C ⥤ D')
    (N : Superfunctor k C (SVec k)) (v : C) (w : D')
    (g h : J.obj v ⟶ w) (b : N.obj v) :
    ELV.BalancedInduction.tensor J N.toFunctor v g ((LinearMap.id : N.obj v →ₗ[k] N.obj v) b) +
      ELV.BalancedInduction.tensor J N.toFunctor v h ((0 : N.obj v →ₗ[k] N.obj v) b) =
        ELV.BalancedInduction.tensor J N.toFunctor v g b := by
  rw [LinearMap.id_apply, LinearMap.zero_apply,
    ELV.BalancedInduction.tensor_zero_right, add_zero]

end Components

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν

@[simp] theorem probeRestrictionEqToIso_hom_app
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) (p : ZMod 2)
    (v : ELV.OldContentCategory D Sc cut ν) :
    (eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)).hom.app p v =
      if p = 0 then LinearMap.id else 0 := by
  rw [eqToIso.hom, scalarModuleEqToHom_app]
  simp only [eqToHom_refl]
  rfl

theorem probeQuotientCounitIso_inv_total
    (M : Superfunctor k (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))
    (w : OrdinaryContentCategory D Sc a ν) :
    (probeQuotientCounitIso D Sc m ν M).inv.total w =
      ELV.BalancedInduction.unit Q (Q ⋙ M.toFunctor) (probeOrdinaryOldObject D Sc m ν w) :=
  ELV.moduleIsoOfEvenNatIso_inv_total _ _ _ _ _ w

/-- The inverse comparison is the literal unit tensor on the same old module vector. -/
theorem probeQuotientInducedModuleIso_inv_tensor
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (w : OrdinaryContentCategory D Sc a ν) (b : N.obj (probeOrdinaryOldObject D Sc m ν w)) :
    (probeQuotientInducedModuleIso D Sc m ν N hN).inv.total w b =
      ELV.BalancedInduction.tensor Q N.toFunctor
        (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b := by
  let S := probeOrdinaryModuleSuperfunctor D Sc m ν N hN
  let u := eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)
  let c := probeQuotientCounitIso D Sc m ν S
  let IQ := ELV.BalancedInduction.induction (k := k) Q
  have hc : c.inv.total w b =
      ELV.BalancedInduction.tensor Q (probeOrdinaryRestriction D Sc m ν S).toFunctor
        (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b := by
    rw [probeQuotientCounitIso_inv_total]
    rfl
  have ht : (probeQuotientInducedModuleIso D Sc m ν N hN).inv.total w =
      (IQ.map u.hom).total w ∘ₗ c.inv.total w := by
    change (c.inv ≫ IQ.map u.hom).total w = _
    exact Superfunctor.comp_total _ _ w
  have hv : (probeQuotientInducedModuleIso D Sc m ν N hN).inv.total w b =
      (IQ.map u.hom).total w (c.inv.total w b) :=
    congrArg (fun f : S.obj w →ₗ[k] ELV.BalancedInduction.Obj Q N.toFunctor w => f b) ht
  refine hv.trans ?_
  refine (congrArg ((IQ.map u.hom).total w) hc).trans ?_
  change (ELV.BalancedInduction.moduleMap Q u.hom).total w
    (ELV.BalancedInduction.tensor Q (probeOrdinaryRestriction D Sc m ν S).toFunctor
      (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b) = _
  refine (ELV.BalancedInduction.moduleMap_total_tensor Q u.hom w
    (probeOrdinaryOldObject D Sc m ν w)
    (show (Q).obj (probeOrdinaryOldObject D Sc m ν w) ⟶ w from 𝟙 w) b).trans ?_
  simp only [u, probeRestrictionEqToIso_hom_app, ↓reduceIte, one_ne_zero]
  exact scalarTensorIdentityAddZero Q N (probeOrdinaryOldObject D Sc m ν w) w
    (show (Q).obj (probeOrdinaryOldObject D Sc m ν w) ⟶ w from 𝟙 w)
    (show (Q).obj (probeOrdinaryOldObject D Sc m ν w) ⟶ w from twist k 1 (𝟙 w)) b

end OddMath.QuiverHecke
end

end

section

/-! # Direct units from rectangular probe crossings

Both signed dot slides and the quadratic remainder give left and right
inverses in the actual source word corner. Finite-dimensionality is not
used. The explicit quadratic remainder and slide hypotheses remain to be
instantiated for the actual distinct-colour crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

/-- Travel from the source word through a target-corner element and back.
The result lies in the literal source corner by the crossing supports. -/
def cyclotomicWordEntry_sandwich {n : ℕ} (s t : Word I (n+1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t)
    (g : wordObj D Sc t ⟶ wordObj D Sc s)
    (w : CyclotomicWordCorner D Sc a t) : CyclotomicWordCorner D Sc a s :=
  ⟨cyclotomicWordEntry D Sc a t s g * w.val *
      cyclotomicWordEntry D Sc a s t f, by
    apply (Subsemigroup.mem_corner_iff (cyclotomicWordIdempotent_idem D Sc a s)).mpr
    constructor
    · rw [← mul_assoc, ← mul_assoc, cyclotomicWordEntry_left_support]
    · rw [mul_assoc, cyclotomicWordEntry_right_support]⟩

/-- Separate left and right positive-dot remainders suffice; they need not
coincide or commute with the following dot. -/
theorem cyclotomicWordEntry_distinct_isUnit_twoRemainders {n : ℕ} (s t : Word I (n+1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t)
    (g : wordObj D Sc t ⟶ wordObj D Sc s)
    (v : CyclotomicWordCorner D Sc a s) (w : CyclotomicWordCorner D Sc a t)
    (lead Rright Rleft : CyclotomicWordCorner D Sc a s)
    (hw : IsUnit w) (hlead : IsUnit lead)
    (slide : w.val * cyclotomicWordEntry D Sc a s t f =
      cyclotomicWordEntry D Sc a s t f * v.val)
    (slide' : v.val * cyclotomicWordEntry D Sc a t s g =
      cyclotomicWordEntry D Sc a t s g * w.val)
    (quadratic_right : cyclotomicWordEntry D Sc a t s g * cyclotomicWordEntry D Sc a s t f =
      lead.val + Rright.val * v.val)
    (quadratic_left : cyclotomicWordEntry D Sc a t s g * cyclotomicWordEntry D Sc a s t f =
      lead.val + v.val * Rleft.val) : IsUnit v := by
  rcases hw with ⟨W, rfl⟩
  rcases hlead with ⟨U, rfl⟩
  let Cr := cyclotomicWordEntry_sandwich D Sc a s t f g (↑(W⁻¹)) - Rright
  let Cl := cyclotomicWordEntry_sandwich D Sc a s t f g (↑(W⁻¹)) - Rleft
  have hwi : W.inv.val * W.val.val = cyclotomicWordIdempotent D Sc a t :=
    congrArg (fun z : CyclotomicWordCorner D Sc a t => z.val) W.inv_val
  have hiw : W.val.val * W.inv.val = cyclotomicWordIdempotent D Sc a t :=
    congrArg (fun z : CyclotomicWordCorner D Sc a t => z.val) W.val_inv
  have hCv : Cr * v = U.val := by
    apply Subtype.ext
    change (cyclotomicWordEntry D Sc a t s g * W.inv.val *
      cyclotomicWordEntry D Sc a s t f - Rright.val) * v.val = U.val.val
    calc
      _ = cyclotomicWordEntry D Sc a t s g *
          (W.inv.val * (cyclotomicWordEntry D Sc a s t f * v.val)) -
          Rright.val * v.val := by noncomm_ring
      _ = cyclotomicWordEntry D Sc a t s g *
          (W.inv.val * (W.val.val * cyclotomicWordEntry D Sc a s t f)) -
          Rright.val * v.val := by rw [slide]
      _ = cyclotomicWordEntry D Sc a t s g * cyclotomicWordEntry D Sc a s t f -
          Rright.val * v.val := by
        rw [← mul_assoc W.inv.val, hwi, cyclotomicWordEntry_left_support]
      _ = U.val.val := by rw [quadratic_right]; noncomm_ring
  have hvC : v * Cl = U.val := by
    apply Subtype.ext
    change v.val * (cyclotomicWordEntry D Sc a t s g * W.inv.val *
      cyclotomicWordEntry D Sc a s t f - Rleft.val) = U.val.val
    calc
      _ = (v.val * cyclotomicWordEntry D Sc a t s g) * W.inv.val *
          cyclotomicWordEntry D Sc a s t f - v.val * Rleft.val := by noncomm_ring
      _ = (cyclotomicWordEntry D Sc a t s g * W.val.val) * W.inv.val *
          cyclotomicWordEntry D Sc a s t f - v.val * Rleft.val := by rw [slide']
      _ = cyclotomicWordEntry D Sc a t s g * cyclotomicWordEntry D Sc a s t f -
          v.val * Rleft.val := by
        rw [mul_assoc (cyclotomicWordEntry D Sc a t s g), hiw,
          cyclotomicWordEntry_right_support]
      _ = U.val.val := by rw [quadratic_left]; noncomm_ring
  let l := U.inv * Cr
  let r := Cl * U.inv
  have hl : l * v = 1 := by
    change (U.inv * Cr) * v = 1
    rw [mul_assoc, hCv, U.inv_val]
  have hr : v * r = 1 := by
    change v * (Cl * U.inv) = 1
    rw [← mul_assoc, hvC, U.val_inv]
  have hlr : l = r := by
    calc
      l = l * (v * r) := by rw [hr, mul_one]
      _ = (l * v) * r := (mul_assoc _ _ _).symm
      _ = r := by rw [hl, one_mul]
  exact ⟨⟨v, r, hr, by rw [← hlr]; exact hl⟩, rfl⟩

end OddMath.QuiverHecke
end

end

section

/-! # Literal crossings of distinct probe words

These are the actual affine morphisms between the two word objects, together
with their signed dot slides and quadratic formula. They precede the source
and target corner comparison; no invertibility assumption is used here.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

def probeMixedWord (pre post : List I) (i j : I) :
    Word I ((pre.length+post.length+1)+1) :=
  ⟨pre ++ [i,j] ++ post, by simp; omega⟩

theorem probeMixedChain (pre post : List I) (i j : I) :
    SChain (pre ++ [i,j] ++ post)
      (pl (pre ++ [i,j] ++ post) [.cross pre.length]) (pre ++ [j,i] ++ post) :=
  sChain_ofShape' pre post (.cross i j) rfl rfl rfl

def probeMixedCross (pre post : List I) (i j : I) :
    (pres D Sc).obj (ob D (pre ++ [i,j] ++ post)) ⟶
      (pres D Sc).obj (ob D (pre ++ [j,i] ++ post)) :=
  cl D Sc _ _ [.cross pre.length] (probeMixedChain pre post i j)

theorem probeMixedCross_slide (pre post : List I) (i j : I) (hij : i ≠ j) :
    probeMixedCross D Sc pre post i j ≫
      dotE D Sc (pre ++ [j,i] ++ post) pre.length =
      SKM.zsign k (D.parity i * D.parity j) •
        (dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) ≫
          probeMixedCross D Sc pre post i j) := by
  change cl D Sc _ _ [.cross pre.length] _ ≫ dotE D Sc _ _ = _
  rw [dotE_eq, dotE_eq]
  simp only [probeMixedCross, cl_comp']
  exact slide_right_ne D Sc pre post i j hij _ _

/-- The reverse crossing supplies the second slide required by the direct
rectangular unit proof, with exactly the same sign. -/
theorem probeMixedCross_slide_reverse (pre post : List I) (i j : I) (hij : i ≠ j) :
    dotE D Sc (pre ++ [j,i] ++ post) pre.length ≫
      probeMixedCross D Sc pre post j i =
      SKM.zsign k (D.parity i * D.parity j) •
        (probeMixedCross D Sc pre post j i ≫
          dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)) := by
  change dotE D Sc _ _ ≫ cl D Sc _ _ [.cross pre.length] _ = _
  rw [dotE_eq, dotE_eq]
  simp only [probeMixedCross, cl_comp']
  simpa only [List.cons_append, List.nil_append, mul_comm] using slide_left_ne D Sc pre post j i hij.symm
    (sChain_comp (sChain_pl _ [.dot pre.length]) (probeMixedChain pre post j i))
    (sChain_comp (probeMixedChain pre post j i)
      (sChain_pl _ [.dot (pre.length+1)]))

theorem probeMixedCross_quadratic_zero (pre post : List I) (i j : I)
    (hij : i ≠ j) (hd : D.d i j = 0) :
    probeMixedCross D Sc pre post i j ≫ probeMixedCross D Sc pre post j i =
      (Sc.t i j : k) • 𝟙 _ := by
  simp only [probeMixedCross, cl_comp']
  exact cross_cross_ne_zero D Sc pre post hij hd _

theorem probeMixedCross_quadratic (pre post : List I) (i j : I)
    (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    probeMixedCross D Sc pre post i j ≫ probeMixedCross D Sc pre post j i =
      (∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
        Sc.s i j p q • (dotE D Sc (pre ++ [i,j] ++ post) pre.length ^ p *
          dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) ^ q)) +
      ((Sc.t i j : k) • dotE D Sc (pre ++ [i,j] ++ post) pre.length ^ D.dn i j +
        (Sc.t j i : k) • dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) ^ D.dn j i) := by
  simp only [probeMixedCross, cl_comp']
  exact cross_cross_ne D Sc pre post hij hd _

/-- The two literal dots obey the prescribed supercommutation sign. -/
theorem probeMixedDots_slide (pre post : List I) (i j : I) :
    dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) *
      dotE D Sc (pre ++ [i,j] ++ post) pre.length =
      SKM.zsign k (D.parity i * D.parity j) •
        (dotE D Sc (pre ++ [i,j] ++ post) pre.length *
          dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)) := by
  have h := genE_interchange D Sc pre [] post (.dot i) (.dot j) rfl rfl
    (w := pre ++ [i,j] ++ post) (by simp [Shape.dom, List.append_assoc])
    (p := pre.length) (q := pre.length+1) rfl (by simp [Shape.dom])
  simpa only [Shape.parity, PG.ofShape] using h

end OddMath.QuiverHecke
end

end

section

/-! # Actual rectangular corner relations for mixed probe dots

The affine slides and positive-dot remainders are compared with the literal
word-corner maps. These comparisons use the existing cyclotomic algebra,
including its actual finite Hom-matrix multiplication.

The hypothesis `Sc.PureNilpotent` (as `[Fact Sc.PureNilpotent]` on the dot unit) is a
route-only intermediate hypothesis for parameters with pure terms: homogeneous parameters
supply it (`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

theorem cyclotomicWordEntry_smul {n : ℕ} (s t : Word I (n+1)) (c : k)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    cyclotomicWordEntry D Sc a s t (c • f) =
      c • cyclotomicWordEntry D Sc a s t f := by
  unfold cyclotomicWordEntry
  rw [FiniteHomMatrix.single_smul, map_smul]

abbrev probeMixedCornerDot (pre post : List I) (i j : I) (r : ℕ) :=
  cyclotomicWordEnd D Sc a (probeMixedWord pre post i j)
    (dotE D Sc (pre ++ [i,j] ++ post) r)

def probeMixedEntry (pre post : List I) (i j : I) :
    CyclotomicAlgebra D Sc a (pre.length+post.length+1) :=
  cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
    (probeMixedWord pre post j i) (probeMixedCross D Sc pre post i j)

theorem probeMixedCorner_slide (pre post : List I) (i j : I) (hij : i ≠ j) :
    (probeMixedCornerDot D Sc a pre post j i pre.length).val *
        probeMixedEntry D Sc a pre post i j =
      SKM.zsign k (D.parity i * D.parity j) •
        (probeMixedEntry D Sc a pre post i j *
          (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val) := by
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
      (probeMixedWord pre post j i) (dotE D Sc (pre ++ [j,i] ++ post) pre.length) *
      cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post j i) (probeMixedCross D Sc pre post i j) = _
  rw [← cyclotomicWordEntry_comp]
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
      (probeMixedWord pre post j i) _ =
    SKM.zsign k (D.parity i * D.parity j) •
      (cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post j i) (probeMixedCross D Sc pre post i j) *
       cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post i j) (dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)))
  rw [← cyclotomicWordEntry_comp, ← cyclotomicWordEntry_smul]
  exact congrArg (cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
    (probeMixedWord pre post j i)) (probeMixedCross_slide D Sc pre post i j hij)

theorem probeMixedCorner_slide_reverse (pre post : List I) (i j : I) (hij : i ≠ j) :
    probeMixedEntry D Sc a pre post j i *
        (probeMixedCornerDot D Sc a pre post j i pre.length).val =
      SKM.zsign k (D.parity i * D.parity j) •
        ((probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val *
          probeMixedEntry D Sc a pre post j i) := by
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
      (probeMixedWord pre post i j) (probeMixedCross D Sc pre post j i) *
      cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
        (probeMixedWord pre post j i) (dotE D Sc (pre ++ [j,i] ++ post) pre.length) = _
  rw [← cyclotomicWordEntry_comp]
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
      (probeMixedWord pre post i j) _ =
    SKM.zsign k (D.parity i * D.parity j) •
      (cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post i j) (dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)) *
       cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
        (probeMixedWord pre post i j) (probeMixedCross D Sc pre post j i))
  rw [← cyclotomicWordEntry_comp, ← cyclotomicWordEntry_smul]
  exact congrArg (cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
    (probeMixedWord pre post i j)) (probeMixedCross_slide_reverse D Sc pre post i j hij)

/-- The scalars act on a word corner through its identity: `c ↦ q(c • 1)`. -/
def cyclotomicWordCornerAlgebraMap {n : ℕ} (s : Word I (n+1)) :
    k →+* CyclotomicWordCorner D Sc a s :=
  (cyclotomicWordEnd D Sc a s).comp (algebraMap k (End (wordObj D Sc s)))

theorem cyclotomicWordCornerAlgebraMap_val {n : ℕ} (s : Word I (n+1)) (c : k) :
    (cyclotomicWordCornerAlgebraMap D Sc a s c).val =
      c • (1 : CyclotomicWordCorner D Sc a s).val := by
  change cyclotomicWordEntry D Sc a s s (algebraMap k (End (wordObj D Sc s)) c) = _
  rw [Algebra.algebraMap_eq_smul_one, cyclotomicWordEntry_smul]
  rfl

theorem cyclotomicWordCornerAlgebraMap_commute {n : ℕ} (s : Word I (n+1)) (c : k)
    (r : CyclotomicWordCorner D Sc a s) :
    cyclotomicWordCornerAlgebraMap D Sc a s c * r = r * cyclotomicWordCornerAlgebraMap D Sc a s c := by
  apply Subtype.ext
  change (cyclotomicWordCornerAlgebraMap D Sc a s c).val * r.val =
    r.val * (cyclotomicWordCornerAlgebraMap D Sc a s c).val
  rw [cyclotomicWordCornerAlgebraMap_val, smul_mul_assoc, mul_smul_comm]
  have h1 : (1 : CyclotomicWordCorner D Sc a s).val * r.val = r.val :=
    congrArg Subtype.val (one_mul r)
  have h2 : r.val * (1 : CyclotomicWordCorner D Sc a s).val = r.val :=
    congrArg Subtype.val (mul_one r)
  rw [h1, h2]

/-- The word corner as an algebra over the ground ring. -/
abbrev cyclotomicWordCornerAlgebra {n : ℕ} (s : Word I (n+1)) :
    Algebra k (CyclotomicWordCorner D Sc a s) :=
  (cyclotomicWordCornerAlgebraMap D Sc a s).toAlgebra'
    (cyclotomicWordCornerAlgebraMap_commute D Sc a s)

/-- Actual connected Q remainders in the source corner. The leading part `Qᵢⱼ(u, 0)` is a unit
because the preceding source dot `u` is a unit and the pure coefficients lie in a nilpotent
ideal (`ScalarData.PureNilpotent`; for parameters without pure terms the zero ideal). -/
theorem probeMixedCorner_remainders_connected (hP : Sc.PureNilpotent) (pre post : List I)
    (i j : I) (hij : i ≠ j) (hd : D.d i j ≠ 0)
    (hu : IsUnit (probeMixedCornerDot D Sc a pre post i j pre.length)) :
    ∃ U Rright Rleft : CyclotomicWordCorner D Sc a (probeMixedWord pre post i j),
      IsUnit U ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + Rright.val * (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val * Rleft.val := by
  let s := probeMixedWord pre post i j
  let _ : Algebra k (CyclotomicWordCorner D Sc a s) := cyclotomicWordCornerAlgebra D Sc a s
  let q : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post))) →+* CyclotomicWordCorner D Sc a s :=
    cyclotomicWordEnd D Sc a s
  let u := dotE D Sc (pre ++ [i,j] ++ post) pre.length
  let v := dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)
  let ε := SKM.zsign k (D.parity i * D.parity j)
  have hqs : ∀ (c : k) (f : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))),
      q (c • f) = c • q f := by
    intro c f
    rw [Algebra.smul_def c f, map_mul, Algebra.smul_def c (q f)]
    rfl
  have he : ε * ε = 1 := zsign_mul_self _
  have huv : u * v = ε • (v * u) := by
    have h := probeMixedDots_slide D Sc pre post i j
    change v * u = ε • (u * v) at h
    rw [h, smul_smul, he, one_smul]
  have hslide : ∀ p : ℕ, q u ^ p * q v = ε ^ p • (q v * q u ^ p) := by
    intro p
    rw [← map_pow, ← map_mul, ← map_mul, ← hqs]
    congr 1
    induction p with
    | zero => simp
    | succ p ih =>
      rw [pow_succ, mul_assoc, huv, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc,
        smul_smul, mul_assoc, ← pow_succ']
  obtain ⟨U, Rr, Rl, hU, hr, hl⟩ :=
    hP.exists_isUnit_quad_remainders hij hd (x := q u) (y := q v) hu ε hslide
  have hQ := probeMixedCross_quadratic D Sc pre post i j hij hd
  have hBA : probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
      (q (probeMixedCross D Sc pre post i j ≫ probeMixedCross D Sc pre post j i)).val := by
    unfold probeMixedEntry
    rw [← cyclotomicWordEntry_comp]
    rfl
  have hq : q (probeMixedCross D Sc pre post i j ≫ probeMixedCross D Sc pre post j i) =
      (Sc.t i j : k) • q u ^ D.dn i j + (Sc.t j i : k) • q v ^ D.dn j i +
        ∑ p ∈ Finset.range (D.dn i j), ∑ q' ∈ Finset.range (D.dn j i),
          Sc.s i j p q' • (q u ^ p * q v ^ q') := by
    rw [hQ]
    simp only [map_add, map_sum, hqs, map_mul, map_pow]
    abel
  refine ⟨U, Rr, Rl, hU, ?_, ?_⟩
  · rw [hBA, hq, hr]
    rfl
  · rw [hBA, hq, hl]
    rfl

/-- The disconnected quadratic supplies the same two remainder statements,
with zero remainders and its single scalar unit leading term. -/
theorem probeMixedCorner_remainders (hP : Sc.PureNilpotent) (pre post : List I) (i j : I)
    (hij : i ≠ j)
    (hu : IsUnit (probeMixedCornerDot D Sc a pre post i j pre.length)) :
    ∃ U Rright Rleft : CyclotomicWordCorner D Sc a (probeMixedWord pre post i j),
      IsUnit U ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + Rright.val * (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val * Rleft.val := by
  by_cases hd : D.d i j = 0
  · let s := probeMixedWord pre post i j
    let q : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post))) →+* CyclotomicWordCorner D Sc a s :=
      cyclotomicWordEnd D Sc a s
    let c := algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))) (Sc.t i j : k)
    have hBA : probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        (q c).val := by
      unfold probeMixedEntry
      rw [← cyclotomicWordEntry_comp]
      change (q (probeMixedCross D Sc pre post i j ≫
        probeMixedCross D Sc pre post j i)).val = (q c).val
      rw [probeMixedCross_quadratic_zero D Sc pre post i j hij hd]
      change (q ((Sc.t i j : k) • (1 : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))))).val =
        (q (algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))) (Sc.t i j : k))).val
      rw [Algebra.algebraMap_eq_smul_one]
    refine ⟨q c, 0, 0,
      (((Sc.t i j).isUnit.map (algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))))).map q), ?_, ?_⟩
    · change probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        (q c).val + (0 : CyclotomicAlgebra D Sc a (pre.length+post.length+1)) *
          (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val
      rw [zero_mul, add_zero]
      exact hBA
    · change probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        (q c).val + (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val *
          (0 : CyclotomicAlgebra D Sc a (pre.length+post.length+1))
      rw [mul_zero, add_zero]
      exact hBA
  · exact probeMixedCorner_remainders_connected D Sc a hP pre post i j hij hd hu

/-- The actual distinct-colour probe step: preceding dots in the source and
swapped target corners are units, hence so is the following source dot.
All signed slides and Q factorization premises are discharged internally. -/
theorem probeMixedCorner_dot_isUnit [hP : Fact Sc.PureNilpotent] (pre post : List I) (i j : I)
    (hij : i ≠ j)
    (hu : IsUnit (probeMixedCornerDot D Sc a pre post i j pre.length))
    (hw : IsUnit (probeMixedCornerDot D Sc a pre post j i pre.length)) :
    IsUnit (probeMixedCornerDot D Sc a pre post i j (pre.length+1)) := by
  let s := probeMixedWord pre post i j
  let t := probeMixedWord pre post j i
  let q : End ((pres D Sc).obj (ob D (pre ++ [j,i] ++ post))) →+* CyclotomicWordCorner D Sc a t :=
    cyclotomicWordEnd D Sc a t
  let ε := SKM.zsign k (D.parity i * D.parity j)
  let v := probeMixedCornerDot D Sc a pre post i j (pre.length+1)
  let A := probeMixedEntry D Sc a pre post i j
  let B := probeMixedEntry D Sc a pre post j i
  let w := probeMixedCornerDot D Sc a pre post j i pre.length
  let W := q (ε • dotE D Sc (pre ++ [j,i] ++ post) pre.length)
  have he : ε * ε = 1 := zsign_mul_self _
  have hε : IsUnit ε := ⟨⟨ε, ε, he, he⟩, rfl⟩
  have hW : IsUnit W := by
    change IsUnit (q (ε • dotE D Sc (pre ++ [j,i] ++ post) pre.length))
    rw [Algebra.smul_def, map_mul]
    exact ((hε.map (algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [j,i] ++ post)))))).map q).mul hw
  have hWval : W.val = ε • w.val := by
    change cyclotomicWordEntry D Sc a t t
      (ε • dotE D Sc (pre ++ [j,i] ++ post) pre.length) =
      ε • cyclotomicWordEntry D Sc a t t
        (dotE D Sc (pre ++ [j,i] ++ post) pre.length)
    exact cyclotomicWordEntry_smul D Sc a t t ε _
  have hs := probeMixedCorner_slide D Sc a pre post i j hij
  change w.val * A = ε • (A * v.val) at hs
  have hs' := probeMixedCorner_slide_reverse D Sc a pre post i j hij
  change B * w.val = ε • (v.val * B) at hs'
  have hslide : W.val * A = A * v.val := by
    rw [hWval, smul_mul_assoc, hs, smul_smul, he, one_smul]
  have hslide' : v.val * B = B * W.val := by
    symm
    rw [hWval, mul_smul_comm, hs', smul_smul, he, one_smul]
  obtain ⟨U, Rright, Rleft, hU, hr, hl⟩ :=
    probeMixedCorner_remainders D Sc a hP.out pre post i j hij hu
  exact cyclotomicWordEntry_distinct_isUnit_twoRemainders D Sc a s t
    (probeMixedCross D Sc pre post i j) (probeMixedCross D Sc pre post j i)
    v W U Rright Rleft hW hU hslide hslide' hr hl

end OddMath.QuiverHecke
end

end

section

/-! # Direct units in same-colour nilHecke probe blocks

The even intertwiner conjugates the two dots. The odd intertwiner square
and an inverse of the preceding dot construct a right inverse of the next dot;
existing kernel propagation makes this a two-sided inverse. Both arguments work
over every ring without finite-dimensionality.
-/
namespace OddMath.QuiverHecke.SignedNilHecke
variable {B : Type*} [Ring B]

theorem EvenTwo.isUnit_right_direct {u v T : B} (h : EvenTwo u v T) (hu : IsUnit u) :
    IsUnit v := by
  have hp : IsUnit (phiEven u v T) :=
    ⟨⟨phiEven u v T, phiEven u v T, h.phiEven_mul_phiEven, h.phiEven_mul_phiEven⟩, rfl⟩
  have he : phiEven u v T * u * phiEven u v T = v := by
    rw [mul_assoc, h.x_mul_phiEven, ← mul_assoc, h.phiEven_mul_phiEven, one_mul]
  rw [← he]
  exact (hp.mul hu).mul hp

/-- The odd intertwiner square supplies a right inverse; kernel propagation
then makes it a two-sided unit. No finite-dimensionality is required. -/
theorem OddTwo.isUnit_right_direct {u v T : B} (h : OddTwo u v T) (hu : IsUnit u) :
    IsUnit v := by
  rcases hu with ⟨U, rfl⟩
  let a : B := ↑(U⁻¹)
  let φ : B := phiOdd (U : B) v T
  have hua : (U : B) * a = 1 := U.val_inv
  have hphi : v * φ * a = -φ := by
    have he := congrArg (fun z : B => z * a) h.x_succ_mul_phiOdd
    change (v * φ) * a = -(φ * (U : B)) * a at he
    simpa only [neg_mul, mul_assoc, hua, mul_one] using he
  have hs : φ * φ = (U : B) * U + v * v := by
    change phiOdd (U : B) v T * phiOdd (U : B) v T = _
    rw [h.phiOdd_mul_phiOdd]
    simp only [sub_mul, mul_sub, h.vu']
    noncomm_ring
  have hf : v * (-φ * a * φ - v) = (U : B) * U := by
    calc
      v * (-φ * a * φ - v) = -(v * φ * a) * φ - v * v := by noncomm_ring
      _ = φ * φ - v * v := by rw [hphi, neg_neg]
      _ = (U : B) * U := by rw [hs]; noncomm_ring
  have hr : v * ((-φ * a * φ - v) * (a * a)) = 1 := by
    rw [← mul_assoc, hf]
    calc
      ((U : B) * U) * (a * a) = (U : B) * ((U : B) * a) * a := by noncomm_ring
      _ = 1 := by rw [hua, mul_one, hua]
  have hinj := h.right_mul_injective (IsUnit.isUnit_iff_mulLeft_bijective.mp U.isUnit).1
  apply IsUnit.isUnit_iff_mulLeft_bijective.mpr
  refine ⟨hinj, ?_⟩
  intro z
  refine ⟨((-φ * a * φ - v) * (a * a)) * z, ?_⟩
  change v * (((-φ * a * φ - v) * (a * a)) * z) = z
  calc
    _ = (v * ((-φ * a * φ - v) * (a * a))) * z := (mul_assoc _ _ _).symm
    _ = z := by rw [hr, one_mul]

end OddMath.QuiverHecke.SignedNilHecke

namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

/-- The direct unit step in the actual word corner, for either parity. -/
theorem cyclotomicBlock_dot_isUnit (pre post : List I) (i : I)
    (hu : IsUnit (cyclotomicBlockDot D Sc a pre post i pre.length)) :
    IsUnit (cyclotomicBlockDot D Sc a pre post i (pre.length+1)) := by
  rcases StringDiagrams.Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · exact (cyclotomicBlock_evenTwo D Sc a pre post i hi).isUnit_right_direct hu
  · exact (cyclotomicBlock_oddTwo D Sc a pre post i hi).isUnit_right_direct hu

end OddMath.QuiverHecke

end

section

/-! # All-position units in the actual cofinal probe

Induction over positions uses both source and swapped word corners. Equal
colours use direct nilHecke units; distinct colours use the actual signed
slides and both Q remainders. The proof works over the original ground ring,
without finite-dimensionality, residue fields, or Nakayama descent.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I]

omit [Fintype I] in
private theorem probeWord_split_two {n : ℕ} (s : Word I (n+1))
    (r : ℕ) (hr : r+1 < n+1) :
    ∃ (pre : List I) (i j : I) (post : List I),
      pre.length = r ∧ s.val = pre ++ [i,j] ++ post := by
  have hdrop : 2 ≤ (s.val.drop r).length := by
    rw [List.length_drop, s.property]
    omega
  cases hd : s.val.drop r with
  | nil => simp [hd] at hdrop
  | cons i rest =>
    cases ht : rest with
    | nil => simp [hd, ht] at hdrop
    | cons j post =>
      refine ⟨s.val.take r, i, j, post, ?_, ?_⟩
      · rw [List.length_take, s.property, Nat.min_eq_left (by omega)]
      · have hs := List.take_append_drop r s.val
        rw [hd, ht] at hs
        simpa only [List.cons_append, List.nil_append, List.append_assoc] using hs.symm

/-- Every literal dot in every word corner of the prescribed cofinal probe
is a unit, directly over the given commutative ground ring. -/
theorem probeWord_dots_isUnit [Fact Sc.PureNilpotent] (m : I → ℕ) (n : ℕ) :
    ∀ r < n+1, ∀ s : Word I (n+1),
      IsUnit (cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m) s
        (dotE D Sc s.val r)) := by
  intro r
  induction r with
  | zero =>
    intro _ s
    exact probe_firstDot_isUnit D Sc m s
  | succ r ih =>
    intro hr s
    obtain ⟨pre, i, j, post, hpre, hs⟩ := probeWord_split_two s r hr
    have hn : n = pre.length + post.length + 1 := by
      have hlen := congrArg List.length hs
      rw [s.property] at hlen
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    subst n
    have hsword : s = probeMixedWord pre post i j := Subtype.ext hs
    subst s
    have hsrc := ih (by omega) (probeMixedWord pre post i j)
    have htgt := ih (by omega) (probeMixedWord pre post j i)
    rw [← hpre] at hsrc htgt ⊢
    by_cases hij : i = j
    · subst j
      exact cyclotomicBlock_dot_isUnit D Sc (probePolynomial (probeDotExponent D) m)
        pre post i hsrc
    · exact probeMixedCorner_dot_isUnit D Sc (probePolynomial (probeDotExponent D) m)
        pre post i j hij hsrc htgt

end OddMath.QuiverHecke
end

end

section

/-! # The literal ordinary word quotient is the actual probe word corner
The forward inclusion uses the existing matrix quotient. Reverse matrix-entry
membership proves injectivity; the existing affine corner range theorem
proves surjectivity. No alternate quotient model or flatness premise is used.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → Polynomial k) (ν : List I)

private def ordinaryWordCornerAdd {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν) :
    End (⟨s.val,hs⟩ : OrdinaryContentCategory D Sc a ν) →+ CyclotomicWordCorner D Sc a s :=
  QuotientAddGroup.lift (cycHom D Sc a s.val s.val).toAddSubgroup
    (cyclotomicWordEnd D Sc a s).toAddMonoidHom (by
      intro f hf
      apply Subtype.ext
      change cyclotomicMk D Sc a n (FiniteHomMatrix.single s s f) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (single_mem_cyclotomicIdeal D Sc a n s s hf))

/-- The existing quotient map, restricted to the literal unital word corner. -/
def ordinaryWordEndCornerMap {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν) :
    End (⟨s.val,hs⟩ : OrdinaryContentCategory D Sc a ν) →+* CyclotomicWordCorner D Sc a s where
  toFun := ordinaryWordCornerAdd D Sc a ν s hs
  map_one' := by
    change cyclotomicWordEnd D Sc a s 1 = 1
    exact map_one _
  map_zero' := map_zero (ordinaryWordCornerAdd D Sc a ν s hs)
  map_add' := map_add (ordinaryWordCornerAdd D Sc a ν s hs)
  map_mul' f g := by
    obtain ⟨f,rfl⟩ := (cycHom D Sc a s.val s.val).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc a s.val s.val).mkQ_surjective g
    change cyclotomicWordEnd D Sc a s (End.of f * End.of g) =
      cyclotomicWordEnd D Sc a s f * cyclotomicWordEnd D Sc a s g
    exact map_mul _ (End.of f) (End.of g)

@[simp] theorem ordinaryWordEndCornerMap_mk {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν)
    (f : End (wordObj D Sc s)) :
    ordinaryWordEndCornerMap D Sc a ν s hs
      (End.of ((cycHom D Sc a s.val s.val).mkQ f)) = cyclotomicWordEnd D Sc a s f := rfl

private theorem ordinaryWordEndCornerMap_zero {n : ℕ}
    (s : Word I (n+1)) (hs : s.val.Perm ν)
    (f : End (⟨s.val,hs⟩ : OrdinaryContentCategory D Sc a ν)) (hf : ordinaryWordEndCornerMap D Sc a ν s hs f = 0) : f = 0 := by
  obtain ⟨f,rfl⟩ := (cycHom D Sc a s.val s.val).mkQ_surjective f
  have hz := congrArg Subtype.val hf
  change cyclotomicMk D Sc a n (FiniteHomMatrix.single s s f) = 0 at hz
  have hi := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hc := (single_mem_cyclotomicIdeal_iff D Sc a n s s f).mp hi
  exact (Submodule.Quotient.mk_eq_zero _).mpr hc

theorem ordinaryWordEndCornerMap_injective {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν) :
    Function.Injective (ordinaryWordEndCornerMap D Sc a ν s hs) := by
  intro f g h
  apply sub_eq_zero.mp
  apply ordinaryWordEndCornerMap_zero D Sc a ν s hs
  rw [map_sub,h,sub_self]

theorem ordinaryWordEndCornerMap_surjective {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν) :
    Function.Surjective (ordinaryWordEndCornerMap D Sc a ν s hs) := by
  intro u
  obtain ⟨z,hz⟩ := Ideal.Quotient.mk_surjective u.val
  have hz' : cyclotomicMk D Sc a n z = u.val := hz
  let e : Hn D Sc (n+1) := Hn.wordIdempotent s
  have he : e * (e * z * e) * e = e * z * e := by
    calc
      e * (e * z * e) * e = (e*e) * z * (e*e) := by simp only [mul_assoc]
      _ = e * z * e := by dsimp only [e]; rw [Hn.wordIdempotent_sq]
  obtain ⟨f,hf⟩ := (Hn.mem_range_cornerInclusion_iff (D := D) (Sc := Sc) s (e*z*e)).mpr he
  refine ⟨End.of ((cycHom D Sc a s.val s.val).mkQ f), ?_⟩
  apply Subtype.ext
  change cyclotomicMk D Sc a n (Hn.cornerInclusion s f) = u.val
  rw [hf,map_mul,map_mul,hz']
  have hu := (Subsemigroup.mem_corner_iff (cyclotomicWordIdempotent_idem D Sc a s)).mp u.property
  change cyclotomicWordIdempotent D Sc a s * u.val * cyclotomicWordIdempotent D Sc a s = u.val
  rw [hu.1,hu.2]

/-- Actual ordinary quotient endomorphisms and the actual unital matrix word corner agree. -/
def ordinaryWordCornerEquiv {n : ℕ} (s : Word I (n+1)) (hs : s.val.Perm ν) :
    End (⟨s.val,hs⟩ : OrdinaryContentCategory D Sc a ν) ≃+* CyclotomicWordCorner D Sc a s :=
  RingEquiv.ofBijective (ordinaryWordEndCornerMap D Sc a ν s hs)
    ⟨ordinaryWordEndCornerMap_injective D Sc a ν s hs,
      ordinaryWordEndCornerMap_surjective D Sc a ν s hs⟩

@[simp] theorem ordinaryWordCornerEquiv_mk {n : ℕ}
    (s : Word I (n+1)) (hs : s.val.Perm ν) (f : End (wordObj D Sc s)) :
    ordinaryWordCornerEquiv D Sc a ν s hs (End.of ((cycHom D Sc a s.val s.val).mkQ f)) =
      cyclotomicWordEnd D Sc a s f := rfl

/-- The established all-position probe units are literal ordinary-category dot units. -/
theorem probeOrdinaryWordDot_isUnit [Fact Sc.PureNilpotent] (m : I → ℕ) {n : ℕ}
    (s : Word I (n+1)) (hs : s.val.Perm ν) (r : ℕ) (hr : r < n+1) :
    IsUnit (End.of ((cycHom D Sc (probePolynomial (probeDotExponent D) m) s.val s.val).mkQ
      (dotE D Sc s.val r)) :
        End (⟨s.val,hs⟩ : OrdinaryContentCategory D Sc (probePolynomial (probeDotExponent D) m) ν)) := by
  apply (MulEquiv.isUnit_map (ordinaryWordCornerEquiv D Sc (probePolynomial (probeDotExponent D) m) ν s hs)).mp
  rw [ordinaryWordCornerEquiv_mk]
  exact probeWord_dots_isUnit D Sc m n r hr s

end OddMath.QuiverHecke
end

end

section

/-! # Actual old append and dot under scalar probe specialization
These formulas compare the existing canonical old append and appended dot
with their literal ordinary probe images. The dot image is a unit in its
actual word corner at every height, including append from the vacuum.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k) [Fintype I]
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

omit [Fintype I] in
/-- Unit-coefficient affine arrows specialize to themselves. -/
theorem elvProbeScalarHom_affineUnit {v w : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    elvProbeScalarHom D m Sc v w (ELV.affineUnit D Sc cut v w f) = f := by
  change (elvAffineScalarSpecialization D Sc cut (probeScalarValues D m)
      (probeScalarValues_vanish D m)).map
    (BoxProd.tmulHom (X := ELV.obj D Sc cut v) (Y := ELV.obj D Sc cut w)
      (SuperalgebraCat.ofElem 1) f) = f
  rw [elvAffineScalarSpecialization_tmul, SuperalgebraCat.toElem_ofElem, map_one, one_smul]

end OddMath.QuiverHecke
end

end

section

/-! # The invertible appended dot on the ordinary probe category
The exact scalar image of the canonical old append dot is supernatural
and a word-corner unit on every appended word, including vacuum append.
This supplies the source transformation for the scalar coend comparison.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "O" => OrdinaryContentCategory D Sc a ν

/-- The literal last dot in the actual ordinary quotient category. -/
def probeOrdinaryAppendDot (i : I) (v : O) :
    (probeOrdinaryAppend D Sc m ν i).obj v ⟶ (probeOrdinaryAppend D Sc m ν i).obj v :=
  (cycHom D Sc a (v.word ++ [i]) (v.word ++ [i])).mkQ
    (dotE D Sc (v.word ++ [i]) v.word.length)

/-- No new dot normalization is chosen: this is the scalar image of the old component. -/
theorem probeOrdinaryAppendDot_old (i : I)
    (v : ELV.OldContentCategory D Sc cut ν) :
    (probeOldOrdinaryFunctor D Sc m (i :: ν)).map
      (show (ELV.oldContentAppend D Sc cut ν i).obj v ⟶
        (ELV.oldContentAppend D Sc cut ν i).obj v from
          ELV.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i v.obj) =
      probeOrdinaryAppendDot D Sc m ν i ((probeOldOrdinaryFunctor D Sc m ν).obj v) := by
  rw [ELV.CyclotomicCrossingTensor.oldAppendDotComponent_eq]
  change (cycHom D Sc a _ _).mkQ
    (elvProbeScalarHom D m Sc _ _
      (ELV.affineUnit D Sc cut _ _ (dotE D Sc (v.obj.word ++ [i]) v.obj.word.length ^ 1))) = _
  rw [pow_one, elvProbeScalarHom_affineUnit]
  rfl

/-- The scalar dot retains its full supernatural sign on ordinary Homs. -/
theorem probeOrdinaryAppendDot_supernatural (i : I) :
    IsSupernatural k (D.parity i) (probeOrdinaryAppendDot D Sc m ν i) := by
  refine ⟨?_, ?_⟩
  · intro v
    exact probeOrdinaryHomSpace_mk_mem D Sc m (positionedDot_parity D Sc v.word [] i)
  · intro v w q f hf
    obtain ⟨fr,hfr,rfl⟩ := probeOrdinaryHomSpace_lift D Sc m hf
    have h := MonoidalSupercategory.super_interchange hfr (firstDot_parity D Sc i [])
    rw [whiskerLeft_dotE D Sc w.word i rfl, whiskerLeft_dotE D Sc v.word i rfl] at h
    have hq := congrArg (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ h
    rw [map_zsmul, koszulSign_smul (R := k)] at hq
    change (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
      ((fr ▷ (pres D Sc).obj (ob D [i])) ≫ dotE D Sc (w.word ++ [i]) w.word.length) =
      sign k (D.parity i * q) •
        (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
          (dotE D Sc (v.word ++ [i]) v.word.length ≫ (fr ▷ (pres D Sc).obj (ob D [i])))
    simpa only [mul_comm q (D.parity i)] using hq

variable [Fintype I]
/-- The literal appended dot is an actual endomorphism unit, including at height zero. -/
theorem probeOrdinaryAppendDot_isUnit [Fact Sc.PureNilpotent] (i : I) (v : O) :
    IsUnit (End.of (probeOrdinaryAppendDot D Sc m ν i v)) := by
  let s : Word I (v.word.length + 1) := ⟨v.word ++ [i], by simp⟩
  have hs : s.val.Perm (i :: ν) := ((probeOrdinaryAppend D Sc m ν i).obj v).wordPerm
  exact probeOrdinaryWordDot_isUnit D Sc (i :: ν) m s hs v.word.length (Nat.lt_succ_self _)

end OddMath.QuiverHecke
end

end

section

/-! # Signed inverse of the ordinary probe induction dot
The inverse source dot has the same parity. Its induced transform requires
the factor (-1)^(p*p), retaining the signed right-multiplication convention.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} (e : ∀ v, J.obj v ≅ J.obj v)
  (he : IsSupernatural k p (fun v => (e v).hom))

omit [IsSuperfunctor k J] in
include he in
/-- The inverse family retains the same parity and supernatural sign. -/
theorem inverseComponent_supernatural :
    IsSupernatural k p (fun v => (e v).inv) := by
  apply IsSupernatural.of_twist (fun v => Supercategory.inv_mem (e v) (he.mem v))
  intro v w f
  have ht := he.naturality_twist (twist k p f)
  rw [twist_twist] at ht
  apply (cancel_mono (e w).hom).mp
  rw [Category.assoc, (e w).inv_hom_id, Category.comp_id]
  rw [Category.assoc, ht, ← Category.assoc, (e v).inv_hom_id, Category.id_comp]

variable (M : Superfunctor k C (SVec k))

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (ν : List I) (i : I)

/-- The literal ordinary appended dot is an isomorphism at each source word. -/
noncomputable def probeOrdinaryAppendDotIso [Fact Sc.PureNilpotent]
    (v : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) :
    (probeOrdinaryAppend D Sc m ν i).obj v ≅ (probeOrdinaryAppend D Sc m ν i).obj v := by
  haveI := (isUnit_iff_isIso (End.of (probeOrdinaryAppendDot D Sc m ν i v))).mp
    (probeOrdinaryAppendDot_isUnit D Sc m ν i v)
  exact asIso (probeOrdinaryAppendDot D Sc m ν i v)

variable (M : Superfunctor k
  (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))

end OddMath.QuiverHecke
end

end

section

/-! # Signed dot inverse on old scalar probe coends
This supplies the probe-unit roadmap input for the prescribed old append induction.
The inverse is constructed on the original balanced quotient using scalar-kernel
closure and the inverse ordinary appended dot. The canonical probe module discharges
the scalar-evaluation condition. No finite-dimensionality or coend comparison is used.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "C" => ELV.OldContentCategory D Sc cut ν
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν

section Action
variable (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

/-- The literal ordinary Hom action retains the original old module values. -/
theorem probeScalarAction_old (v w : C) (f : v ⟶ w) :
    probeOrdinaryModuleHom D m Sc ν N hN v w ((Q).map (X := v) (Y := w) f) =
      N.toFunctor.map (X := v) (Y := w) f :=
  probeOrdinaryModuleHom_old D m Sc ν N hN v w f

/-- Composition holds on unchanged old values, without rebuilding object labels. -/
theorem probeScalarAction_comp (v w z : C)
    (f : (Q).obj v ⟶ (Q).obj w) (g : (Q).obj w ⟶ (Q).obj z) :
    probeOrdinaryModuleHom D m Sc ν N hN v z (f ≫ g) =
      probeOrdinaryModuleHom D m Sc ν N hN v w f ≫
        probeOrdinaryModuleHom D m Sc ν N hN w z g := by
  obtain ⟨fr,rfl⟩ := elvProbeOldHom_surjective D m Sc v.obj.word w.obj.word f
  obtain ⟨gr,rfl⟩ := elvProbeOldHom_surjective D m Sc w.obj.word z.obj.word g
  let f₀ : v ⟶ w := fr
  let g₀ : w ⟶ z := gr
  change probeOrdinaryModuleHom D m Sc ν N hN v z
      ((Q).map (X := v) (Y := w) f₀ ≫ (Q).map (X := w) (Y := z) g₀) =
    probeOrdinaryModuleHom D m Sc ν N hN v w ((Q).map (X := v) (Y := w) f₀) ≫
      probeOrdinaryModuleHom D m Sc ν N hN w z ((Q).map (X := w) (Y := z) g₀)
  have hq := congrArg (probeOrdinaryModuleHom D m Sc ν N hN v z) ((Q).map_comp f₀ g₀)
  have hf := probeScalarAction_old D Sc m ν N hN v w f₀
  have hg := probeScalarAction_old D Sc m ν N hN w z g₀
  exact hq.symm.trans ((probeScalarAction_old D Sc m ν N hN v z (f₀ ≫ g₀)).trans
    ((N.toFunctor.map_comp f₀ g₀).trans
      (congrArg₂ (fun x : N.obj v ⟶ N.obj w => fun y : N.obj w ⟶ N.obj z => x ≫ y)
        hf.symm hg.symm)))

end Action

/-- The prescribed old dot, on the existing content append functor. -/
def probeOldContentAppendDot (i : I) (v : C) :
    (ELV.oldContentAppend D Sc cut ν i).obj v ⟶
      (ELV.oldContentAppend D Sc cut ν i).obj v :=
  ELV.CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i v.obj

theorem probeOldContentAppendDot_supernatural (i : I) :
    IsSupernatural k (D.parity i) (probeOldContentAppendDot D Sc m ν i) where
  mem v := (ELV.CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cut i).mem v.obj
  naturality hf :=
    (ELV.CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cut i).naturality hf

/-- The original signed balanced transform, on the actual old content coend. -/
def probeOldContentInductionDot (i : I)
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ELV.BalancedInduction.Obj (ELV.oldContentAppend D Sc cut ν i) N.toFunctor t →ₗ[k]
      ELV.BalancedInduction.Obj (ELV.oldContentAppend D Sc cut ν i) N.toFunctor t :=
  ELV.BalancedInduction.transformLinear (probeOldContentAppendDot_supernatural D Sc m ν i) N t

@[simp] theorem probeOldContentInductionDot_tensor (i : I)
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (v : C) (t : ELV.OldContentCategory D Sc cut (i :: ν))
    (g : (ELV.oldContentAppend D Sc cut ν i).obj v ⟶ t) (b : N.obj v) :
    probeOldContentInductionDot D Sc m ν i N t
      (ELV.BalancedInduction.tensor (ELV.oldContentAppend D Sc cut ν i) N.toFunctor v g b) =
    ELV.BalancedInduction.tensor (ELV.oldContentAppend D Sc cut ν i) N.toFunctor v
      (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) b :=
  ELV.BalancedInduction.transformLinear_tensor _ _ _ _ _ _

section SourceInverse
variable [Fintype I] (i : I)
local notation "J" => ELV.oldContentAppend D Sc cut ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

/-- Inverse of the source dot in the literal ordinary Hom quotient. -/
def probeOrdinarySourceDotInverse [Fact Sc.PureNilpotent] (v : C) :
    (U).obj ((J).obj v) ⟶ (U).obj ((J).obj v) :=
  (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v)).inv

omit [Fintype I] in
theorem probeOldContentAppendDot_image (v : C) :
    (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) =
      probeOrdinaryAppendDot D Sc m ν i ((Q).obj v) :=
  probeOrdinaryAppendDot_old D Sc m ν i v

theorem probeOrdinarySourceDotInverse_dot [Fact Sc.PureNilpotent] (v : C) :
    probeOrdinarySourceDotInverse D Sc m ν i v ≫
      (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) =
        𝟙 ((U).obj ((J).obj v)) := by
  rw [probeOldContentAppendDot_image]
  exact (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v)).inv_hom_id

theorem probeOrdinarySourceDot_dotInverse [Fact Sc.PureNilpotent] (v : C) :
    (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) ≫
      probeOrdinarySourceDotInverse D Sc m ν i v = 𝟙 ((U).obj ((J).obj v)) := by
  rw [probeOldContentAppendDot_image]
  exact (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v)).hom_inv_id

theorem probeOrdinarySourceDotInverse_mem [Fact Sc.PureNilpotent] (v : C) :
    probeOrdinarySourceDotInverse D Sc m ν i v ∈
      parity (R := k) ((U).obj ((J).obj v)) ((U).obj ((J).obj v)) (D.parity i) :=
  Supercategory.inv_mem (probeOrdinaryAppendDotIso D Sc m ν i ((Q).obj v))
    ((probeOrdinaryAppendDot_supernatural D Sc m ν i).mem ((Q).obj v))

/-- The inverse retains the full output twist on actual old input arrows. -/
theorem probeOrdinarySourceDotInverse_naturality [Fact Sc.PureNilpotent] (v w : C) (f : v ⟶ w) :
    (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f) ≫
      probeOrdinarySourceDotInverse D Sc m ν i w =
    probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i)
        ((U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f)) := by
  let qf := (Q).map (X := v) (Y := w) f
  have hs : (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f) =
      (T).map (X := (Q).obj v) (Y := (Q).obj w) qf :=
    elvProbeOldHom_rightContext D m Sc [i] v.obj.word w.obj.word f
  have hi := (ELV.BalancedInduction.inverseComponent_supernatural T
    (probeOrdinaryAppendDotIso D Sc m ν i)
    (probeOrdinaryAppendDot_supernatural D Sc m ν i)).naturality_twist qf
  calc
    _ = (T).map qf ≫ probeOrdinarySourceDotInverse D Sc m ν i w :=
      congrArg (fun x => x ≫ probeOrdinarySourceDotInverse D Sc m ν i w) hs
    _ = probeOrdinarySourceDotInverse D Sc m ν i v ≫ (T).map (twist k (D.parity i) qf) := hi
    _ = probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) ((T).map qf) :=
      congrArg (fun x => probeOrdinarySourceDotInverse D Sc m ν i v ≫ x) (map_twist T (D.parity i) qf)
    _ = _ := congrArg (fun x => probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) x) hs.symm
/-- The inverse-dot/twisted-Hom expression is linear in the actual old Hom. -/
def probeOrdinaryInverseHom [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ((J).obj v ⟶ t) →ₗ[k] ((U).obj ((J).obj v) ⟶ (U).obj t) :=
  (Linear.leftComp k ((U).obj t) (probeOrdinarySourceDotInverse D Sc m ν i v)).comp
    ((twist k (D.parity i) (X := (U).obj ((J).obj v)) (Y := (U).obj t)).comp
      ((U).mapLinearMap (R := k) (X := (J).obj v) (Y := t)))

@[simp] theorem probeOrdinaryInverseHom_apply [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) :
    probeOrdinaryInverseHom D Sc m ν i v t g =
      probeOrdinarySourceDotInverse D Sc m ν i v ≫
        twist k (D.parity i) ((U).map (X := (J).obj v) (Y := t) g) := rfl

/-- This is the ordinary Hom identity needed for actual old coend balancing. -/
theorem probeOrdinaryInverseHom_balance [Fact Sc.PureNilpotent] (v w : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν))
    (f : v ⟶ w) (g : (J).obj w ⟶ t) :
    probeOrdinaryInverseHom D Sc m ν i v t ((J).map (X := v) (Y := w) f ≫ g) =
      (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f) ≫
        probeOrdinaryInverseHom D Sc m ν i w t g := by
  let uf := (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f)
  let ug := (U).map (X := (J).obj w) (Y := t) g
  have hm : (U).map (X := (J).obj v) (Y := t) ((J).map (X := v) (Y := w) f ≫ g) =
      uf ≫ ug := (U).map_comp ((J).map (X := v) (Y := w) f) g
  change probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i) ((U).map (X := (J).obj v) (Y := t) ((J).map f ≫ g)) =
    uf ≫ (probeOrdinarySourceDotInverse D Sc m ν i w ≫ twist k (D.parity i) ug)
  calc
    _ = probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) (uf ≫ ug) :=
      congrArg (fun x => probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) x) hm
    _ = (probeOrdinarySourceDotInverse D Sc m ν i v ≫ twist k (D.parity i) uf) ≫
        twist k (D.parity i) ug := by rw [twist_comp, Category.assoc]
    _ = (uf ≫ probeOrdinarySourceDotInverse D Sc m ν i w) ≫ twist k (D.parity i) ug :=
      congrArg (fun x => x ≫ twist k (D.parity i) ug)
        (probeOrdinarySourceDotInverse_naturality D Sc m ν i v w f).symm
    _ = _ := Category.assoc _ _ _

/-- The first inverse product reduces to the scalar image of the old Hom. -/
theorem probeOrdinaryInverseHom_dot [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) :
    probeOrdinaryInverseHom D Sc m ν i v t
      (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) =
      sign k (D.parity i * D.parity i) • (U).map (X := (J).obj v) (Y := t) g := by
  let ad := (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v)
  let ug := (U).map (X := (J).obj v) (Y := t) g
  have ha : ad ∈ parity (R := k) ((U).obj ((J).obj v)) ((U).obj ((J).obj v)) (D.parity i) := by
    rw [show ad = probeOrdinaryAppendDot D Sc m ν i ((Q).obj v) from
      probeOldContentAppendDot_image D Sc m ν i v]
    exact (probeOrdinaryAppendDot_supernatural D Sc m ν i).mem ((Q).obj v)
  have hm : (U).map (X := (J).obj v) (Y := t)
      (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) =
      ad ≫ twist k (D.parity i) ug := by
    exact ((U).map_comp (probeOldContentAppendDot D Sc m ν i v) (twist k (D.parity i) g)).trans
      (congrArg (fun z => ad ≫ z) (map_twist U (D.parity i) g))
  change probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i) ((U).map (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g)) = _
  rw [hm, twist_comp, twist_twist, twist_of_mem (D.parity i) ha,
    Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
    probeOrdinarySourceDotInverse_dot, Category.id_comp]

/-- The other inverse product retains the same parity-square sign. -/
theorem probeOrdinaryDot_twist_inverseHom [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) :
    (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v) ≫
      twist k (D.parity i) (probeOrdinaryInverseHom D Sc m ν i v t g) =
      sign k (D.parity i * D.parity i) • (U).map (X := (J).obj v) (Y := t) g := by
  change (U).map (probeOldContentAppendDot D Sc m ν i v) ≫
    twist k (D.parity i) (probeOrdinarySourceDotInverse D Sc m ν i v ≫
      twist k (D.parity i) ((U).map g)) = _
  rw [twist_comp, twist_twist,
    twist_of_mem (D.parity i) (probeOrdinarySourceDotInverse_mem D Sc m ν i v),
    Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
    probeOrdinarySourceDot_dotInverse, Category.id_comp]

end SourceInverse

section InverseSummand
variable [Fintype I] (i : I)
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)
local notation "J" => ELV.oldContentAppend D Sc cut ν i
local notation "L" => ELV.BalancedInduction.induced J N
local notation "hL" => probeOldInduced_evaluatesCoefficients D m Sc ν i N hN
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

/-- Ordinary Hom action on the unchanged actual induced old module values. -/
def probeOldInverseHomAction [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ((J).obj v ⟶ t) →ₗ[k] ((L).obj ((J).obj v) ⟶ (L).obj t) :=
  (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t).comp
    (probeOrdinaryInverseHom D Sc m ν i v t)

/-- The inverse summand is bilinear in the original old Hom and module vector. -/
def probeOldInverseGenerator [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ((J).obj v ⟶ t) →ₗ[k] (N.obj v →ₗ[k] ELV.BalancedInduction.Obj J N.toFunctor t) :=
  (Linear.leftComp k ((L).obj t)
    (show N.obj v ⟶ (L).obj ((J).obj v) from ELV.BalancedInduction.unit J N.toFunctor v)).comp
      (probeOldInverseHomAction D Sc m ν i N hN v t)

@[simp] theorem probeOldInverseGenerator_apply [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeOldInverseGenerator D Sc m ν i N hN v t g b =
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (probeOrdinaryInverseHom D Sc m ν i v t g)
        (ELV.BalancedInduction.unit J N.toFunctor v b) := rfl

def probeOldInverseSummand [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    (((J).obj v ⟶ t) ⊗[k] N.obj v) →ₗ[k] ELV.BalancedInduction.Obj J N.toFunctor t :=
  TensorProduct.lift (probeOldInverseGenerator D Sc m ν i N hN v t)

@[simp] theorem probeOldInverseSummand_tmul [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeOldInverseSummand D Sc m ν i N hN v t (g ⊗ₜ[k] b) =
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (probeOrdinaryInverseHom D Sc m ν i v t g)
        (ELV.BalancedInduction.unit J N.toFunctor v b) :=
  TensorProduct.lift.tmul g b
/-- Balancing is proved inside the original old coend. -/
theorem probeOldInverseSummand_balance [Fact Sc.PureNilpotent] (v w : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν))
    (f : v ⟶ w) (g : (J).obj w ⟶ t) (b : N.obj v) :
    probeOldInverseSummand D Sc m ν i N hN v t (((J).map f ≫ g) ⊗ₜ[k] b) =
      probeOldInverseSummand D Sc m ν i N hN w t (g ⊗ₜ[k] N.toFunctor.map f b) := by
  rw [probeOldInverseSummand_tmul, probeOldInverseSummand_tmul]
  let uf := (U).map (X := (J).obj v) (Y := (J).obj w) ((J).map (X := v) (Y := w) f)
  let hg := probeOrdinaryInverseHom D Sc m ν i w t g
  let uv := ELV.BalancedInduction.unit J N.toFunctor v b
  have hb := probeOrdinaryInverseHom_balance D Sc m ν i v w t f g
  have hc := probeScalarAction_comp D Sc m (i :: ν) L hL ((J).obj v) ((J).obj w) t uf hg
  have ho : probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj w) uf =
      (show (L).obj ((J).obj v) ⟶ (L).obj ((J).obj w) from
        ELV.BalancedInduction.postcompose J N.toFunctor ((J).map f)) :=
    probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) ((J).obj w) ((J).map f)
  have hu := LinearMap.congr_fun (ELV.BalancedInduction.unit_naturality J N.toFunctor f) b
  calc
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (uf ≫ hg) uv :=
      congrArg (fun z => probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t z uv) hb
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg
        (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj w) uf uv) := by
      simpa only [SVec.comp_apply] using congrArg
        (fun z : (L).obj ((J).obj v) ⟶ (L).obj t => z uv) hc
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg
        (ELV.BalancedInduction.postcompose J N.toFunctor ((J).map f) uv) :=
      congrArg (fun z => probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg z)
        (congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj ((J).obj w) => z uv) ho)
    _ = _ := congrArg (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj w) t hg)
      (by simpa only [LinearMap.comp_apply] using hu)

/-- Explicit signed inverse candidate on the actual old balanced quotient. -/
def probeOldContentInductionDotInverse [Fact Sc.PureNilpotent]
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ELV.BalancedInduction.Obj J N.toFunctor t →ₗ[k]
      ELV.BalancedInduction.Obj J N.toFunctor t :=
  sign k (D.parity i * D.parity i) • ELV.BalancedInduction.lift J N.toFunctor t
    (fun v => probeOldInverseSummand D Sc m ν i N hN v t)
    (fun v w f g b => probeOldInverseSummand_balance D Sc m ν i N hN v w t f g b)

@[simp] theorem probeOldContentInductionDotInverse_tensor [Fact Sc.PureNilpotent] (v : C)
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeOldContentInductionDotInverse D Sc m ν i N hN t
      (ELV.BalancedInduction.tensor J N.toFunctor v g b) =
    sign k (D.parity i * D.parity i) •
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (probeOrdinaryInverseHom D Sc m ν i v t g)
        (ELV.BalancedInduction.unit J N.toFunctor v b) := by
  rw [probeOldContentInductionDotInverse, LinearMap.smul_apply,
    ELV.BalancedInduction.lift_tensor, probeOldInverseSummand_tmul]

/-- No finite-dimensionality is used: one inverse product is checked on the old generators. -/
theorem probeOldContentInductionDotInverse_comp_dot [Fact Sc.PureNilpotent]
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    (probeOldContentInductionDotInverse D Sc m ν i N hN t).comp
      (probeOldContentInductionDot D Sc m ν i N t) = LinearMap.id := by
  apply ELV.BalancedInduction.hom_ext
  intro v g b
  rw [LinearMap.comp_apply, probeOldContentInductionDot_tensor,
    probeOldContentInductionDotInverse_tensor, probeOrdinaryInverseHom_dot,
    map_smul, SVec.smul_apply, sign_smul_sign_smul]
  have h := probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) t g
  have hv := congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj t =>
    z (ELV.BalancedInduction.unit J N.toFunctor v b)) h
  exact hv.trans (ELV.BalancedInduction.postcompose_unit J N.toFunctor g b)

omit [Fintype I] in
private theorem probeOldContentInductionDot_unit_action (v : C) (b : N.obj v) :
    probeOldContentInductionDot D Sc m ν i N ((J).obj v)
      (ELV.BalancedInduction.unit J N.toFunctor v b) =
    probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj v)
      ((U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v))
      (ELV.BalancedInduction.unit J N.toFunctor v b) := by
  have h := probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) ((J).obj v)
    (probeOldContentAppendDot D Sc m ν i v)
  exact (ELV.BalancedInduction.transform_unit
    (probeOldContentAppendDot_supernatural D Sc m ν i) N v b).trans
      (congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj ((J).obj v) =>
        z (ELV.BalancedInduction.unit J N.toFunctor v b)) h).symm

/-- The second inverse product uses the old dot's descended full supernaturality. -/
theorem probeOldContentInductionDot_comp_inverse [Fact Sc.PureNilpotent]
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    (probeOldContentInductionDot D Sc m ν i N t).comp
      (probeOldContentInductionDotInverse D Sc m ν i N hN t) = LinearMap.id := by
  apply ELV.BalancedInduction.hom_ext
  intro v g b
  rw [LinearMap.comp_apply, probeOldContentInductionDotInverse_tensor, map_smul]
  let hf := probeOrdinaryInverseHom D Sc m ν i v t g
  let ad := (U).map (X := (J).obj v) (Y := (J).obj v) (probeOldContentAppendDot D Sc m ν i v)
  let uv := ELV.BalancedInduction.unit J N.toFunctor v b
  have hv : probeOldContentInductionDot D Sc m ν i N t
      (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t hf uv) =
      probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        (twist k (D.parity i) hf)
        (probeOldContentInductionDot D Sc m ν i N ((J).obj v) uv) := by
    obtain ⟨fr, hfr⟩ := elvProbeOldHom_surjective D m Sc ((J).obj v).obj.word t.obj.word hf
    let f₀ : (J).obj v ⟶ t := fr
    have hfr' : (U).map (X := (J).obj v) (Y := t) f₀ = hf := hfr
    rw [← hfr', probeScalarAction_old, ← map_twist (U) (D.parity i) f₀,
      probeScalarAction_old]
    exact LinearMap.congr_fun (ELV.BalancedInduction.transformLinear_naturality
      (probeOldContentAppendDot_supernatural D Sc m ν i) N f₀) uv
  have hc := probeScalarAction_comp D Sc m (i :: ν) L hL ((J).obj v) ((J).obj v) t
    ad (twist k (D.parity i) hf)
  have hcv := congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj t => z uv) hc
  have hd := probeOrdinaryDot_twist_inverseHom D Sc m ν i v t g
  calc
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (twist k (D.parity i) hf)
          (probeOldContentInductionDot D Sc m ν i N ((J).obj v) uv) := by
      exact congrArg (fun z => sign k (D.parity i * D.parity i) • z)
        hv
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (twist k (D.parity i) hf)
          (probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) ((J).obj v) ad uv) :=
      congrArg (fun z => sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t (twist k (D.parity i) hf) z)
          (probeOldContentInductionDot_unit_action D Sc m ν i N hN v b)
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
          (ad ≫ twist k (D.parity i) hf) uv :=
      congrArg (fun z => sign k (D.parity i * D.parity i) • z)
        (by simpa only [SVec.comp_apply] using hcv.symm)
    _ = sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
          (sign k (D.parity i * D.parity i) • (U).map (X := (J).obj v) (Y := t) g) uv :=
      congrArg (fun z => sign k (D.parity i * D.parity i) •
        probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t z uv) hd
    _ = probeOrdinaryModuleHom D m Sc (i :: ν) L hL ((J).obj v) t
        ((U).map (X := (J).obj v) (Y := t) g) uv := by
      rw [map_smul, SVec.smul_apply, sign_smul_sign_smul]
    _ = _ := (congrArg (fun z : (L).obj ((J).obj v) ⟶ (L).obj t => z uv)
      (probeScalarAction_old D Sc m (i :: ν) L hL ((J).obj v) t g)).trans
        (ELV.BalancedInduction.postcompose_unit J N.toFunctor g b)

/-- Intermediate unit for a scalar-evaluated old module. The canonical probe-module
specialization below proves the scalar-evaluation hypothesis. -/
def probeOldContentInductionDotUnit [Fact Sc.PureNilpotent]
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    (End (ELV.BalancedInduction.superspace J N.toFunctor t))ˣ where
  val := End.of (probeOldContentInductionDot D Sc m ν i N t)
  inv := End.of (probeOldContentInductionDotInverse D Sc m ν i N hN t)
  val_inv := probeOldContentInductionDot_comp_inverse D Sc m ν i N hN t
  inv_val := probeOldContentInductionDotInverse_comp_dot D Sc m ν i N hN t

include hN in
theorem probeOldContentInductionDot_isUnit [Fact Sc.PureNilpotent]
    (t : ELV.OldContentCategory D Sc cut (i :: ν)) :
    IsUnit (End.of (probeOldContentInductionDot D Sc m ν i N t) :
      End (ELV.BalancedInduction.superspace J N.toFunctor t)) :=
  (probeOldContentInductionDotUnit D Sc m ν i N hN t).isUnit

end InverseSummand

section ProbeModule
variable [Fintype I] {B : Type u} [Ring B] [Algebra k B]
  {GB : ZMod 2 → Submodule k B}
  (M : SuperBimodule
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) ν.length) GB)

end ProbeModule

end OddMath.QuiverHecke
end

end

section

/-! # Generators of the scalar old-to-ordinary append comparison

The ordinary-probe generator transport in STATUS's remaining critical chain
item 3 requires the selected scalar append comparison. We compute its unit
and tensor generators through the canonical balanced-induction square, and
compare the signed dots used in DeformedActionAssembly §§5–6. All scalar
coefficients and the chosen ordinary probe category are retained.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory

namespace OddMath.QuiverHecke
universe u

section Cancellation
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

private theorem scalarComp_total_apply
    {F G H : Superfunctor k C (SVec k)} (f : F ⟶ G) (g : G ⟶ H)
    (w : C) (b : F.obj w) :
    (f ≫ g).total w b = g.total w (f.total w b) := by
  rw [Superfunctor.comp_total, SVec.comp_apply]

private theorem scalarComp_total
    {F G H : Superfunctor k C (SVec k)} (f : F ⟶ G) (g : G ⟶ H) (w : C) :
    (f ≫ g).total w = g.total w ∘ₗ f.total w :=
  Superfunctor.comp_total f g w

private theorem scalarTotal_congr
    {F G : Superfunctor k C (SVec k)} {f g : F ⟶ G} (h : f = g) (w : C) :
    f.total w = g.total w := congrArg (fun a : F ⟶ G => a.total w) h

private theorem scalarTensor_congr
    {E : Type u} [Category.{u} E] [Preadditive E] [Linear k E]
    (J : C ⥤ E) (M : Superfunctor k C (SVec k)) (v : C) (w : E)
    {g h : J.obj v ⟶ w} {b₀ b₁ : M.obj v}
    (hg : g = h) (hb : b₀ = b₁) :
    ELV.BalancedInduction.tensor J M.toFunctor v g b₀ =
      ELV.BalancedInduction.tensor J M.toFunctor v h b₁ :=
  congrArg₂ (fun a x => ELV.BalancedInduction.tensor J M.toFunctor v a x) hg hb

private theorem scalarIso_total_hom_inv
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (b : G.obj w) :
    e.hom.total w (e.inv.total w b) = b := by
  calc
    _ = (e.inv ≫ e.hom).total w b :=
      (scalarComp_total_apply e.inv e.hom w b).symm
    _ = (𝟙 G : G ⟶ G).total w b :=
      congrArg (fun f : G ⟶ G => f.total w b) e.inv_hom_id
    _ = b := by
      change ((LinearMap.id : G.obj w →ₗ[k] G.obj w) + 0) b = b
      rw [add_zero, LinearMap.id_apply]

private theorem scalarEqToHom_mem {F G : Superfunctor k C (SVec k)} (h : F = G) :
    (eqToHom h : F ⟶ G) ∈ parity (R := k) F G 0 := by
  subst G
  exact id_mem F

end Cancellation

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν

/-- The prescribed scalar quotient comparison is even. -/
theorem probeQuotientInducedModuleIso_hom_mem
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    (probeQuotientInducedModuleIso D Sc m ν N hN).hom ∈ parity (R := k) _ _ 0 := by
  let u := eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)
  let IQ := ELV.BalancedInduction.induction (k := k) Q
  have hu : u.inv ∈ parity (R := k) _ _ 0 :=
    scalarEqToHom_mem (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN).symm
  have hi : IQ.map u.inv ∈ parity (R := k) _ _ 0 := IsSuperfunctor.map_mem hu
  have hc : (probeQuotientCounitIso D Sc m ν
      (probeOrdinaryModuleSuperfunctor D Sc m ν N hN)).hom ∈ parity (R := k) _ _ 0 := by
    unfold probeQuotientCounitIso
    exact ELV.moduleIsoOfEvenNatIso_hom_mem _ _ _ _ _
  exact comp_mem hi hc

/-- The scalar quotient comparison cancels its canonical inverse unit tensor. -/
theorem probeQuotientInducedModuleIso_hom_unit
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (w : OrdinaryContentCategory D Sc a ν) (b : N.obj (probeOrdinaryOldObject D Sc m ν w)) :
    (probeQuotientInducedModuleIso D Sc m ν N hN).hom.app 0 w
      (ELV.BalancedInduction.tensor Q N.toFunctor
        (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b) = b := by
  let e := probeQuotientInducedModuleIso D Sc m ν N hN
  have h := probeQuotientInducedModuleIso_inv_tensor D Sc m ν N hN w b
  have hc := (congrArg (e.hom.total w) h).symm.trans
    (scalarIso_total_hom_inv e w b)
  have he : e.hom ∈ parity (R := k) _ _ 0 :=
    probeQuotientInducedModuleIso_hom_mem D Sc m ν N hN
  simpa only [SuperNatTrans.total,
    Superfunctor.app_eq_zero_of_mem he (q := 1) (by decide), add_zero] using hc

section Append
variable
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N) (i : I)
local notation "J" => ELV.oldContentAppend D Sc cut ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "L" => ELV.BalancedInduction.induced J N
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν N hN
local notation "hL" => probeOldInduced_evaluatesCoefficients D m Sc ν i N hN

private def probeQuotientComparisonMap : (ELV.BalancedInduction.induction Q).obj N ⟶ O :=
  (probeQuotientInducedModuleIso D Sc m ν N hN).hom

local notation "S" => ELV.BalancedInduction.squareLinear J U Q T
  (probeOldOrdinaryFunctor_append D Sc m ν i) N O
  (probeQuotientComparisonMap D Sc m ν N hN)

private theorem probeAppend_hom_square :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom =
      (probeQuotientInducedModuleIso D Sc m (i :: ν) L hL).inv ≫
        ELV.BalancedInduction.squareComparison J U Q T
          (probeOldOrdinaryFunctor_append D Sc m ν i) N O
          (probeQuotientInducedModuleIso D Sc m ν N hN).hom := by
  rw [ELV.BalancedInduction.squareComparison_eq]
  rfl

/-- The chosen comparison expressed on the literal old and ordinary coends.
This exposes identical module instances before computing generators. -/
def probeAppendComparisonLinear (w : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ELV.BalancedInduction.Obj J N.toFunctor w →ₗ[k]
      ELV.BalancedInduction.Obj T (O).toFunctor ((U).obj w) :=
  (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total ((U).obj w)

private def probeAppendQuotientInverseLinear
    (w : ELV.OldContentCategory D Sc cut (i :: ν)) :
    ELV.BalancedInduction.Obj J N.toFunctor w →ₗ[k]
      ELV.BalancedInduction.Obj U (L).toFunctor ((U).obj w) :=
  (probeQuotientInducedModuleIso D Sc m (i :: ν) L hL).inv.total ((U).obj w)

private theorem probeAppendComparisonLinear_factor
    (w : ELV.OldContentCategory D Sc cut (i :: ν)) :
    probeAppendComparisonLinear D Sc m ν N hN i w =
      S ((U).obj w) ∘ₗ
        probeAppendQuotientInverseLinear D Sc m ν N hN i w := by
  exact (scalarTotal_congr (probeAppend_hom_square D Sc m ν N hN i) ((U).obj w)).trans
    (scalarComp_total _ _ ((U).obj w))

/-- The selected comparison on arbitrary old tensor generators. -/
theorem probeAppendOrdinaryModuleIso_hom_tensor
    (v : ELV.OldContentCategory D Sc cut ν)
    (w : ELV.OldContentCategory D Sc cut (i :: ν))
    (g : (J).obj v ⟶ w) (b : N.obj v) :
    probeAppendComparisonLinear D Sc m ν N hN i w
      (ELV.BalancedInduction.tensor J N.toFunctor v g b) =
      ELV.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) ((U).map g) b := by
  let c := probeQuotientComparisonMap D Sc m ν N hN
  have h₁ : probeAppendQuotientInverseLinear D Sc m ν N hN i w
      (ELV.BalancedInduction.tensor J N.toFunctor v g b) =
      ELV.BalancedInduction.tensor U (L).toFunctor w (𝟙 ((U).obj w))
        (ELV.BalancedInduction.tensor J N.toFunctor v g b) :=
    probeQuotientInducedModuleIso_inv_tensor D Sc m (i :: ν) L hL
      ((U).obj w) (ELV.BalancedInduction.tensor J N.toFunctor v g b)
  have h₂ := ELV.BalancedInduction.squareLinear_tensor
    J U Q T (probeOldOrdinaryFunctor_append D Sc m ν i) N O
    (probeQuotientComparisonMap D Sc m ν N hN)
    (probeQuotientInducedModuleIso_hom_mem D Sc m ν N hN) v w g b
  have hunit : c.app 0 ((Q).obj v)
      (ELV.BalancedInduction.unit Q N.toFunctor v b) = b :=
    probeQuotientInducedModuleIso_hom_unit D Sc m ν N hN ((Q).obj v) b
  have hs : S ((U).obj w)
      (ELV.BalancedInduction.tensor U (L).toFunctor w (𝟙 ((U).obj w))
        (ELV.BalancedInduction.tensor J N.toFunctor v g b)) =
      ELV.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) ((U).map g) b := by
    have ha : eqToHom (congrArg
        (fun F : ELV.OldContentCategory D Sc cut ν ⥤
            OrdinaryContentCategory D Sc a (i :: ν) => F.obj v)
        (probeOldOrdinaryFunctor_append D Sc m ν i)).symm ≫ (U).map g =
          (U).map g := by
      change 𝟙 ((U).obj ((J).obj v)) ≫ (U).map g = (U).map g
      exact Category.id_comp _
    exact h₂.trans (scalarTensor_congr T O ((Q).obj v) ((U).obj w) ha hunit)
  rw [probeAppendComparisonLinear_factor, LinearMap.comp_apply]
  calc
    _ = S ((U).obj w)
        (ELV.BalancedInduction.tensor U (L).toFunctor w (𝟙 ((U).obj w))
          (ELV.BalancedInduction.tensor J N.toFunctor v g b)) :=
      congrArg (S ((U).obj w)) h₁
    _ = _ := hs

/-- In particular, the chosen comparison intertwines the literal append units. -/
theorem probeAppendOrdinaryModuleIso_hom_unit
    (v : ELV.OldContentCategory D Sc cut ν) (b : N.obj v) :
    probeAppendComparisonLinear D Sc m ν N hN i ((J).obj v)
      (ELV.BalancedInduction.unit J N.toFunctor v b) =
      ELV.BalancedInduction.unit T (O).toFunctor ((Q).obj v) b := by
  have h := probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN i v ((J).obj v) (𝟙 _) b
  have hin := congrArg (probeAppendComparisonLinear D Sc m ν N hN i ((J).obj v))
    (ELV.BalancedInduction.unit_apply J N.toFunctor v b)
  have hout := ELV.BalancedInduction.unit_apply T (O).toFunctor ((Q).obj v) b
  exact hin.trans ((h.trans (congrArg
    (fun z => ELV.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) z b)
    ((U).map_id ((J).obj v)))).trans hout.symm)

/-- The chosen comparison intertwines the prescribed signed induction dots,
including the odd twist on inhomogeneous coend arrows. -/
theorem probeAppendOrdinaryModuleIso_hom_dot
    (w : ELV.OldContentCategory D Sc cut (i :: ν)) :
    probeAppendComparisonLinear D Sc m ν N hN i w ∘ₗ
        probeOldContentInductionDot D Sc m ν i N w =
      ELV.BalancedInduction.transformLinear
        (probeOrdinaryAppendDot_supernatural D Sc m ν i) O ((U).obj w) ∘ₗ
        probeAppendComparisonLinear D Sc m ν N hN i w := by
  apply ELV.BalancedInduction.hom_ext
  intro v g b
  rw [LinearMap.comp_apply, probeOldContentInductionDot_tensor,
    probeAppendOrdinaryModuleIso_hom_tensor, LinearMap.comp_apply,
    probeAppendOrdinaryModuleIso_hom_tensor,
    ELV.BalancedInduction.transformLinear_tensor]
  have hg : (U).map (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) =
      probeOrdinaryAppendDot D Sc m ν i ((Q).obj v) ≫
        twist k (D.parity i) ((U).map g) := by
    rw [Functor.map_comp, probeOldContentAppendDot_image, map_twist]
    rfl
  exact congrArg (fun h => ELV.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) h b) hg

end Append
end OddMath.QuiverHecke
end

end

section

/-! # Scalar descent and restriction along append

The ordinary-probe comparison in STATUS critical-chain item 3 must retain the
chosen induction–restriction adjunction of DeformedActionAssembly §5. Scalar
coefficient evaluation is preserved by restriction, and the descended old
restriction equals literal ordinary restriction on the same vectors.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory

namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "J" => ELV.oldContentAppend D Sc cut ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

/-- Restriction preserves the full scalar coefficient evaluation condition,
including the odd coefficient kernel. -/
theorem probeOldRestriction_evaluatesCoefficients
    (N : Superfunctor k (ELV.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N) :
    ProbeEvaluatesCoefficients D m Sc ν
      ((ELV.BalancedInduction.restriction J).obj N) := by
  intro v c
  change N.toFunctor.map ((J).map (probeOldCoefficient D m Sc ν v c)) = _
  rw [probeOldCoefficient_append]
  exact hN ((J).obj v) c

/-- Scalar descent commutes with the specified old and ordinary append
restrictions, as an equality of supermodules on the original vector values. -/
theorem probeOrdinaryRestrictionModule_eq
    (N : Superfunctor k (ELV.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N) :
    probeOrdinaryModuleSuperfunctor D Sc m ν
      ((ELV.BalancedInduction.restriction J).obj N)
      (probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN) =
        (ELV.BalancedInduction.restriction T).obj
          (probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN) := by
  let R := (ELV.BalancedInduction.restriction J).obj N
  let hR := probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
  apply Superfunctor.ext
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro v
    rfl
  case h_map =>
    intro v w f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    let sv := probeOrdinaryOldObject D Sc m ν v
    let sw := probeOrdinaryOldObject D Sc m ν w
    obtain ⟨g, hg⟩ := elvProbeOldHom_surjective D m Sc v.word w.word f
    let g₀ : sv ⟶ sw := g
    have hq : (Q).map (X := sv) (Y := sw) g₀ = f := hg
    rw [← hq]
    have hs : (U).map (X := (J).obj sv) (Y := (J).obj sw)
        ((J).map (X := sv) (Y := sw) g₀) =
        (T).map (X := (Q).obj sv) (Y := (Q).obj sw)
          ((Q).map (X := sv) (Y := sw) g₀) :=
      elvProbeOldHom_rightContext D m Sc [i] sv.obj.word sw.obj.word g₀
    change probeOrdinaryModuleHom D m Sc ν R hR sv sw ((Q).map g₀) =
      probeOrdinaryModuleHom D m Sc (i :: ν) N hN ((J).obj sv) ((J).obj sw)
        ((T).map ((Q).map g₀))
    calc
      _ = R.toFunctor.map g₀ :=
        probeOrdinaryModuleHom_old D m Sc ν R hR sv sw g₀
      _ = N.toFunctor.map ((J).map g₀) := rfl
      _ = probeOrdinaryModuleHom D m Sc (i :: ν) N hN ((J).obj sv) ((J).obj sw)
          ((U).map ((J).map g₀)) :=
        (probeOrdinaryModuleHom_old D m Sc (i :: ν) N hN
          ((J).obj sv) ((J).obj sw) ((J).map g₀)).symm
      _ = _ := congrArg
        (probeOrdinaryModuleHom D m Sc (i :: ν) N hN ((J).obj sv) ((J).obj sw)) hs

end OddMath.QuiverHecke
end

end

section

/-! # The scalar-evaluated old probe module category

`SwappedNondegeneracy` §3 and `SwappedDetectingFamily` §2 use the prescribed
scalar specialization of the full ELV probe factor. Its full module
subcategory is stable under the actual append induction and restriction,
parity, and module products. The target retains all module morphisms;
no assertion is made about arbitrary unevaluated old modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
private theorem comp_scalar_action
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (S : Superfunctor k (SVec k) (SVec k))
    (v : C) (f : v ⟶ v) (r : k) (h : M.toFunctor.map f = r • 𝟙 (M.obj v)) :
    (M.comp S).toFunctor.map f = r • 𝟙 ((M.comp S).obj v) := by
  change S.toFunctor.map (M.toFunctor.map f) = _
  rw [h, CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)

/-- All old probe modules with the prescribed full scalar coefficient action;
all even and odd module morphisms are retained. -/
abbrev ProbeEvaluatedModules :=
  ObjectProperty.FullSubcategory (ProbeEvaluatesCoefficients D m Sc ν)

/-- The specified old append induction stays inside the scalar specialization. -/
def probeEvaluatedInduction (i : I) :
    ProbeEvaluatedModules D Sc m ν ⥤ ProbeEvaluatedModules D Sc m (i :: ν) where
  obj N := ⟨induced (oldContentAppend D Sc (probeCutoff D m) ν i) N.obj,
    probeOldInduced_evaluatesCoefficients D m Sc ν i N.obj N.property⟩
  map f := ⟨(induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map f.hom⟩
  map_id N := InducedCategory.hom_ext ((induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_id N.obj)
  map_comp f g := InducedCategory.hom_ext ((induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_comp f.hom g.hom)

/-- The specified old restriction stays inside the same scalar specialization. -/
def probeEvaluatedRestriction (i : I) :
    ProbeEvaluatedModules D Sc m (i :: ν) ⥤ ProbeEvaluatedModules D Sc m ν where
  obj N := ⟨(restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).obj N.obj,
    probeOldRestriction_evaluatesCoefficients D Sc m ν i N.obj N.property⟩
  map f := ⟨(restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map f.hom⟩
  map_id N := InducedCategory.hom_ext ((restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_id N.obj)
  map_comp f g := InducedCategory.hom_ext ((restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_comp f.hom g.hom)

instance probeEvaluatedInduction_additive (i : I) : (probeEvaluatedInduction D Sc m ν i).Additive where
  map_add := InducedCategory.hom_ext ((induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_add)
instance probeEvaluatedInduction_linear (i : I) : (probeEvaluatedInduction D Sc m ν i).Linear k where
  map_smul f r := InducedCategory.hom_ext ((induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_smul r f.hom)
instance probeEvaluatedInduction_super (i : I) : IsSuperfunctor k (probeEvaluatedInduction D Sc m ν i) where
  map_mem := by
    intro A B p f hf
    change f.hom ∈ parity (R := k) _ _ p at hf
    change (induction (oldContentAppend D Sc (probeCutoff D m) ν i)).map f.hom ∈ parity (R := k) _ _ p
    exact map_mem _ hf
instance probeEvaluatedRestriction_additive (i : I) : (probeEvaluatedRestriction D Sc m ν i).Additive where
  map_add := InducedCategory.hom_ext ((restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_add)
instance probeEvaluatedRestriction_linear (i : I) : (probeEvaluatedRestriction D Sc m ν i).Linear k where
  map_smul f r := InducedCategory.hom_ext ((restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map_smul r f.hom)
instance probeEvaluatedRestriction_super (i : I) : IsSuperfunctor k (probeEvaluatedRestriction D Sc m ν i) where
  map_mem := by
    intro A B p f hf
    change f.hom ∈ parity (R := k) _ _ p at hf
    change (restriction (oldContentAppend D Sc (probeCutoff D m) ν i)).map f.hom ∈ parity (R := k) _ _ p
    exact map_mem _ hf

/-- Scalar evaluation is stable under the actual vector parity functor. -/
theorem probeEvaluatesCoefficients_parity
    (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    ProbeEvaluatesCoefficients D m Sc ν (supermoduleParityObj N) := by
  intro v c
  exact comp_scalar_action N (PiSCat.piHom (PiSCat.of k (SVec k))) v
    (probeOldCoefficient D m Sc ν v c) _ (hN v c)

/-- The actual scalar-evaluated probe category has its inherited parity completion. -/
@[instance_reducible]
def probeEvaluatedPiSupercategory : PiSupercategory k (ProbeEvaluatedModules D Sc m ν) :=
  letI := supermodulePiSupercategory (k := k) (C := OldContentCategory D Sc (probeCutoff D m) ν)
  CyclotomicAction.fullPiSupercategory (ProbeEvaluatesCoefficients D m Sc ν)
    (probeEvaluatesCoefficients_parity D Sc m ν)

end OddMath.QuiverHecke
end

end

section

/-! # Permutation transport of the scalar-evaluated old probe

`SwappedDetectingFamily` §2: replacing a stored content list by a permutation
retains the literal old word objects, quotient arrows and coefficient action.
These equivalences permit canonical multiset representatives without changing
the probe algebra or imposing coefficient-power truncation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  {ν μ η : List I}

/-- Reindex only the permutation certificate of an actual old word. -/
def oldContentReindex (h : ν.Perm μ) :
    OldContentCategory D Sc cutoff ν ⥤ OldContentCategory D Sc cutoff μ where
  obj v := ⟨v.obj, v.wordPerm.trans h⟩
  map f := f

instance (h : ν.Perm μ) : (oldContentReindex D Sc cutoff h).Additive where
  map_add := rfl
instance (h : ν.Perm μ) : (oldContentReindex D Sc cutoff h).Linear k where
  map_smul _ _ := rfl
instance (h : ν.Perm μ) : IsSuperfunctor k (oldContentReindex D Sc cutoff h) where
  map_mem hf := hf

@[simp] theorem oldContentReindex_comp (h : ν.Perm μ) (g : μ.Perm η) :
    oldContentReindex D Sc cutoff h ⋙ oldContentReindex D Sc cutoff g =
      oldContentReindex D Sc cutoff (h.trans g) := rfl

@[simp] theorem oldContentReindex_refl :
    oldContentReindex D Sc cutoff (List.Perm.refl ν) = 𝟭 _ := rfl

end OddMath.QuiverHecke.ELV

namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  {ν μ η : List I}

/-- Pullback along a representative change retains scalar evaluation. -/
theorem probeEvaluatesCoefficients_reindex (h : ν.Perm μ)
    (M : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) μ) (SVec k))
    (hM : ProbeEvaluatesCoefficients D m Sc μ M) :
    ProbeEvaluatesCoefficients D m Sc ν
      ((restriction (oldContentReindex D Sc (probeCutoff D m) h)).obj M) := by
  intro v c
  exact hM ((oldContentReindex D Sc (probeCutoff D m) h).obj v) c

/-- Transport an evaluated module to a new stored list, with unchanged vector spaces. -/
def probeEvaluatedReindex (h : ν.Perm μ) :
    ProbeEvaluatedModules D Sc m ν ⥤ ProbeEvaluatedModules D Sc m μ where
  obj M := ⟨(restriction (oldContentReindex D Sc (probeCutoff D m) h.symm)).obj M.obj,
    probeEvaluatesCoefficients_reindex D Sc m h.symm M.obj M.property⟩
  map f := ⟨(restriction (oldContentReindex D Sc (probeCutoff D m) h.symm)).map f.hom⟩
  map_id M := InducedCategory.hom_ext ((restriction
    (oldContentReindex D Sc (probeCutoff D m) h.symm)).map_id M.obj)
  map_comp f g := InducedCategory.hom_ext ((restriction
    (oldContentReindex D Sc (probeCutoff D m) h.symm)).map_comp f.hom g.hom)

instance (h : ν.Perm μ) : (probeEvaluatedReindex D Sc m h).Additive where
  map_add := InducedCategory.hom_ext ((restriction
    (oldContentReindex D Sc (probeCutoff D m) h.symm)).map_add)
instance (h : ν.Perm μ) : (probeEvaluatedReindex D Sc m h).Linear k where
  map_smul f r := InducedCategory.hom_ext ((restriction
    (oldContentReindex D Sc (probeCutoff D m) h.symm)).map_smul r f.hom)
instance (h : ν.Perm μ) : IsSuperfunctor k (probeEvaluatedReindex D Sc m h) where
  map_mem := by
    intro A B p f hf
    change f.hom ∈ parity (R := k) _ _ p at hf
    change (restriction (oldContentReindex D Sc (probeCutoff D m) h.symm)).map f.hom ∈ parity (R := k) _ _ p
    exact map_mem _ hf

@[simp] theorem probeEvaluatedReindex_comp (h : ν.Perm μ) (g : μ.Perm η) :
    probeEvaluatedReindex D Sc m h ⋙ probeEvaluatedReindex D Sc m g =
      probeEvaluatedReindex D Sc m (h.trans g) := rfl

@[simp] theorem probeEvaluatedReindex_refl :
    probeEvaluatedReindex D Sc m (List.Perm.refl ν) = 𝟭 _ := rfl

end OddMath.QuiverHecke
end

end
