/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators
import OddMath.QuiverHecke.SwappedAssembly.Quad

/-! # The inversion relations in the swapped layer representation

The relations `invNe₁`, `invNe₂`, `invP₁`–`invP₅` and `invM₁`–`invM₅` of
`OddMath.SKM.Presentation` are (1.11)–(1.14) of Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, Definition 1.5, with the leftward crossing and the
`♦`-cups and caps of (2.6) as generators: for `i ≠ j` the leftward crossing is a two-sided
inverse of the sideways crossing `σ : Eⱼ Fᵢ → Fᵢ Eⱼ`, and for `i = j` the leftward crossing and
the `♦`-cups and caps are the components of the inverse of the augmented maps (1.13), (1.14).

For the swapped generators `swappedGens c L`:

* distinct colours: the leftward crossing `lcrossNeImage` is the entrywise inverse of the
  matrix of `σ`. When that matrix is a permutation matrix with invertible entries
  (`SigmaPermutation`, the block structure of `docs/Nondegeneracy/SwappedActionAssembly.md`
  §5), it is the two-sided inverse (`sigma_lcross_sum`, `lcross_sigma_sum`);
* equal colours: the identities characterizing the leftward data `L` are the remaining
  relations themselves (`LeftwardData.IsInverse`).

`inversionRelations` combines the two. `compEval_dg_append` (the entry of a composite of two
normal-form diagrams is the matrix product of their entries) is used throughout.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u uB v w

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

open Classical in
/-- **The entry of a composite of two normal-form diagrams** is the matrix product of their
entries. -/
theorem compEval_dg_append (gens : P.Generators) (ν : X) {t t' t'' : List (Letter I)}
    (ls ms : List (SKM.LayerData I)) (h₁ : SKM.SChain t ls t') (h₂ : SKM.SChain t' ms t'')
    {s r : Sector I} (p : SPath (SKM.ob D ν t).word s r) (q : SPath (SKM.ob D ν t'').word s r)
    (Z : P.H r) :
    letI := Fintype.ofFinite (SPath (SKM.ob D ν t').word s r)
    compEval gens (SKM.dg D ν (ls ++ ms) (h₁.append h₂) : LinDiagram k _ _) p q Z =
      ∑ m, compDiag gens (SKM.mkD D ν ls h₁) p m Z ≫ compDiag gens (SKM.mkD D ν ms h₂) m q Z := by
  refine (compEval_of gens _ p q Z).trans ?_
  rw [← SKM.mkD_comp]
  exact compDiag_comp gens _ _ p q Z

/-- The inverse of an invertible zero morphism is zero. -/
theorem inv_eq_zero_of_eq_zero {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {A A' : C}
    (f : A ⟶ A') (h : IsIso f) (hf : f = 0) : @inv _ _ _ _ f h = 0 := by
  subst hf
  have : @inv _ _ _ _ (0 : A ⟶ A') h = @inv _ _ _ _ (0 : A ⟶ A') h ≫ (0 : A ⟶ A') ≫
      @inv _ _ _ _ (0 : A ⟶ A') h := by
    rw [@IsIso.hom_inv_id _ _ _ _ _ h, Category.comp_id]
  exact this.trans (by rw [Limits.zero_comp, Limits.comp_zero])

/-- The entry of the leftward crossing for distinct colours vanishes where the corresponding
entry of the sideways crossing does. -/
theorem lcrossNeImage_eq_zero (c : P.CrossCoeff) (i j : I) (ν : X) {t s : Sector I}
    (p : SPath (wd D ν [dn i, up j]) t s) (p' : SPath (wd D ν [up j, dn i]) t s) (Z : P.H s)
    (h : P.sigmaEntry c i j ν p' p Z = 0) : P.lcrossNeImage c i j ν p p' Z = 0 := by
  unfold lcrossNeImage
  split_ifs with hi
  · exact inv_eq_zero_of_eq_zero _ hi h
  · rfl

/-- The entry of the leftward crossing for distinct colours at an invertible entry of the
sideways crossing is its inverse. -/
theorem lcrossNeImage_of_isIso (c : P.CrossCoeff) (i j : I) (ν : X) {t s : Sector I}
    (p : SPath (wd D ν [dn i, up j]) t s) (p' : SPath (wd D ν [up j, dn i]) t s) (Z : P.H s)
    [h : IsIso (P.sigmaEntry c i j ν p' p Z)] :
    P.lcrossNeImage c i j ν p p' Z = inv (P.sigmaEntry c i j ν p' p Z) := by
  unfold lcrossNeImage
  simp only [h, dite_true]

/-- **The matrix of the sideways crossing is a permutation matrix with invertible entries**:
for all sectors there is a bijection `f` of summand paths with `σ p q = 0` for `q ≠ f p` and
`σ p (f p)` invertible. -/
def SigmaPermutation (c : P.CrossCoeff) (i j : I) (ν : X) : Prop :=
  ∀ t s : Sector I, ∃ f : SPath (wd D ν [up j, dn i]) t s ≃ SPath (wd D ν [dn i, up j]) t s,
    (∀ p q (Z : P.H s), q ≠ f p → P.sigmaEntry c i j ν p q Z = 0) ∧
      ∀ p (Z : P.H s), IsIso (P.sigmaEntry c i j ν p (f p) Z)

/-- The entry of the leftward crossing diagram is the leftward crossing image. -/
theorem compDiag_lcrossL (gens : P.Generators) (i j : I) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν [dn i, up j]) s t) (q : SPath (wd D ν [up j, dn i]) s t) (Z : P.H t) :
    compDiag gens (SKM.mkD D ν (SKM.lcrossL i j) (SKM.sChain_lcrossL i j)) p q Z =
      gens.lcross i j ν p q Z := by
  show compList gens (a := SKM.ob D ν [dn i, up j]) (b := SKM.ob D ν [up j, dn i])
    [SKM.lay D ν [] (SKM.Shape.lcross i j) []] ((SKM.sChain_lcrossL i j).chain D ν) p q Z = _
  erw [compList_one]
  simp only [SPath.cast_self, eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [compLayer_eq_of_path gens (SKM.lay D ν [] (SKM.Shape.lcross i j) []) (.nil s) p q
    (.nil t) p q (SPath.append_nil_pair p) (SPath.append_nil_pair q) Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The entry of the sideways crossing diagram for the swapped generators. -/
theorem compDiag_sigmaL_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) (i j : I) (ν : X)
    {t s : Sector I} (p : SPath (wd D ν [up j, dn i]) t s)
    (q : SPath (wd D ν [dn i, up j]) t s) (Z : P.H s) :
    compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.sigmaL i j) (SKM.sChain_sigmaL i j)) p q Z =
      P.sigmaEntry c i j ν p q Z :=
  compList_sigmaL_swappedGens c L i j ν p q Z

open Classical in
/-- **The leftward crossing is a right inverse of the sideways crossing** for distinct
colours, entry by entry, when the matrix of `σ` is a permutation matrix with invertible
entries. -/
theorem sigma_lcross_sum {c : P.CrossCoeff} {i j : I} {ν : X} (hσ : P.SigmaPermutation c i j ν)
    {t s : Sector I} [Fintype (SPath (wd D ν [dn i, up j]) t s)]
    (p q : SPath (wd D ν [up j, dn i]) t s) (Z : P.H s) :
    ∑ m : SPath (wd D ν [dn i, up j]) t s,
      P.sigmaEntry c i j ν p m Z ≫ P.lcrossNeImage c i j ν m q Z =
      if hpq : p = q then eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0 := by
  obtain ⟨f, hz, hi⟩ := hσ t s
  rw [Finset.sum_eq_single (f p) (fun m _ hm => by rw [hz p m Z hm, Limits.zero_comp])
    (by simp)]
  by_cases hpq : p = q
  · subst hpq
    have := hi p Z
    rw [lcrossNeImage_of_isIso, IsIso.hom_inv_id]
    simp
  · have hf : f p ≠ f q := fun h => hpq (f.injective h)
    rw [lcrossNeImage_eq_zero c i j ν _ _ Z (hz q (f p) Z hf), Limits.comp_zero]
    simp [hpq]

open Classical in
/-- **The leftward crossing is a left inverse of the sideways crossing** for distinct
colours, entry by entry, when the matrix of `σ` is a permutation matrix with invertible
entries. -/
theorem lcross_sigma_sum {c : P.CrossCoeff} {i j : I} {ν : X} (hσ : P.SigmaPermutation c i j ν)
    {t s : Sector I} [Fintype (SPath (wd D ν [up j, dn i]) t s)]
    (p q : SPath (wd D ν [dn i, up j]) t s) (Z : P.H s) :
    ∑ m : SPath (wd D ν [up j, dn i]) t s,
      P.lcrossNeImage c i j ν p m Z ≫ P.sigmaEntry c i j ν m q Z =
      if hpq : p = q then eqToHom (congrArg (fun r => (P.pathFunctor r).obj Z) hpq) else 0 := by
  obtain ⟨f, hz, hi⟩ := hσ t s
  rw [Finset.sum_eq_single (f.symm p) (fun m _ hm => by
    rw [lcrossNeImage_eq_zero c i j ν _ _ Z (hz m p Z (fun h => hm (by simp [h]))),
      Limits.zero_comp]) (by simp)]
  have hi' := hi (f.symm p) Z
  rw [Equiv.apply_symm_apply] at hi'
  by_cases hpq : p = q
  · subst hpq
    rw [lcrossNeImage_of_isIso, IsIso.inv_hom_id]
    simp
  · rw [hz (f.symm p) q Z (by rw [Equiv.apply_symm_apply]; exact Ne.symm hpq), Limits.comp_zero]
    simp [hpq]

/-- The distinct-colour inversion relations `invNe₁`, `invNe₂`. -/
def IsInvNe : SKM.Rel D → Prop
  | .invNe₁ .. | .invNe₂ .. => True
  | _ => False

/-- **The equal-colour leftward data invert the augmented maps** (1.13), (1.14): every
equal-colour inversion relation (`invP₁`–`invP₅`, `invM₁`–`invM₅`) holds entrywise for the
swapped generators. These identities characterize the leftward crossing `Fᵢ Eᵢ → Eᵢ Fᵢ` and
the `♦`-cups and caps as the components of the inverses of the augmented maps.

The identities are required only when the rightmost sector carries the weight of the right
region of the relation (`P.wt t = (dom r).endR`): these are the entries that the layer
representation evaluates, and the augmented maps are not invertible at the other sectors
(the number of dotted windows depends on the weight). -/
def LeftwardData.IsInverse (L : P.LeftwardData) (c : P.CrossCoeff) : Prop :=
  ∀ r : SKM.Rel D, relGroup r = .inversion → ¬ IsInvNe r → ∀ {s t : Sector I}
    (p : SPath ((SKM.pres D Sc).dom r).word s t) (q : SPath ((SKM.pres D Sc).cod r).word s t)
    (Z : P.H t), P.wt t = ((SKM.pres D Sc).dom r).endR →
      compEval (P.swappedGens c L) ((SKM.pres D Sc).rel r) p q Z = 0

/-- The equal-colour leftward data vanish at the sectors whose rightmost sector does not carry
the weight `ν` of the right region. Only the weight-matched entries enter the layer
representation; this normalizes the others. -/
def LeftwardData.VanishesOffWeight (L : P.LeftwardData) : Prop :=
  (∀ (i : I) (ν : X) {t s : Sector I} (p : SPath (wd D ν (SKM.Shape.lcross i i).dom) t s)
      (p' : SPath (wd D ν (SKM.Shape.lcross i i).cod) t s) (Z : P.H s),
      P.wt s ≠ ν → L.lcrossSame i ν p p' Z = 0) ∧
  (∀ (i : I) (n : ℕ) (ν : X) {t s : Sector I} (p : SPath (wd D ν (SKM.Shape.dcup i n).dom) t s)
      (p' : SPath (wd D ν (SKM.Shape.dcup i n).cod) t s) (Z : P.H s),
      P.wt s ≠ ν → L.dcup i n ν p p' Z = 0) ∧
  (∀ (i : I) (n : ℕ) (ν : X) {t s : Sector I} (p : SPath (wd D ν (SKM.Shape.dcap i n).dom) t s)
      (p' : SPath (wd D ν (SKM.Shape.dcap i n).cod) t s) (Z : P.H s),
      P.wt s ≠ ν → L.dcap i n ν p p' Z = 0)

variable {Gs Ys : ∀ s, P.H s}

/-- **`InversionRelations` for the swapped layer representation**: the relations
(1.11)–(1.14) hold, whiskered arbitrarily, when the matrices of the sideways crossings of
distinct colours are permutation matrices with invertible entries and the equal-colour
leftward data invert the augmented maps. -/
theorem inversionRelations {c : P.CrossCoeff} {L : P.LeftwardData}
    (hσ : ∀ i j ν, i ≠ j → P.SigmaPermutation c i j ν) (hL : L.IsInverse c) :
    InversionRelations Sc (P.layerRep Gs Ys (P.swappedGens c L)) := by
  classical
  intro r hr
  refine relHolds_of_compEval_wt _ r fun p q Z hw => ?_
  cases r with
  | invNe₁ i j ν hij =>
    show compEval (P.swappedGens c L) (a := SKM.ob D ν [up j, dn i])
      (b := SKM.ob D ν [up j, dn i]) (SKM.relation D Sc (.invNe₁ i j ν hij)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_dg_append _ ν (SKM.sigmaL i j) (SKM.lcrossL i j)
      (SKM.sChain_sigmaL i j) (SKM.sChain_lcrossL i j), compEval_of]
    have hs : ∀ m : SPath (wd D ν [dn i, up j]) _ _,
        compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.sigmaL i j) (SKM.sChain_sigmaL i j))
          p m Z ≫ compDiag (P.swappedGens c L)
            (SKM.mkD D ν (SKM.lcrossL i j) (SKM.sChain_lcrossL i j)) m q Z =
        P.sigmaEntry c i j ν p m Z ≫ P.lcrossNeImage c i j ν m q Z := fun m => by
      erw [compDiag_sigmaL_swappedGens, compDiag_lcrossL, P.swappedGens_lcross_of_ne c L hij]
    rw [sub_eq_zero]
    simp only [hs]
    let : ∀ a b, Fintype (SPath (wd D ν [dn i, up j]) a b) := fun _ _ => Fintype.ofFinite _
    erw [sigma_lcross_sum (hσ i j ν hij), compDiag_id]
  | invNe₂ i j ν hij =>
    show compEval (P.swappedGens c L) (a := SKM.ob D ν [dn i, up j])
      (b := SKM.ob D ν [dn i, up j]) (SKM.relation D Sc (.invNe₂ i j ν hij)) p q Z = 0
    simp only [SKM.relation]
    rw [compEval_sub, compEval_dg_append _ ν (SKM.lcrossL i j) (SKM.sigmaL i j)
      (SKM.sChain_lcrossL i j) (SKM.sChain_sigmaL i j), compEval_of]
    have hs : ∀ m : SPath (wd D ν [up j, dn i]) _ _,
        compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.lcrossL i j) (SKM.sChain_lcrossL i j))
          p m Z ≫ compDiag (P.swappedGens c L)
            (SKM.mkD D ν (SKM.sigmaL i j) (SKM.sChain_sigmaL i j)) m q Z =
        P.lcrossNeImage c i j ν p m Z ≫ P.sigmaEntry c i j ν m q Z := fun m => by
      erw [compDiag_sigmaL_swappedGens, compDiag_lcrossL, P.swappedGens_lcross_of_ne c L hij]
    rw [sub_eq_zero]
    simp only [hs]
    let : ∀ a b, Fintype (SPath (wd D ν [up j, dn i]) a b) := fun _ _ => Fintype.ofFinite _
    erw [lcross_sigma_sum (hσ i j ν hij), compDiag_id]
  | _ => exact hL _ hr (by simp [IsInvNe]) p q Z hw

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
