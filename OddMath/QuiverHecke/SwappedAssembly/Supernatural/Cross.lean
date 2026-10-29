/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Basic
import OddMath.QuiverHecke.SwappedAssembly.Generators.Cross

/-! # Supernaturality of the swapped upward crossing

The image of the upward crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` of Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, Definition 1.5, in the swapped Hom construction
(`OddMath/QuiverHecke/SwappedAssembly/Generators/Cross.lean`) is supernatural of parity
`pᵢ pⱼ`, entry by entry (`docs/Nondegeneracy/SwappedActionAssembly.md`, end of §3).

The reduction of a two-letter matrix to its components at sectors in general position is
`twoTwo_supernatural`. The components are composites of the factor crossings and dots of the
Rouquier families, whiskered by Hom-sector functors, of associators, of the comparisons of the
parity shifts and of the mixed interchange `J`; each is supernatural of its parity. The
polynomial `Q` is even: its monomials of odd parity have zero coefficient by the parity
conditions on the scalars `sᵢⱼ^{pq}` and on the `dᵢⱼ` (Brundan–Ellis (1.4), (1.6)).

For equal colours, the coefficient `a` of the mixed block is data; its supernaturality, of
parity `pᵢ`, is the hypothesis `CrossCoeff.IsSupernatural`.

Main declarations: `ProbeReservoir.twoTwo_supernatural`,
`ProbeReservoir.crossImage_supernatural`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct

universe u

section Generic

variable {R : Type*} [CommRing R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type*} [Category D] [Preadditive D] [Linear R D] [Supercategory R D]

theorem IsSupernatural.add {p : ZMod 2} {F G : C ⥤ D} {x y : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) (hy : IsSupernatural R p y) :
    IsSupernatural R p fun X => x X + y X where
  mem X := Submodule.add_mem _ (hx.mem X) (hy.mem X)
  naturality hf := by
    rw [Preadditive.comp_add, hx.naturality hf, hy.naturality hf, ← smul_add,
      Preadditive.add_comp]

theorem IsSupernatural.smul {p : ZMod 2} {F G : C ⥤ D} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) (r : R) : IsSupernatural R p fun X => r • x X where
  mem X := Submodule.smul_mem _ r (hx.mem X)
  naturality hf := by
    rw [Linear.comp_smul, hx.naturality hf, smul_comm, Linear.smul_comp]

theorem IsSupernatural.neg {p : ZMod 2} {F G : C ⥤ D} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) : IsSupernatural R p fun X => -x X where
  mem X := Submodule.neg_mem _ (hx.mem X)
  naturality hf := by
    rw [Preadditive.comp_neg, hx.naturality hf, Preadditive.neg_comp, smul_neg]

theorem IsSupernatural.sum {p : ZMod 2} {F G : C ⥤ D} {ι : Type*} (s : Finset ι)
    {x : ι → ∀ X, F.obj X ⟶ G.obj X} (hx : ∀ a ∈ s, IsSupernatural R p (x a)) :
    IsSupernatural R p fun X => ∑ a ∈ s, x a X := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSupernatural_zero (R := R) p (F := F) (G := G)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact IsSupernatural.add (hx a (Finset.mem_insert_self a s))
      (ih fun b hb => hx b (Finset.mem_insert_of_mem hb))

theorem IsSupernatural.of_parity_eq {p q : ZMod 2} {F G : C ⥤ D}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R p x) (h : p = q) :
    IsSupernatural R q x := h ▸ hx

/-- Products of supernatural endomorphism families multiply in the order of `End`. -/
theorem IsSupernatural.mul {p q : ZMod 2} {F : C ⥤ D} [F.Additive] [F.Linear R]
    {x y : ∀ X, End (F.obj X)} (hx : IsSupernatural R p x) (hy : IsSupernatural R q y) :
    IsSupernatural R (p + q) fun X => x X * y X :=
  IsSupernatural.of_parity_eq (hy.comp hx) (add_comm q p)

theorem IsSupernatural.pow {p : ZMod 2} {F : C ⥤ D} [F.Additive] [F.Linear R]
    {x : ∀ X, End (F.obj X)} (hx : IsSupernatural R p x) (n : ℕ) :
    IsSupernatural R (n * p) fun X => x X ^ n := by
  induction n with
  | zero => simpa using isSupernatural_id (R := R) (F := F)
  | succ n ih =>
    simp only [pow_succ]
    exact IsSupernatural.of_parity_eq (IsSupernatural.mul ih hx) (by push_cast; ring)

theorem isSupernatural_one {F : C ⥤ D} [F.Linear R] :
    IsSupernatural R 0 fun X => (1 : End (F.obj X)) :=
  isSupernatural_id

end Generic

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]

/-! ## Comparisons of Hom functors -/

section HomFunctors

omit [∀ a b : B, PiSupercategory k (a ⟶ b)]

/-- Precomposition by a composite is the composite of the precompositions. -/
def homPreComp {a b c d : B} (E : a ⟶ b) (F : b ⟶ c) :
    homPre (k := k) (c := d) F ⋙ homPre (k := k) E ≅ homPre (k := k) (E ≫ F) :=
  NatIso.ofComponents (fun Z => (associator E F Z).symm) (by
    intro Z Z' η
    exact TwoSupercategory.associator_inv_naturality_right (R := k) E F η)

theorem homPreComp_hom_mem {a b c d : B} (E : a ⟶ b) (F : b ⟶ c) (Z : c ⟶ d) :
    (homPreComp (k := k) E F).hom.app Z ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E F Z)

theorem homPreComp_inv_mem {a b c d : B} (E : a ⟶ b) (F : b ⟶ c) (Z : c ⟶ d) :
    (homPreComp (k := k) E F).inv.app Z ∈ parity (R := k) _ _ 0 :=
  TwoSupercategory.associator_hom_mem (R := k) E F Z

theorem homSectorInterchange_inv_mem {a b c d : B} (E : a ⟶ b) (F : c ⟶ d) (Z : b ⟶ c) :
    (homSectorInterchange (k := k) E F).inv.app Z ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E Z F)

end HomFunctors

/-- **The mixed interchange `J` is supernatural**, of the sum of the two shift parities. -/
theorem homMixedInterchange_supernatural {a b c d : B} (E : a ⟶ b) (F : c ⟶ d)
    (κ τ : ZMod 2) :
    IsSupernatural k (κ + τ)
      (F := homPost (k := k) F ⋙ homParityShift (k := k) κ ⋙ homPre (k := k) E)
      (G := homPre (k := k) E ⋙ homPost (k := k) F ⋙ homParityShift (k := k) τ)
      (fun Z => (homMixedInterchange (k := k) E F κ τ Z).hom) := by
  have hA := ((homParityShiftDatum (k := k) κ).supernatural.whiskerLeft
    (homPost (k := k) (a := b) F)).whiskerRight (homPre (k := k) E)
  have hB := isSupernatural_of_natTrans (R := k) (homSectorInterchange (k := k) E F).inv
    (homSectorInterchange_inv_mem E F)
  have hC := (isSupernatural_iso_inv (k := k)
    (F := homParityShift (k := k) (C := a ⟶ d) τ) (G := 𝟭 _)
    (fun Z => (homParityShiftDatum (k := k) (C := a ⟶ d) τ).iso Z)
    (homParityShiftDatum (k := k) (C := a ⟶ d) τ).supernatural).whiskerLeft
      (homPre (k := k) E ⋙ homPost (k := k) (a := a) F)
  have := hA.comp (hB.comp hC)
  simp only [zero_add] at this
  exact this

variable {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-! ## Two-letter matrices -/

/-- The entry of a matrix between two-letter words at the paths through given summands. -/
theorem twoTwo_two (c₁ c₂ d₁ d₂ : Col I X) (f : P.TwoEntry c₁ c₂ d₁ d₂)
    {t s s' : Sector I} (σ₁ σ₂ τ₁ τ₂ : Bool) (hv₁ : StepValid c₁.l σ₁ t)
    (hv₂ : StepValid c₂.l σ₂ (nextSector c₁.l σ₁ t)) (hw₁ : StepValid d₁.l τ₁ t)
    (hw₂ : StepValid d₂.l τ₂ (nextSector d₁.l τ₁ t))
    (e : nextSector c₂.l σ₂ (nextSector c₁.l σ₁ t) = s)
    (e' : nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t) = s') (hs : s = s') (Z : P.H s')
    (Z' : P.H (nextSector d₂.l τ₂ (nextSector d₁.l τ₁ t))) (hZ : HEq Z' Z) :
    P.twoTwo c₁ c₂ d₁ d₂ f (SPath.two σ₁ σ₂ hv₁ hv₂ e) (SPath.two τ₁ τ₂ hw₁ hw₂ e') hs Z =
      eqToHom (by subst e e'; obtain rfl := eq_of_heq hZ; rfl) ≫
        f t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ (e.trans (hs.trans e'.symm)) Z' ≫
        eqToHom (by subst e e'; obtain rfl := eq_of_heq hZ; rfl) := by
  subst e e'; obtain rfl := eq_of_heq hZ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- **Supernaturality of a matrix between two-letter words** from that of its components. -/
theorem twoTwo_supernatural (c₁ c₂ d₁ d₂ : Col I X) (p : ZMod 2) (f : P.TwoEntry c₁ c₂ d₁ d₂)
    (hf : ∀ t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ hs, IsSupernatural k p
      (F := P.castH hs ⋙ P.step c₂.l σ₂ _ hv₂ ⋙ P.step c₁.l σ₁ t hv₁)
      (G := P.step d₂.l τ₂ _ hw₂ ⋙ P.step d₁.l τ₁ t hw₁)
      (f t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ hs))
    {t s : Sector I} (q : SPath [c₁, c₂] t s) (q' : SPath [d₁, d₂] t s) :
    IsSupernatural k p (fun Z => P.twoTwo c₁ c₂ d₁ d₂ f q q' rfl Z) := by
  obtain ⟨σ₁, σ₂, hv₁, hv₂, e, rfl⟩ := SPath.exists_eq_two q
  subst e
  obtain ⟨τ₁, τ₂, hw₁, hw₂, e', rfl⟩ := SPath.exists_eq_two q'
  have hx := (hf t σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ e'.symm).whiskerLeft (P.castH e')
  have hF : P.pathFunctor (SPath.two (c₁ := c₁) (c₂ := c₂) σ₁ σ₂ hv₁ hv₂ rfl) =
      P.castH e' ⋙ P.castH e'.symm ⋙ P.step c₂.l σ₂ _ hv₂ ⋙ P.step c₁.l σ₁ t hv₁ := by
    rw [P.pathFunctor_two, ← Functor.assoc, P.castH_comp_castH, P.castH_rfl]
    rfl
  refine IsSupernatural.of_eq_conj hF (P.pathFunctor_two τ₁ τ₂ hw₁ hw₂ e') hx _
    (fun Z => Functor.congr_obj hF Z) (fun _ => by rw [P.pathFunctor_two]) fun Z => ?_
  rw [P.twoTwo_two c₁ c₂ d₁ d₂ f σ₁ σ₂ τ₁ τ₂ hv₁ hv₂ hw₁ hw₂ rfl e' rfl Z
    ((P.castH e').obj Z) (P.castH_obj_heq e' Z)]

/-! ## The mixed paths -/

/-- The mixed interchange `J` is supernatural of the parity of the crossing. -/
theorem mixedJ_supernatural (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t)) :
    IsSupernatural k (D.parity i * D.parity j)
      (F := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (G := P.step (true, i) true (nextSector (true, j) false t) trivial ⋙
        P.step (true, j) false t hR)
      (fun Z => (P.mixedJ i j t hR Z).hom) := by
  refine IsSupernatural.of_parity_eq (homMixedInterchange_supernatural (k := k)
    (P.T.E i (P.muP_preE i t)) (P.W.E j (P.muM_postE j hR))
    (homContentShift D j (t.1 + Finsupp.single i 1)) (homContentShift D j t.1)) ?_
  rw [homContentShift_add_single, add_comm, ← add_assoc, Supercategory.zmod2_add_self, zero_add, mul_comm]

/-- The inverse of the mixed interchange is supernatural of the parity of the crossing. -/
theorem mixedJ_inv_supernatural (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t)) :
    IsSupernatural k (D.parity i * D.parity j)
      (F := P.step (true, i) true (nextSector (true, j) false t) trivial ⋙
        P.step (true, j) false t hR)
      (G := P.step (true, j) false (nextSector (true, i) true t) hR ⋙
        P.step (true, i) true t trivial)
      (fun Z => (P.mixedJ i j t hR Z).inv) :=
  isSupernatural_iso_inv (k := k)
    (F := P.step (true, j) false (nextSector (true, i) true t) hR ⋙
      P.step (true, i) true t trivial)
    (G := P.step (true, i) true (nextSector (true, j) false t) trivial ⋙
      P.step (true, j) false t hR)
    (fun Z => P.mixedJ i j t hR Z) (P.mixedJ_supernatural i j t hR)

/-- The probe dot of the path `(P,R)` is supernatural of the parity of its colour. -/
theorem prPreDot_supernatural (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t)) :
    IsSupernatural k (D.parity i)
      (F := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (G := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (P.prPreDot i j t hR) := by
  have hx := ((homPreTransform (k := k)
    (c := P.W.obj (P.muM (nextSector (true, i) true t)))
    (P.T.dot i (P.muP_preE i t)) (P.T.dot_mem i _)).isSupernatural (D.parity i)).whiskerLeft
      (P.step (true, j) false _ hR)
  refine IsSupernatural.of_eq_conj
    (F := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
    (G := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
    rfl rfl hx _ (fun _ => rfl) (fun _ => rfl) fun Z => ?_
  simp only [homPreTransform, prPreDot, eqToHom_refl, Category.id_comp,
    Category.comp_id, ite_true]

/-- The reservoir dot of the path `(P,R)` is supernatural of the parity of its colour. -/
theorem prPostDot_supernatural (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t)) :
    IsSupernatural k (D.parity j)
      (F := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (G := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (P.prPostDot i j t hR) := by
  have hx := homContentPostDot_power_supernatural (k := k) P.T.obj P.W j
    (nextSector (true, i) true t).1 (P.muP (nextSector (true, i) true t)) (P.muM_postE j hR) 1
  simp only [Nat.cast_one, one_mul, pow_one] at hx
  exact hx.whiskerRight (P.step (true, i) true t trivial)

theorem natCast_dn_mul_parity (D : Datum I X) (i j : I) :
    (D.dn i j : ZMod 2) * D.parity i = 0 := by
  rcases parity_eq_zero_or_one (D.parity i) with h | h
  · rw [h, mul_zero]
  · rw [h, mul_one, ZMod.natCast_eq_zero_iff_even, ← Int.even_coe_nat]
    rcases le_or_gt 0 (D.d i j) with h0 | h0
    · rw [Datum.dn, Int.toNat_of_nonneg h0]
      exact D.even_d_of_odd h j
    · rw [Datum.dn, Int.toNat_eq_zero.mpr h0.le]
      exact Even.zero

/-- **The parameter polynomial `Q` is even**: its monomials of odd parity have zero
coefficient (Brundan–Ellis (1.4), (1.6)). -/
theorem mixedQ_supernatural (i j : I) (t : Sector I)
    (hR : StepValid (true, j) false (nextSector (true, i) true t)) :
    IsSupernatural k 0
      (F := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (G := P.step (true, j) false _ hR ⋙ P.step (true, i) true t trivial)
      (P.mixedQ i j t hR) := by
  unfold mixedQ
  split_ifs
  · exact IsSupernatural.smul isSupernatural_one _
  · refine IsSupernatural.add (IsSupernatural.add ?_ ?_)
      (IsSupernatural.sum _ fun p _ => IsSupernatural.sum _ fun q _ => ?_)
    · refine IsSupernatural.smul (IsSupernatural.of_parity_eq
        (IsSupernatural.pow (P.prPreDot_supernatural i j t hR) _) ?_) _
      exact natCast_dn_mul_parity D i j
    · refine IsSupernatural.smul (IsSupernatural.of_parity_eq
        (IsSupernatural.pow (P.prPostDot_supernatural i j t hR) _) ?_) _
      exact natCast_dn_mul_parity D j i
    · by_cases hs : Sc.s i j p q = 0
      · rw [hs]
        simpa only [zero_smul] using isSupernatural_zero (R := k) 0
      · have hp : (p : ZMod 2) * D.parity i = 0 := by
          rcases parity_eq_zero_or_one ((p : ZMod 2) * D.parity i) with h | h
          · exact h
          · exact absurd (Sc.s_eq_zero i j p q h) hs
        have hq : (q : ZMod 2) * D.parity j = 0 := by
          rcases parity_eq_zero_or_one ((q : ZMod 2) * D.parity j) with h | h
          · exact h
          · exact absurd ((Sc.s_symm i j p q).trans (Sc.s_eq_zero j i q p h)) hs
        refine IsSupernatural.smul (IsSupernatural.of_parity_eq (IsSupernatural.mul
          (IsSupernatural.pow (P.prPreDot_supernatural i j t hR) p)
          (IsSupernatural.pow (P.prPostDot_supernatural i j t hR) q)) ?_) _
        rw [hp, hq, add_zero]
