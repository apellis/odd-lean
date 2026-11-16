import OddMath.QuiverHecke.SwappedAssembly.PointwiseLeftwardInverse

/-! # Supernaturality of leftward inverses after restricting inputs

Brundan–Ellis (1.13)–(1.14): the inverse-matrix uniqueness argument
applies after any superfunctor on the input category. In particular,
local inverse identities on a full supported subcategory suffice; no
inverse identities on unrelated raw Hom inputs are needed.
-/
noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
universe u uB vB wB uC vC
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{wB,vB} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear k C] [Supercategory k C]

/-- Positive augmented inverse entries are supernatural on the prescribed
input functor whenever their five local inverse identities hold there. -/
theorem leftward_supernatural_of_posInverseAt_comp
    (c : P.CrossCoeff) (L : P.LeftwardData) (hc : c.IsSupernatural)
    (i : I) (ν : X) (t s : Sector I) (J : C ⥤ P.H s) [J.Additive]
    [J.Linear k] [IsSuperfunctor k J]
    (hL : ∀ Z, P.PosInverseAt c i ν t s (J.obj Z)
      (fun q p => L.lcrossSame i ν q p (J.obj Z))
      (fun n r p => L.dcup i n ν r p (J.obj Z))) :
    (∀ (q : SPath (wd D ν [dn i,up i]) t s) (p : SPath (wd D ν [up i,dn i]) t s),
      IsSupernatural k (D.parity i * D.parity i)
        (F := J ⋙ P.pathFunctor q) (G := J ⋙ P.pathFunctor p)
        (fun Z => L.lcrossSame i ν q p (J.obj Z))) ∧
    (∀ (n : Fin (D.h i ν).toNat) (r : SPath (wd D ν []) t s)
      (p : SPath (wd D ν [up i,dn i]) t s),
      IsSupernatural k (((n : ℕ) : ZMod 2) * D.parity i)
        (F := J ⋙ P.pathFunctor r) (G := J ⋙ P.pathFunctor p)
        (fun Z => L.dcup i n ν r p (J.obj Z))) := by
  let lc : ∀ (q : SPath (wd D ν [dn i,up i]) t s)
      (p : SPath (wd D ν [up i,dn i]) t s) (Z : C),
      (P.pathFunctor q).obj (J.obj Z) ⟶ (P.pathFunctor p).obj (J.obj Z) :=
    fun q p Z => L.lcrossSame i ν q p (J.obj Z)
  let cup : ∀ (n : ℕ) (r : SPath (wd D ν []) t s)
      (p : SPath (wd D ν [up i,dn i]) t s) (Z : C),
      (P.pathFunctor r).obj (J.obj Z) ⟶ (P.pathFunctor p).obj (J.obj Z) :=
    fun n r p Z => L.dcup i n ν r p (J.obj Z)
  have hL' (Z : C) : P.PosInverseAt c i ν t s (J.obj Z)
      (fun q p => lc q p Z) (fun n r p => cup n r p Z) := hL Z
  let A := SPath (wd D ν [up i,dn i]) t s
  let A' := SPath (wd D ν [dn i,up i]) t s
  let A₀ := SPath (wd D ν []) t s
  let N := (D.h i ν).toNat
  let : Fintype A := Fintype.ofFinite _
  let : Fintype A' := Fintype.ofFinite _
  let : Fintype A₀ := Fintype.ofFinite _
  let F : A → C ⥤ P.H t := fun p => J ⋙ P.pathFunctor p
  let G : A' ⊕ (Fin N × A₀) → C ⥤ P.H t :=
    Sum.elim (fun q => J ⋙ P.pathFunctor q) (fun nr => J ⋙ P.pathFunctor nr.2)
  let ρ : A' ⊕ (Fin N × A₀) → ZMod 2 :=
    Sum.elim (fun _ => D.parity i * D.parity i) (fun nr => ((nr.1 : ℕ) : ZMod 2) * D.parity i)
  let a : ∀ p y Z, (F p).obj Z ⟶ (G y).obj Z := fun p y Z =>
    Sum.rec (motive := fun y => (F p).obj Z ⟶ (G y).obj Z)
      (fun q => P.sigmaEntry c i i ν p q (J.obj Z))
      (fun nr => P.epsEntry c i nr.1 ν p nr.2 (J.obj Z)) y
  let b : ∀ y p Z, (G y).obj Z ⟶ (F p).obj Z := fun y p Z =>
    Sum.rec (motive := fun y => (G y).obj Z ⟶ (F p).obj Z)
      (fun q => -lc q p Z)
      (fun nr => cup nr.1 nr.2 p Z) y
  have ha : ∀ p y, IsSupernatural k (ρ y) (a p y) := by
    rintro p (q | ⟨n,r⟩)
    · exact (sigmaEntry_supernatural c hc i i ν p q).whiskerLeft J
    · simpa only [a,F,G,ρ,Sum.elim_inr,compDiag_epsL_swappedGens] using
        (compDiag_epsL_supernatural c L hc i n ν p r).whiskerLeft J
  have hab : ∀ p p' Z, ∑ y, a p y Z ≫ b y p' Z = famDelta F p p' Z := by
    intro p p' Z
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
    change (∑ q : A', P.sigmaEntry c i i ν p q (J.obj Z) ≫
        (-lc q p' Z)) +
      (∑ n : Fin N, ∑ r : A₀, P.epsEntry c i n ν p r (J.obj Z) ≫
        cup n r p' Z) = _
    rw [Fin.sum_univ_eq_sum_range (fun n => ∑ r : A₀,
      P.epsEntry c i n ν p r (J.obj Z) ≫ cup n r p' Z) N]
    have hδ : famDelta F p p' Z = famDelta (fun p : A => P.pathFunctor p) p p' (J.obj Z) := rfl
    rw [hδ]
    simpa only [N,Preadditive.comp_neg,Finset.sum_neg_distrib] using (hL' Z).1 p p'
  have hba : ∀ y y' Z, ∑ p, b y p Z ≫ a p y' Z = famDelta G y y' Z := by
    rintro (q | ⟨n,r⟩) (q' | ⟨m,r'⟩) Z
    · change (∑ p : A, (-lc q p Z) ≫
        P.sigmaEntry c i i ν p q' (J.obj Z)) =
        famId (Sum.elim (fun q : A' => (P.pathFunctor q).obj (J.obj Z))
          (fun nr : Fin N × A₀ => (P.pathFunctor nr.2).obj (J.obj Z))) (.inl q) (.inl q')
      rw [famId_inl,P.famId_path]
      have h := (hL' Z).2.1 q q'
      change (∑ p : A, lc q p Z ≫ P.sigmaEntry c i i ν p q' (J.obj Z)) =
        -famDelta (fun q : A' => P.pathFunctor q) q q' (J.obj Z) at h
      simpa only [Preadditive.neg_comp,Finset.sum_neg_distrib,neg_neg] using congrArg Neg.neg h
    · change (∑ p : A, (-lc q p Z) ≫
        P.epsEntry c i m ν p r' (J.obj Z)) =
        famId (Sum.elim (fun q : A' => (P.pathFunctor q).obj (J.obj Z))
          (fun nr : Fin N × A₀ => (P.pathFunctor nr.2).obj (J.obj Z))) (.inl q) (.inr (m,r'))
      rw [famId_inl_inr]
      simpa only [Preadditive.neg_comp,Finset.sum_neg_distrib,neg_eq_zero] using
        (hL' Z).2.2.1 m (Int.lt_toNat.mp m.isLt) q r'
    · change (∑ p : A, cup n r p Z ≫
        P.sigmaEntry c i i ν p q' (J.obj Z)) =
        famId (Sum.elim (fun q : A' => (P.pathFunctor q).obj (J.obj Z))
          (fun nr : Fin N × A₀ => (P.pathFunctor nr.2).obj (J.obj Z))) (.inr (n,r)) (.inl q')
      rw [famId_inr_inl]
      exact (hL' Z).2.2.2.1 n (Int.lt_toNat.mp n.isLt) r q'
    · change (∑ p : A, cup n r p Z ≫
        P.epsEntry c i m ν p r' (J.obj Z)) =
        famId (Sum.elim (fun q : A' => (P.pathFunctor q).obj (J.obj Z))
          (fun nr : Fin N × A₀ => (P.pathFunctor nr.2).obj (J.obj Z))) (.inr (n,r)) (.inr (m,r'))
      rw [famId_inr,famId_prod (Yb := fun r : A₀ => (P.pathFunctor r).obj (J.obj Z)),P.famId_path]
      simpa only [Fin.ext_iff,eq_comm] using
        (hL' Z).2.2.2.2 m n (Int.lt_toNat.mp m.isLt) (Int.lt_toNat.mp n.isLt) r r'
  refine ⟨fun q p => ?_,fun n r p => ?_⟩
  · have h := IsSupernatural.neg (isSupernatural_of_inverse_target ρ a b ha hab hba (.inl q) p)
    simpa only [b,lc,ρ,F,G,Sum.elim_inl,neg_neg] using h
  · exact isSupernatural_of_inverse_target ρ a b ha hab hba (.inr (n,r)) p

/-- Negative augmented inverse entries are supernatural on the prescribed
input functor whenever their five local inverse identities hold there. -/
theorem leftward_supernatural_of_negInverseAt_comp
    (c : P.CrossCoeff) (L : P.LeftwardData) (hc : c.IsSupernatural)
    (i : I) (ν : X) (t s : Sector I) (J : C ⥤ P.H s) [J.Additive]
    [J.Linear k] [IsSuperfunctor k J]
    (hL : ∀ Z, P.NegInverseAt c i ν t s (J.obj Z)
      (fun q p => L.lcrossSame i ν q p (J.obj Z))
      (fun n q r => L.dcap i n ν q r (J.obj Z))) :
    (∀ (q : SPath (wd D ν [dn i,up i]) t s) (p : SPath (wd D ν [up i,dn i]) t s),
      IsSupernatural k (D.parity i * D.parity i)
        (F := J ⋙ P.pathFunctor q) (G := J ⋙ P.pathFunctor p)
        (fun Z => L.lcrossSame i ν q p (J.obj Z))) ∧
    (∀ (n : Fin (-D.h i ν).toNat) (q : SPath (wd D ν [dn i,up i]) t s)
      (r : SPath (wd D ν []) t s),
      IsSupernatural k (((n : ℕ) : ZMod 2) * D.parity i)
        (F := J ⋙ P.pathFunctor q) (G := J ⋙ P.pathFunctor r)
        (fun Z => L.dcap i n ν q r (J.obj Z))) := by
  let lc : ∀ (q : SPath (wd D ν [dn i,up i]) t s)
      (p : SPath (wd D ν [up i,dn i]) t s) (Z : C),
      (P.pathFunctor q).obj (J.obj Z) ⟶ (P.pathFunctor p).obj (J.obj Z) :=
    fun q p Z => L.lcrossSame i ν q p (J.obj Z)
  let cap : ∀ (n : ℕ) (q : SPath (wd D ν [dn i,up i]) t s)
      (r : SPath (wd D ν []) t s) (Z : C),
      (P.pathFunctor q).obj (J.obj Z) ⟶ (P.pathFunctor r).obj (J.obj Z) :=
    fun n q r Z => L.dcap i n ν q r (J.obj Z)
  have hL' (Z : C) : P.NegInverseAt c i ν t s (J.obj Z)
      (fun q p => lc q p Z) (fun n q r => cap n q r Z) := hL Z
  let A := SPath (wd D ν [up i,dn i]) t s
  let A' := SPath (wd D ν [dn i,up i]) t s
  let A₀ := SPath (wd D ν []) t s
  let N := (-D.h i ν).toNat
  let : Fintype A := Fintype.ofFinite _
  let : Fintype A' := Fintype.ofFinite _
  let : Fintype A₀ := Fintype.ofFinite _
  let F : A ⊕ (Fin N × A₀) → C ⥤ P.H t :=
    Sum.elim (fun p => J ⋙ P.pathFunctor p) (fun nr => J ⋙ P.pathFunctor nr.2)
  let G : A' → C ⥤ P.H t := fun q => J ⋙ P.pathFunctor q
  let ρ : A ⊕ (Fin N × A₀) → ZMod 2 :=
    Sum.elim (fun _ => D.parity i * D.parity i) (fun nr => ((nr.1 : ℕ) : ZMod 2) * D.parity i)
  let a : ∀ x q Z, (F x).obj Z ⟶ (G q).obj Z := fun x q Z =>
    Sum.rec (motive := fun x => (F x).obj Z ⟶ (G q).obj Z)
      (fun p => -P.sigmaEntry c i i ν p q (J.obj Z))
      (fun nr => P.etaEntry c i nr.1 ν nr.2 q (J.obj Z)) x
  let b : ∀ q x Z, (G q).obj Z ⟶ (F x).obj Z := fun q x Z =>
    Sum.rec (motive := fun x => (G q).obj Z ⟶ (F x).obj Z)
      (fun p => lc q p Z)
      (fun nr => cap nr.1 q nr.2 Z) x
  have ha : ∀ x q, IsSupernatural k (ρ x) (a x q) := by
    rintro (p | ⟨n,r⟩) q
    · exact IsSupernatural.neg ((sigmaEntry_supernatural c hc i i ν p q).whiskerLeft J)
    · simpa only [a,F,G,ρ,Sum.elim_inr,compDiag_etaL_swappedGens] using
        (compDiag_etaL_supernatural c L hc i n ν r q).whiskerLeft J
  have hab : ∀ x x' Z, ∑ q, a x q Z ≫ b q x' Z = famDelta F x x' Z := by
    rintro (p | ⟨n,r⟩) (p' | ⟨m,r'⟩) Z
    · change (∑ q : A', (-P.sigmaEntry c i i ν p q (J.obj Z)) ≫
        lc q p' Z) =
        famId (Sum.elim (fun p : A => (P.pathFunctor p).obj (J.obj Z))
          (fun nr : Fin N × A₀ => (P.pathFunctor nr.2).obj (J.obj Z))) (.inl p) (.inl p')
      rw [famId_inl,P.famId_path]
      have h := (hL' Z).2.1 p p'
      change (∑ q : A', P.sigmaEntry c i i ν p q (J.obj Z) ≫ lc q p' Z) =
        -famDelta (fun p : A => P.pathFunctor p) p p' (J.obj Z) at h
      simpa only [Preadditive.neg_comp,Finset.sum_neg_distrib,neg_neg] using congrArg Neg.neg h
    · change (∑ q : A', (-P.sigmaEntry c i i ν p q (J.obj Z)) ≫
        cap m q r' Z) =
        famId (Sum.elim (fun p : A => (P.pathFunctor p).obj (J.obj Z))
          (fun nr : Fin N × A₀ => (P.pathFunctor nr.2).obj (J.obj Z))) (.inl p) (.inr (m,r'))
      rw [famId_inl_inr]
      simpa only [Preadditive.neg_comp,Finset.sum_neg_distrib,neg_eq_zero] using
        (hL' Z).2.2.2.1 m (Int.lt_toNat.mp m.isLt) p r'
    · change (∑ q : A', P.etaEntry c i n ν r q (J.obj Z) ≫
        lc q p' Z) =
        famId (Sum.elim (fun p : A => (P.pathFunctor p).obj (J.obj Z))
          (fun nr : Fin N × A₀ => (P.pathFunctor nr.2).obj (J.obj Z))) (.inr (n,r)) (.inl p')
      rw [famId_inr_inl]
      exact (hL' Z).2.2.1 n (Int.lt_toNat.mp n.isLt) r p'
    · change (∑ q : A', P.etaEntry c i n ν r q (J.obj Z) ≫
        cap m q r' Z) =
        famId (Sum.elim (fun p : A => (P.pathFunctor p).obj (J.obj Z))
          (fun nr : Fin N × A₀ => (P.pathFunctor nr.2).obj (J.obj Z))) (.inr (n,r)) (.inr (m,r'))
      rw [famId_inr,famId_prod (Yb := fun r : A₀ => (P.pathFunctor r).obj (J.obj Z)),P.famId_path]
      simpa only [Fin.ext_iff] using
        (hL' Z).2.2.2.2 n m (Int.lt_toNat.mp n.isLt) (Int.lt_toNat.mp m.isLt) r r'
  have hba : ∀ q q' Z, ∑ x, b q x Z ≫ a x q' Z = famDelta G q q' Z := by
    intro q q' Z
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
    change (∑ p : A, lc q p Z ≫
        (-P.sigmaEntry c i i ν p q' (J.obj Z))) +
      (∑ n : Fin N, ∑ r : A₀, cap n q r Z ≫
        P.etaEntry c i n ν r q' (J.obj Z)) = _
    rw [Fin.sum_univ_eq_sum_range (fun n => ∑ r : A₀,
      cap n q r Z ≫ P.etaEntry c i n ν r q' (J.obj Z)) N]
    have hδ : famDelta G q q' Z = famDelta (fun q : A' => P.pathFunctor q) q q' (J.obj Z) := rfl
    rw [hδ]
    simpa only [N,Preadditive.comp_neg,Finset.sum_neg_distrib] using (hL' Z).1 q q'
  exact ⟨fun q p => isSupernatural_of_inverse_source ρ a b ha hab hba q (.inl p),
    fun n q r => isSupernatural_of_inverse_source ρ a b ha hab hba q (.inr (n,r))⟩

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
