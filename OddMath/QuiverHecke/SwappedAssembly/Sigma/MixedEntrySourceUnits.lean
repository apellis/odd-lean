import OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntry
import OddMath.SKM.RouquierHomDistinctSourceUnits

/-! # Distinct-colour entries from source polynomial units

BE2 (1.11), in the swapped construction: the mixed entry only needs the
source polynomial unit criterion. The ELV application must discharge this
criterion using contentwise transpose bounds, rather than a global
nilpotence hypothesis. This module is an intermediate reduction.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB vB wB
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{wB, vB} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

theorem isIso_homDistinctMixedMateDot_of_pow_sourceUnits {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d}
    {F' : d ⟶ c} (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)
    {x : E ⟶ E} {y : E' ⟶ E'} {ex ey : ℕ}
    (hx : rouquierPower x ex ∈ parity (R := k) E E 0)
    (hy : rouquierPower y ey ∈ parity (R := k) E' E' 0)
    (hu : MixedPostSourceUnits E A κ H (rouquierPower x ex) (rouquierPower y ey)) (c : kˣ) (n : ℕ) {N}
    (hN : N ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ ex)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ ey)
      (fun _ => True) (fun _ => True) 1) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((c : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ (ex * n) +
        N)) := by
  have hX : mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ ex =
      mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') (rouquierPower x ex) :=
    whiskerRight_rouquierPower (k := k) x _ ex
  have hY : mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ ey =
      mixedPostTargetPostDot (k := k) E κ H (F' := F') (rouquierPower y ey) := by
    rw [whiskerLeft_rouquierPower (k := k), rouquierPower_eq_pow, ← map_rouquierPower,
      rouquierPower_eq_pow, whiskerLeft_rouquierPower (k := k)]
  rw [hX, hY] at hN
  rw [pow_mul, hX]
  exact homDistinctMixedMateDot_isIso_of_sourceUnits E A κ τ H hx hy hu c n hN

/-- Source-unit form of `isIso_homDistinctMixedMateDot_param`, for parameters without pure terms
(`ScalarData.NoPure`, a hypothesis of this route; see `BWWMixedEntry` for the general box). -/
theorem isIso_homDistinctMixedMateDot_param_sourceUnits (hn : Sc.NoPure) {a b c d : B}
    (E : a ⟶ b) {E' : c ⟶ d}
    {F' : d ⟶ c} (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)
    {i j : I} (hij : i ≠ j) {x : E ⟶ E} (hx : x ∈ parity (R := k) E E (D.parity i))
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' (D.parity j))
    (hu : MixedPostSourceUnits E A κ H
      (rouquierPower x (if D.parity i = 1 then 2 else 1))
      (rouquierPower y (if D.parity j = 1 then 2 else 1))) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      (if D.d i j = 0 then (Sc.t i j : k) • (1 : End (E ≫ (homParityShift (k := k) κ).obj
          (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) else
        (Sc.t i j : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^
            D.dn i j +
          (Sc.t j i : k) • mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ D.dn j i +
          ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
            Sc.s i j p q • (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ p *
              mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q))) := by
  set ex := if D.parity i = 1 then 2 else 1
  set ey := if D.parity j = 1 then 2 else 1
  have hx' : rouquierPower x ex ∈ parity (R := k) E E 0 := by
    have h := rouquierPower_mem (k := k) hx ex
    rwa [mul_parity_pow_eq_zero] at h
  have hy' : rouquierPower y ey ∈ parity (R := k) E' E' 0 := by
    have h := rouquierPower_mem (k := k) hy ey
    rwa [mul_parity_pow_eq_zero] at h
  set X := mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x
  set Y := mixedPostTargetPostDot (k := k) E κ H (F' := F') y
  have hmono : ∀ p q : ℕ, (p : ZMod 2) * D.parity i ≠ 1 → (q : ZMod 2) * D.parity j ≠ 1 →
      1 ≤ q → X ^ p * Y ^ q ∈ admissibleMonomials (k := k) (X ^ ex) (Y ^ ey)
        (fun _ => True) (fun _ => True) 1 := by
    intro p q hp hq hq1
    obtain ⟨p', rfl⟩ := dvd_of_mul_parity_ne_one hp
    obtain ⟨q', rfl⟩ := dvd_of_mul_parity_ne_one hq
    refine Submodule.subset_span ⟨p', q', trivial, trivial, ?_, by rw [pow_mul, pow_mul]⟩
    rcases Nat.eq_zero_or_pos q' with h | h
    · simp [h] at hq1
    · exact h
  split_ifs with hd
  · have h := isIso_homDistinctMixedMateDot_of_pow_sourceUnits E A κ τ H hx' hy' hu (Sc.t i j) 0
      (N := 0) (Submodule.zero_mem _)
    rwa [mul_zero, pow_zero, add_zero] at h
  · have hdij : D.d i j ≠ 0 := hd
    have hdji : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff i j).mpr h)
    have hpar : ∀ {i j : I}, i ≠ j → D.d i j ≠ 0 →
        (D.dn i j : ZMod 2) * D.parity i ≠ 1 ∧ 1 ≤ D.dn i j := by
      intro i j hij hd
      have h₁ := D.dn_cast hij
      have h₃ := D.d_nonneg hij
      refine ⟨fun h => ?_, by omega⟩
      have hi : D.parity i = 1 := by
        rcases (show D.parity i = 0 ∨ D.parity i = 1 by
          generalize D.parity i = z; fin_cases z <;> simp) with h' | h'
        · rw [h', mul_zero] at h; exact absurd h (by decide)
        · exact h'
      obtain ⟨r, hr⟩ := D.even_d_of_odd hi j
      rw [hi, mul_one, ZMod.natCast_eq_one_iff_odd] at h
      obtain ⟨r', hr'⟩ := h
      omega
    obtain ⟨hpi, -⟩ := hpar hij hdij
    obtain ⟨hpj, hpos⟩ := hpar hij.symm hdji
    obtain ⟨n, hn⟩ := dvd_of_mul_parity_ne_one hpi
    rw [add_assoc, hn]
    refine isIso_homDistinctMixedMateDot_of_pow_sourceUnits E A κ τ H hx' hy' hu (Sc.t i j) n
      (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun p hp => Submodule.sum_mem _ fun q hq => ?_))
    · simpa only [pow_zero, one_mul] using hmono 0 (D.dn j i) (by simp) hpj hpos
    · by_cases hs : Sc.s i j p q = 0
      · rw [hs, zero_smul]; exact Submodule.zero_mem _
      · have hq1 : 1 ≤ q := by
          by_contra h0
          exact hs (hn i j p q hij (Finset.mem_range.mp hp) (Finset.mem_range.mp hq)
            (Or.inr (by omega)))
        exact Submodule.smul_mem _ _ (hmono p q (fun h => hs (Sc.s_eq_zero i j p q h))
          (fun h => hs ((Sc.s_symm i j p q).trans (Sc.s_eq_zero j i q p h))) hq1)

variable (P : ProbeReservoir k B D Sc)

attribute [local irreducible] Finsupp.zipWith Finsupp.single Finsupp.onFinset homContentShift
  contentWeight in
/-- Mixed sideways crossing invertibility from the source-polynomial unit
criterion. The criterion remains an explicit intermediate hypothesis. -/
theorem isIso_sigmaEntry_probe_reservoir_sourceUnits (hn : Sc.NoPure) (hu : ∀ (i j : I), i ≠ j →
      ∀ {a b c d : X} (hT : a + D.α i = b) (hW : c + D.α j = d)
        (κ : ZMod 2) (H : P.T.obj b ⟶ P.W.obj d),
      MixedPostSourceUnits (P.T.E i hT) (P.W.adj j hW) κ H
        (rouquierPower (P.T.dot i hT) (if D.parity i = 1 then 2 else 1))
        (rouquierPower (P.W.dot j hW) (if D.parity j = 1 then 2 else 1)))
    (c : P.CrossCoeff) {i j : I} (hij : i ≠ j) (ν : X) (t : Sector I)
    (q : SPath (wd D ν [dn i, up j]) t
      (nextSector (dn i) false (nextSector (up j) true t)))
    (Z : P.H (nextSector (dn i) false (nextSector (up j) true t))) :
    IsIso (P.sigmaEntry c i j ν
      (SPath.cons _ true t trivial (SPath.cons _ false _ trivial (SPath.nil _))) q Z) := by
  have hR : StepValid (up i) false (nextSector (dn i) false t) := by
    simp [StepValid, nextSector]
  have e₀ : nextSector (up i) false (nextSector (dn i) false t) = t := by
    simp only [nextSector]; ext <;> simp
  let cupPath : SPath (wd D (SKM.wt D ν [up j, dn i]) (SKM.Shape.cup i).cod) t t :=
    SPath.two false false trivial hR e₀
  let p : SPath (wd D ν [up j, dn i]) t (nextSector (dn i) false (nextSector (up j) true t)) :=
    SPath.cons _ true t trivial (SPath.cons _ false _ trivial (SPath.nil _))
  let m₁ : SPath (wd D ν [dn i, up i, up j, dn i]) t
      (nextSector (dn i) false (nextSector (up j) true t)) :=
    ((SPath.nil t).append cupPath).append p
  have hR' : StepValid (up i) false (nextSector (up j) true (nextSector (dn i) false t)) := by
    simp [StepValid, nextSector]
  have e₁ : nextSector (up j) true (nextSector (up i) false (nextSector (dn i) false t)) =
      nextSector (up j) true t := by rw [e₀]
  have e₂ : nextSector (up i) false (nextSector (up j) true (nextSector (dn i) false t)) =
      nextSector (up j) true t := by
    simp only [nextSector]; ext <;> simp
  let pu₂ : SPath (wd D (SKM.wt D ν ((SKM.Shape.cross i j).dom ++ [dn i])) [dn i]) t
      (nextSector (dn i) false t) := SPath.cons _ false t trivial (SPath.nil _)
  let pv₂ : SPath (wd D ν [dn i]) (nextSector (up j) true t)
      (nextSector (dn i) false (nextSector (up j) true t)) :=
    SPath.cons _ false _ trivial (SPath.nil _)
  let crossDom : SPath (wd D (SKM.wt D ν [dn i]) (SKM.Shape.cross i j).dom)
      (nextSector (dn i) false t) (nextSector (up j) true t) := SPath.two false true hR trivial e₁
  let crossCod : SPath (wd D (SKM.wt D ν [dn i]) (SKM.Shape.cross i j).cod)
      (nextSector (dn i) false t) (nextSector (up j) true t) := SPath.two true false trivial hR' e₂
  let m₂ : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).cod.word t
      (nextSector (dn i) false (nextSector (up j) true t)) := (pu₂.append crossCod).append pv₂
  have hm₁ : m₁ = (pu₂.append crossDom).append pv₂ := SPath.eq_of_sides _ _ (by
    simp only [m₁, cupPath, p, pu₂, pv₂, crossDom, SPath.sides_append, SPath.sides_two]; rfl)
  rw [P.sigmaEntry_eq c hij ν _ q m₁ m₂ Z (a := true) (b := false) rfl (by
      simp only [m₁, cupPath, p, SPath.sides_append, SPath.sides_two]; rfl)
    (by simp only [m₂, pu₂, pv₂, crossCod, SPath.sides_append, SPath.sides_two]; rfl)]
  have h₁ : compLayer (P.upwardGens c) (SKM.lay D ν [] (Shape.cup i) [up j, dn i]) p m₁ Z = _ :=
    P.compLayer_eq (P.upwardGens c) (SKM.lay D ν [] (Shape.cup i) [up j, dn i])
      (SPath.nil t) (SPath.nil t) cupPath p Z
  have h₂ : compLayer (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i])
      ((pu₂.append crossDom).append pv₂) m₂ Z = _ :=
    P.compLayer_eq (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i])
      pu₂ crossDom crossCod pv₂ Z
  let t' := nextSector (dn i) false t
  let u := nextSector (dn i) false (nextSector (up j) true t)
  have hR'' : StepValid (up i) false u := by simp [u, StepValid, nextSector]
  have ecap : nextSector (dn i) false (nextSector (up i) false u) = u := by
    simp only [u, nextSector]; ext <;> simp
  let pu₃ : SPath (wd D (SKM.wt D ν ((SKM.Shape.cap i).dom ++ [])) [dn i, up j]) t u :=
    SPath.cons _ false t trivial (SPath.cons _ true t' trivial (SPath.nil _))
  let capPath : SPath (wd D (SKM.wt D ν []) (SKM.Shape.cap i).dom) u u :=
    SPath.two false false hR'' trivial ecap
  have hm₂ : m₂.cast (sigma_cross_cap_word i j ν) = (pu₃.append capPath).append (SPath.nil _) :=
    SPath.eq_of_sides _ _ (by
      simp only [SPath.sides_cast, m₂, pu₂, pv₂, crossCod, pu₃, capPath, SPath.sides_append,
        SPath.sides_two]; rfl)
  have hq : q.cast (sigma_cap_word i j ν) = (pu₃.append (SPath.nil _)).append (SPath.nil _) :=
    SPath.eq_of_sides _ _ (by
      have : Subsingleton (SPath (wd D ν [dn i, up j]) t u) := SPath.subsingleton_dnUp hij _ _ t u
      rw [Subsingleton.elim q (SPath.cons _ false t (by trivial) (SPath.cons _ true t'
        (by trivial) (SPath.nil _)))]
      simp only [SPath.sides_cast, pu₃, SPath.sides_append]; rfl)
  have h₃ := P.compLayer_eq (P.upwardGens c) (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) [])
      pu₃ capPath (SPath.nil _) (SPath.nil _) Z
  conv at h₁ =>
    rhs
    dsimp only [SKM.lay]
    simp only [Generators.image, upwardGens, cupImage]
    rw [P.zeroTwo_two (hZ := eqRec_heq e₀.symm _)]
    simp only [cupEntry]
    unfold postCup
    simp only [pathFunctor_cons, pathFunctor_nil_map, Functor.comp_map, Functor.id_map, dn, up,
      step, homContentPreE_map, Functor.map_comp, Category.assoc]
  conv at h₂ =>
    rhs
    dsimp only [SKM.lay]
    simp only [Generators.image, upwardGens, crossImage, dite_eq_right hij]
    rw [P.twoTwo_two (hZ := eqRec_heq e₂.symm _)]
    simp only [crossNeEntry]
    unfold mixedJ
    simp only [pu₂, pathFunctor_cons, pathFunctor_nil_map, Functor.comp_map, Functor.id_map, dn, up,
      step, homContentPreE_map, Functor.map_comp, Category.assoc]
  conv at h₃ =>
    rhs
    dsimp only [SKM.lay]
    simp only [Generators.image, upwardGens, capImage]
    rw [P.twoZero_two (hZ := eqRec_heq ecap.symm _)]
    simp only [capEntry]
    unfold postCap
    simp only [pu₃, pathFunctor_cons, pathFunctor_nil_map, Functor.comp_map, Functor.id_map, dn, up,
      step, homContentPreE_map, Functor.map_comp, Category.assoc]
  have h₂' := P.compLayer_congr (P.upwardGens c)
    (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]) hm₁ (rfl : m₂ = m₂) Z
  rw [h₂] at h₂'
  have h₃' := P.compLayer_congr (P.upwardGens c) (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) [])
    hm₂ hq Z
  rw [h₃] at h₃'
  refine isIso_comp_layers _ _ h₁ h₂' h₃' ?_
  simp only [Category.assoc]
  refine isIso_postCup_mixedCross_postCap P.T.obj P.W i t.1 u.1 (μ₀ := P.muP t)
    (μ₁ := P.muP u) (P.T.E j (P.muP_preE j t')) (m₀ := P.muM t)
    (m₁ := P.muM (nextSector (true, i) false u)) (n := P.muM u) ?hm (P.muM_postF i t)
    (P.muM_postE i hR'') _ (fun Y => P.mixedQ j i t' hR' Y) ?hiso _ ?hA _ ?hB
    _ _ ?hf2 _ _ ?hf5 _ _ _ _ _ _ _ _ _ _ _ ?hf18 _ _ ?hf21 _ _ _
  case hf2 | hf5 | hf18 | hf21 => eqToHom_witness
  case hm => simp only [muM, u, nextSector, add_tsub_cancel_right]
  case hiso =>
    exact isIso_homDistinctMixedMateDot_param_sourceUnits hn _ _ _ _ _ hij.symm (P.T.dot_mem j _)
      (P.W.dot_mem i _) (hu j i hij.symm _ _ _ _)
  case hA =>
    apply eq_of_heq
    refine (eqRec_heq _ _).trans ((eqRec_heq _ _).trans ?_)
    refine HEq.trans (HEq.rfl : (P.pathFunctor p).obj Z ≍ P.T.E j (P.muP_preE j t') ≫
      (homContentPostF P.T.obj P.W i u.1 (P.muP u) (P.muM_postF i t)).obj Z) ?_
    apply heq_of_eq
    exact congrArg (fun Y => P.T.E j (P.muP_preE j t') ≫
      (homContentPostF P.T.obj P.W i u.1 (P.muP u) (P.muM_postF i t)).obj Y)
      (eq_of_heq ((eqRec_heq _ _).trans (eqRec_heq _ _))).symm
  case hB =>
    apply eq_of_heq
    refine (eqRec_heq _ _).trans ?_
    exact homContentPostF_obj_heq (Z := Z) P.T.obj P.W i u.1 (P.muP u)
      (by simp only [muM, u, nextSector, add_tsub_cancel_right]) rfl
      (P.muM_postF i (nextSector (up j) true t)) _
      ((eqRec_heq _ _).trans (eqRec_heq _ _)).symm

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
