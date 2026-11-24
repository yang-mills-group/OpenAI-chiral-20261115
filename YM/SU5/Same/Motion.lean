import YM.SU5.Same.Space

/-!
# Same-character identification (CP18 vs CP27), II

Identify the actual heat and spacetime translations. Both including the full Hilbert
spaces and on their continuous sectors. Here we also use the real `edge` in
the Hilbert space, i.e. boosts are *not* granted to do this. We leave the
physical need for the forward cone, Lorentz group covariances etc. clearly in place.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P : Spine) (a : Axis) (x : P.Spectrum0 a) (j : Axis)
local notation "Y" => P.run
local notation "H" => P.large
local notation "V" => P.law
local notation "G" => P.projection
local notation "c" => P.glassAxis a x j
local notation "ξ" => P.advocate a x j
local notation "R" => P.glassSpace a x j
local notation "S" => P.ColorHil j ξ
local notation "L" => P.toGlass a x j
local notation "L₀" => (L).toLinearIsometry.toContinuousLinearMap
local notation "E₁" => P.physicalEnergy j ξ
local notation "A₁" => P.voyageF j ξ
local notation "M" => timeMesh P.par
local notation "D" => marks (timeMesh P.par)

abbrev glassRide : OS.Semigroup (P.glassSpace a x j) j :=
  Selected.ride Y H V P.history P.projection.clipped j false (P.room j) (P.glassAxis a x j)
abbrev glassStile : Alliance (Trans j) (marks (timeMesh P.par)) (P.glassSpace a x j) :=
  Selected.turnstile Y H V P.history P.projection.clipped j false (P.room j) (P.glassAxis a x j)
local notation "E₂" => P.glassRide a x j
local notation "A₂" => P.glassStile a x j

lemma glass_clockBud (s i : ℕ) {f : P.Test} (p : P.birthF j s f) :
    (E₂).E (whenly (timeMesh P.par) s i) (P.glassBud a x j s p) = P.glassBud a x j s (P.passesLater j s i p) := by
  obtain ⟨u,rfl⟩ := p
  refine (Selected.ride_ticks Y H V s P.history P.projection.clipped j false (P.room j) c u.val i).trans ?_
  apply congrArg (Selected.bud Y H V s P.history P.projection.clipped j false (P.room j) c)
  exact Subtype.ext (congrArg (fun a : P.Test => a.val) (P.wishing j s u i).symm)

lemma glassRide_eq (t : ℝ≥0) : (L₀).comp ((E₁).E t) = ((E₂).E t).comp (L₀) := by
  have he (s i : ℕ) {f : P.Test} (p : P.birthF j s f) :
      L (((E₁).E (whenly M s i)) (P.viewF j ξ s p)) =
        (E₂).E (whenly M s i) (L (P.viewF j ξ s p)) := by
    rw [← P.releasedLater j ξ s i p,P.toGlass_view,P.toGlass_view,P.glass_clockBud]
  apply ContinuousLinearMap.ext_on (P.partner_dense j ξ)
  rintro _ ⟨⟨s,f,p⟩,rfl⟩
  let y := P.viewF j ξ s p
  refine congrFun ((fills (M)).denseRange_val.equalizer
    (g:=fun t : ℝ≥0 => L (((E₁).E t) y)) (h:=fun t : ℝ≥0 => (E₂).E t (L y))
    ((L).continuous.comp ((E₁).continuousE _)) ((E₂).continuousE _) ?_) t
  funext v
  change L (((E₁).E v.val) y) = (E₂).E v.val (L y)
  obtain ⟨n,i,u⟩ := MeshClock.split M v.property
  let e := le_max_left s n
  let r := max s n
  change L (((E₁).E v.val) (P.viewF j ξ s p)) = (E₂).E v.val (L (P.viewF j ξ s p))
  rw [←u, ← P.view_rig j ξ s r p e, ← matchR M n r i (le_max_right ..)]
  exact he r _ _

lemma toGlass_heat (t : ℝ≥0) (y : P.ColorHil j ξ) :
    P.toGlass a x j ((E₁).E t y) = (E₂).E t (P.toGlass a x j y) :=
  DFunLike.congr_fun (P.glassRide_eq a x j t) y

/-- Continuation in the full-Hilbert spaces, *still positive heat* only in this equation. -/
lemma toGlass_inside {t : ℂ} (ht : t ∈ OS.Semigroup.inside) (y : P.ColorHil j ξ) :
    P.toGlass a x j ((E₁).F t y) = (E₂).F t (P.toGlass a x j y) :=
  DFunLike.congr_fun (opaque_compare E₁ E₂ L₀ (P.glassRide_eq a x j) ht) y
lemma toGlass_realTime (t : ℝ) (y : P.ColorHil j ξ) :
    P.toGlass a x j ((E₁).edge t y) = (E₂).edge t (P.toGlass a x j y) :=
  DFunLike.congr_fun (within_energy E₁ E₂ L₀ (P.glassRide_eq a x j) t) y

local notation "W₁" i:max => ((A₁).crew i).play
local notation "W₂" i:max => ((A₂).crew i).play

lemma glassStile_eq (k : Trans j) (x' : marks (timeMesh P.par)) :
    (L₀).comp ((W₁ k) x') = ((W₂ k) x').comp L₀ := by
  have he (s : ℕ) (i : ℤ) {f : P.Test} (p : P.birthF j s f) :
      L ((W₁ k) (notch M s i) (P.viewF j ξ s p)) =
        (W₂ k) (notch M s i) (L (P.viewF j ξ s p)) := by
    rw [P.registered,P.toGlass_view,P.toGlass_view]
    exact (Selected.turnstile_in Y H V s P.history P.projection.clipped j false (P.room j) c (P.bornVox j s p) k i).symm
  obtain ⟨n,i,rfl⟩ := notch_exists M x'
  apply ContinuousLinearMap.ext_on (P.partner_dense j ξ)
  rintro _ ⟨⟨s,f,p⟩,rfl⟩
  change L ((W₁ k) (notch M n i) (P.viewF j ξ s p)) = (W₂ k) _ (L (P.viewF j ξ s p))
  let r := max s n
  rw [←P.view_rig j ξ s r p (le_max_left ..), ← notch_up M n r (le_max_right ..)]
  exact he _ _ _

lemma toGlass_play (k : Trans j) (t : marks (timeMesh P.par)) (y : P.ColorHil j ξ) :
    P.toGlass a x j ((W₁ k) t y) = (W₂ k) t (L y) :=
  DFunLike.congr_fun (P.glassStile_eq a x j k t) y

lemma toGlass_raw (p : Trans j → marks (timeMesh P.par)) (l : List (Trans j)) (y : P.ColorHil j ξ) :
    P.toGlass a x j ((A₁).raw l p y) = (A₂).raw l p (L y) := by
  induction l generalizing y with
  | nil => rfl
  | cons i l ih => rw [Alliance.raw_step,Alliance.raw_step,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,P.toGlass_play,ih]

abbrev glassWalkers : Submodule ℂ R := Selected.saunters Y H V P.history P.projection.clipped
  j false (P.room j) (P.glassAxis a x j)
local notation "G₂" => P.glassWalkers a x j
local notation "G₁" => P.Viewers j ξ

lemma toGlass_oneAxisContinuous_iff (i : Trans j) (y : P.ColorHil j ξ) :
    y ∈ ((A₁).crew i).lives S ↔ L y ∈ ((A₂).crew i).lives R := by
  have h : (fun t : marks M => (W₂ i) t (L y)) = L ∘ (fun t => (W₁ i) t y) :=
    funext (fun t => (P.toGlass_play a x j i t y).symm)
  change ContinuousAt (fun t=> (W₁ i) t y) 0 ↔ ContinuousAt (fun t=> (W₂ i) t (L y)) 0
  rw [h]
  exact (L).toHomeomorph.isInducing.continuousAt_iff

lemma toGlass_walkers_iff (y : P.ColorHil j ξ) :
    y ∈ P.Viewers j (P.advocate a x j) ↔ (P.toGlass a x j) y ∈ P.glassWalkers a x j := by
  exact (Alliance.assembled A₁ (look j) y).trans
    ((forall_congr' fun i => forall_congr' (fun _ : i∈look j => P.toGlass_oneAxisContinuous_iff a x j i y)).trans
      (Alliance.assembled A₂ (look j) (L y)).symm)

abbrev glassFort : Hilbert := Selected.fort Y H V P.history P.projection.clipped
  j false (P.room j) (P.glassAxis a x j)
local notation "R'" => P.glassFort a x j
local notation "S'" => P.ManyF j (P.advocate a x j)

/-- Explicit inclusion/projection of the CP27 spatially continuous subspace. -/
abbrev fortIn : R' →ₗᵢ[ℂ] R := (P.glassWalkers a x j).subtypeₗᵢ
abbrev fortProj : R →L[ℂ] R' := (P.glassWalkers a x j).orthogonalProjectionOnto
local notation "ι₁" => P.enter j ξ
local notation "ι₂" => P.fortIn a x j
local notation "π₁" => P.wealth j ξ
local notation "π₂" => P.fortProj a x j

def toFort : S' ≃ₗᵢ[ℂ] R' where
  toFun y := (⟨L (ι₁ y), (P.toGlass_walkers_iff a x j _).1 y.property⟩ : G₂)
  invFun y := (⟨(L).symm (ι₂ y), (P.toGlass_walkers_iff a x j _).2 (by
    rw [LinearIsometryEquiv.apply_symm_apply]; exact y.property)⟩ : G₁)
  left_inv y := Subtype.ext ((L).symm_apply_apply (ι₁ y))
  right_inv y := Subtype.ext ((L).apply_symm_apply (ι₂ y))
  map_add' y z := Subtype.ext (map_add L (ι₁ y) (ι₁ z))
  map_smul' r y := Subtype.ext (map_smul L r (ι₁ y))
  norm_map' y := (L).norm_map (ι₁ y)
local notation "F" => P.toFort a x j

lemma toFort_enter (x' : S') : P.toGlass a x j (ι₁ x') = ι₂ ((P.toFort a x j) x') := rfl
lemma toFort_exit (x' : R') : (P.toGlass a x j).symm (ι₂ x') = ι₁ ((P.toFort a x j).symm x') := rfl
lemma wealth_inner (x' : S) (y : S') : inner ℂ y ((P.wealth j ξ) x') = inner ℂ (ι₁ y) x' := by
  have h : (π₁ x' : G₁) = (G₁).orthogonalProjectionOnto x' := Subtype.ext
    (DFunLike.congr_fun (P.visitors_op j ξ) x')
  exact (congrArg (inner ℂ y) h).trans (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K:=G₁) y x')
lemma fort_inner (x' : R) (y : R') : inner ℂ y (π₂ x') = inner ℂ (ι₂ y) x' :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K:=G₂) y x'

lemma toFort_wealth (y : P.ColorHil j ξ) : F (π₁ y) = π₂ (L y) := by
  apply ext_inner_left ℂ
  intro z
  obtain ⟨z,rfl⟩ := (F).surjective z
  rw [LinearIsometryEquiv.inner_map_map,P.fort_inner,P.wealth_inner,←P.toFort_enter, LinearIsometryEquiv.inner_map_map]

abbrev glassSeason : OS.Semigroup (P.glassFort a x j) j := Selected.peninsula Y H V
  P.history P.projection.clipped j false (P.room j) (P.glassAxis a x j)
local notation "T₁" => P.seasons j ξ
local notation "T₂" => P.glassSeason a x j

lemma toFort_heat (t : ℝ≥0) (y : S') : F ((T₁).E t y) = (T₂).E t (F y) :=
  Subtype.ext (P.toGlass_heat a x j t (ι₁ y))
lemma toFort_inside {t : ℂ} (ht : t ∈ OS.Semigroup.inside) (y : S') : F ((T₁).F t y) = (T₂).F t (F y) :=
  DFunLike.congr_fun (opaque_compare T₁ T₂ (F).toLinearIsometry.toContinuousLinearMap (fun t=>
    ContinuousLinearMap.ext (fun y=> P.toFort_heat a x j t y)) ht) y
lemma toFort_edge (t : ℝ) (y : S') : F ((T₁).edge t y) = (T₂).edge t (F y) :=
  DFunLike.congr_fun (within_energy T₁ T₂ (F).toLinearIsometry.toContinuousLinearMap (fun t=>
    ContinuousLinearMap.ext (fun y=> P.toFort_heat a x j t y)) t) y
abbrev glassHeaven : P.glassFort a x j := Selected.vocation Y H V P.history P.projection.clipped
  j false (P.room j) (P.glassAxis a x j)
lemma fortHeaven_in : ι₂ (P.glassHeaven a x j) = P.glassVac a x j :=
  Selected.vocate Y H V P.history P.projection.clipped j false (P.room j) (P.glassAxis a x j)
lemma toFort_heaven : F (P.heaven j ξ) = P.glassHeaven a x j :=
  (ι₂).injective ((P.toGlass_vacuum a x j).trans (P.fortHeaven_in a x j).symm)

lemma toFort_realSpace (t : OS.Cross j) (y : S') :
    F ((T₁).U t y) = (T₂).U t (F y) := by
  let q : (Trans j→D) → Trans j → ℝ := fun f i=> (f i:ℝ)
  have h : DenseRange q := DenseRange.piMap fun i:Trans j=> (daylight M).denseRange_val
  refine congrFun (h.equalizer
    (g:=fun t : Trans j → ℝ => F ((A₁).aviation (daylight M) (look j) t y))
    (h:=fun t : Trans j → ℝ => (A₂).aviation (daylight M) (look j) t (F y))
    ((F).continuous.comp ((A₁).aviation_cont (daylight M) (look j) _ (fun i _=> continuous_apply i) y))
    ((A₂).aviation_cont (daylight M) (look j) _ (fun i _=> continuous_apply i) (F y)) ?_) (fun i : Trans j => t.val i.val)
  funext r
  apply (ι₂).injective
  change L ((A₁).flight (daylight M) (look j) (q r) (ι₁ y)) =
    (A₂).flight (daylight M) (look j) (q r) (ι₂ (F y))
  rw [(A₁).smooth_notch (daylight M) (look j) r,(A₂).smooth_notch (daylight M) (look j) r,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,(A₁).grounded _ (show ι₁ y∈ G₁ from y.property),
        (A₂).grounded _ (show ι₂ (F y) ∈ G₂ from (F y).property),P.toGlass_raw,←P.toFort_enter]

lemma toFort_translation (t : E4) (y : S') :
    F ((T₁).unit.translation t y) = (T₂).unit.translation t (F y) := by
  change F ((T₁).edge (t j) ((T₁).U _ y)) = (T₂).edge (t j) ((T₂).U _ (F y))
  rw [P.toFort_edge,P.toFort_realSpace]

open Spectral Measure Analysis Boundary Probe
lemma toFort_spectrum (v : S') :
    (T₂).ℚmeasure.diagonal (F v) = (T₁).ℚmeasure.diagonal v := by
  apply Measure.ext_of_charFun
  funext t
  rw [(T₂).joint,(T₁).joint,← P.toFort_translation,LinearIsometryEquiv.inner_map_map]

lemma glassForward_iff : ConePrice.Forward T₂ ↔ ConePrice.Forward T₁ := by
  constructor
  · intro e
    ext1 v
    apply ((T₁).ℚmeasure.null_pair (ConePrice.closed_front _).isOpen_compl.measurableSet v).mp
    rw [←P.toFort_spectrum]
    exact ((T₂).ℚmeasure.null_pair (ConePrice.closed_front _).isOpen_compl.measurableSet _).mpr (by rw [e]; rfl)
  intro e
  ext1 v
  apply ((T₂).ℚmeasure.null_pair (ConePrice.closed_front _).isOpen_compl.measurableSet v).mp
  obtain ⟨v,rfl⟩ := (F).surjective v
  rw [P.toFort_spectrum]
  exact ((T₁).ℚmeasure.null_pair (ConePrice.closed_front _).isOpen_compl.measurableSet _).mpr (by rw [e]; rfl)

lemma glassPresent_iff : G₂ = ⊤ ↔ G₁ = ⊤ := by
  rw [eq_top_iff,eq_top_iff]
  constructor
  · exact fun h y _ => (P.toGlass_walkers_iff a x j y).mpr (h (Submodule.mem_top))
  intro h y _
  obtain ⟨z,rfl⟩ := (L).surjective y
  exact (P.toGlass_walkers_iff a x j z).mp (h (Submodule.mem_top))

#print axioms toFort_spectrum
#print axioms toFort_wealth
#print axioms toGlass_play
#print axioms glassPresent_iff
#print axioms glassForward_iff
#print axioms toFort_heaven
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
