import YM.SatinExist.FoyerAction
import YM.SU5.Reconstruction.Trap.Castle
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup
open MacroGrid Set
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "Y" => P.run
local notation "H" => P.large
local notation "Λ" => P.par
local notation "V" => P.law
local notation "G" => P.history
local notation "Gt" => P.projection.clipped
local notation "W" => timeMesh P.par
local notation "C" => P.room
local notation "ξ" => P.advocate 3 x j
local notation "ζ" => P.glasshouseCharacter 3 x
local notation "χ" => P.orientHouse x j
local notation "Hi" => P.GreatRoom x j
local notation "Hz" => P.PortionHil j ξ
local notation "Hc" => P.ColorHil j ξ
local notation "Bc" => P.stateVox j ξ
local notation "Bg" => P.greatBud x j
local notation "α" => P.foyer x j
local notation "β" => P.colorRoom x j
local notation "α'" => (α).toLinearIsometry.toContinuousLinearMap
local notation "Tg" => Selected.turnstile Y H V G Gt j false (C j) χ
local notation "R″" => Selected.ride Y H V G Gt j false (C j) χ
open YM.SelectionAnalysis
local notation "Tc" => P.voyageF j ξ
local notation "K" => P.Viewers j ξ
local notation "L" => Selected.saunters Y H V G Gt j false (C j) χ
local notation "Z₀" => Selected.fort Y H V G Gt j false (C j) χ
local notation "Z" => P.ManyF j ξ

private lemma rearrange {X D:Hilbert}(αe:X≃ₗᵢ[ℂ]D){Ye:Type*}[TopologicalSpace Ye](p:Ye)(f:Ye→X)(g:Ye→D)
    (u:∀ y, αe (f y)=g y) : ContinuousAt f p ↔ ContinuousAt g p := by
  rw [show g= αe ∘ f from (funext u).symm]
  refine ⟨fun h=> αe.continuous.continuousAt.comp h, fun h=>?_⟩
  have e : f= αe.symm ∘ (αe ∘ f) := by ext x; simp
  conv => arg 1; rw [e]
  exact αe.symm.continuous.continuousAt.comp h
lemma colorRoom_lives (z:Hc) : z∈ K ↔ β z ∈ L := by
  change z∈ (Tc).aviator (look j) ↔ β z∈ (Tg).aviator (look j)
  rw [Alliance.assembled,Alliance.assembled]
  refine forall₂_congr fun i e=> ?_
  exact rearrange (X:=Hc) (D:=Hi) (β) (0:marks W) _ _ (P.color_grid x j i · z)

noncomputable def partColorRoom : P.ManyF j (P.advocate 3 x j) →ₗᵢ[ℂ] Selected.fort
    P.run P.large P.law P.history P.projection.clipped j false (P.room j) (P.orientHouse x j) where
  toFun i := (⟨(β i.val), (P.colorRoom_lives ..).1 i.property⟩ : L)
  map_add' a b := Subtype.ext ((β).map_add a.val b.val)
  map_smul' c a := Subtype.ext ((β).map_smul c a.val)
  norm_map' a := (β).norm_map a.val
lemma partColorRoom_onto : Function.Surjective (P.partColorRoom x j) := by
  intro i; let q := (β).symm i.val; have e : β q = i.val := (β).apply_symm_apply _
  exact ⟨(⟨q,(P.colorRoom_lives ..).2 (e.symm ▸ i.property)⟩ : K), Subtype.ext e⟩
noncomputable def onGlass := LinearIsometryEquiv.ofSurjective (P.partColorRoom x j) (P.partColorRoom_onto x j)
local notation "δ" => P.onGlass x j
local notation "Ω" => P.heaven j ξ
local notation "Ωg" => Selected.vocation Y H V G Gt j false (C j) χ

lemma onGlass_at (f:Z) : ((δ f:L).val) = β (P.enter j ξ f) := rfl
lemma onGlass_vac : δ Ω = Ωg :=
  Subtype.ext ((P.colorRoom_vacuum x j).trans (Selected.vocate ..).symm)
lemma onGlass_part (i:Hc) : δ (P.wealth j ξ i)=(L).orthogonalProjectionOnto (β i) := by
  let pr:= (L).orthogonalProjectionOnto
  have hP : P.wealth j ξ i=(K).orthogonalProjectionOnto i:= by
    apply Subtype.ext
    exact DFunLike.congr_fun (P.visitors_op j ξ) i
  apply ext_inner_left ℂ
  intro z
  obtain ⟨t,rfl⟩ := (δ).surjective z
  rw [hP,(δ).inner_map_map]
  change inner ℂ (t : K) _ = inner ℂ ((δ t) : L) _
  exact ((K).inner_orthogonalProjectionOnto_eq_of_mem_left t _).trans
    (((β).inner_map_map t.val i).symm.trans ((L).inner_orthogonalProjectionOnto_eq_of_mem_left (δ t) _).symm)

local notation "Sg" => Selected.peninsula Y H V G Gt j false (C j) χ
local notation "Sc" => P.seasons j ξ
lemma onGlass_wait (t:ℝ≥0)(z:Z) : δ ((Sc).E t z)=(Sg).E t (δ z) :=
  Subtype.ext (P.color_wait x j t _)
lemma onGlass_time (t:ℝ)(z:Z) : δ ((Sc).edge t z)=(Sg).edge t (δ z) :=
  DFunLike.congr_fun (within_energy Sc Sg (δ).toLinearIsometry.toContinuousLinearMap
    (fun r => ContinuousLinearMap.ext fun i=> P.onGlass_wait x j r i) t) z

lemma onGlass_fly (x':Trans j→ℝ)(v:Z) :
    β ((Tc).flight (daylight W) (look j) x' v.val)=(Tg).flight (daylight W) (look j) x' ((δ v:L).val) := by
  let z:= (δ v:L)
  let X : marks W →ℝ := ((↑) : (marks W)→ ℝ)
  let f (a:Trans j→ℝ): Hi:= β ((Tc).flight (daylight W) (look j) a v.val)
  let g (a:Trans j→ℝ): Hi:= (Tg).flight (daylight W) (look j) a z.val
  let w(a:Trans j→marks W): Trans j→ℝ:= X ∘ a
  have he: DenseRange w:= DenseRange.piMap fun i:Trans j=> (daylight W).denseRange_val
  suffices p:f=g from congrFun p x'
  apply he.equalizer ((β).continuous.comp (Alliance.moves (Tc) (daylight W) (look j) _ (fun i _=> continuous_apply (A:=fun _=>ℝ) i) (fun _=>v.val) continuous_const))
    (Alliance.moves (Tg) (daylight W) (look j) _ (fun i _=> continuous_apply (A:=fun _=>ℝ) i) (fun _=>z.val) continuous_const)
  funext y
  change β ((Tc).flight (daylight W) (look j) (fun i=>(y i:ℝ)) v.val)=
    (Tg).flight (daylight W) (look j) (fun i=>(y i:ℝ)) z.val
  rw [Alliance.smooth_notch,Alliance.smooth_notch,ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Alliance.grounded (Tc) _ v.property,Alliance.grounded (Tg) _ z.property]
  suffices ht : ∀ k : List (Trans j), β ((Tc).raw k y v.val)=(Tg).raw k y z.val from ht _
  intro k; induction k with
  | nil=> rfl
  | cons i k t => rw [Alliance.raw_step,Alliance.raw_step,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,P.color_grid,t]
lemma onGlass_move (u:OS.Cross j)(z:Z) : δ ((Sc).U u z)=(Sg).U u (δ z) := by
  apply Subtype.ext
  exact P.onGlass_fly x j (fun i=>u.val i.val) z

local notation "τg" => (Sg).unit.translation
local notation "τc" => (Sc).unit.translation
local notation "νg" => (Sg).ℚmeasure
local notation "νc" => (Sc).ℚmeasure
lemma onGlass_translation (s:E4)(z:Z) : δ (τc s z)= τg s (δ z) :=
  (P.onGlass_time x j (s j) ((Sc).U (OS.Semigroup.SEP j s) z)).trans
    (congrArg ((Sg).edge (s j)) (P.onGlass_move x j _ z))
lemma onGlass_spectrum (z:Z) : (νg).diagonal (δ z) = (νc).diagonal z := by
  apply Measure.ext_of_charFun
  ext1 b
  rw [(Sg).joint, (Sc).joint,← P.onGlass_translation, (δ).inner_map_map]

lemma onGlass_regions (s:Set E4)(h:MeasurableSet s)(z:Z) : δ ((νc).region s z)=(νg).region s (δ z) := by
  let Q:= (νg).region s; let D:= (νc).region s; let A:= (δ).toLinearIsometry.toContinuousLinearMap
  let U : (Z).Op:= (δ).symm.toLinearIsometry.toContinuousLinearMap.comp (Q.comp A)
  have hu (x:Z) : U x=(δ).symm (Q (δ x)) := rfl
  have he (x:Z) : inner ℂ x (U x) = inner ℂ x (D x) := by
    rw [← (δ).inner_map_map, hu, (δ).apply_symm_apply]
    unfold Q D
    rw [← (νc).at_pair h, ← (νg).at_pair h,P.onGlass_spectrum]
  have ht : U.toLinearMap=D.toLinearMap := by
    apply (ext_inner_map _ _).1
    intro u; apply (starRingEnd ℂ).injective
    rw [inner_conj_symm, inner_conj_symm]
    exact he u
  apply (δ).symm.injective
  exact ((δ).symm_apply_apply _).trans (LinearMap.congr_fun ht.symm z)

open ConePrice
lemma onGlass_forward_iff : Forward (P.seasons j ξ) ↔ Forward (Sg) := by
  let C₀:= (front j)ᶜ
  let R := P.onGlass_regions x j C₀ (closed_front j|>.measurableSet.compl)
  change (νc).region _=0 ↔ (νg).region _=0
  constructor <;> intro p <;> ext1 z
  · obtain ⟨t,rfl⟩:= (δ).surjective z
    rw [← R,(show (νc).region C₀=0 from p),ContinuousLinearMap.zero_apply,map_zero]; rfl
  rw [show (νg).region C₀=0 from p] at R
  apply (δ).injective
  exact (R z).trans (map_zero _).symm
lemma onGlass_present : (P.Viewers j ξ)=⊤ ↔ L=⊤ := by
  constructor <;> intro p
  · apply top_unique; intro z _
    obtain ⟨i,rfl⟩:= (β).surjective z
    apply (P.colorRoom_lives x j i).1
    rw [p]; exact Submodule.mem_top
  apply top_unique; intro z _
  apply (P.colorRoom_lives x j z).2
  rw [p]; exact Submodule.mem_top

-- CP27 does not natively provide full Poincare group relations. But present and cone are the inputs needed.
lemma eligible_chamber : FirstWindows.LightBudget.BoostBacking Y H V P.projection C 3 ζ ↔
    ∀ j:Axis,P.Viewers j (P.advocate 3 x j)=⊤ ∧ Forward (P.seasons j (P.advocate 3 x j)) := by
  constructor
  · exact fun h j=> ⟨(P.onGlass_present x j).2 (h.present j),(P.onGlass_forward_iff x j).2 (h.forward j)⟩
  intro p
  apply (FirstWindows.LightBudget.real_boost_purchase Y H V P.projection C 3 ζ (r:=0) le_rfl (e:=1) zero_lt_one).1
  constructor
  intro j
  apply FirstWindows.LightBudget.twoShotPays
  apply (FirstWindows.LightBudget.true_spectrum Y H V P.projection j (C j) _ le_rfl zero_lt_one).2
  exact ⟨(P.onGlass_present x j).1 (p j).1,(P.onGlass_forward_iff x j).1 (p j).2⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
