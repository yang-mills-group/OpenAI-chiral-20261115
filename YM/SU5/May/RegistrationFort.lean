import YM.SU5.May.RegistrationClock
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine

open Aria Germ Alliance SelectionAnalysis Set
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "C" => P.room
local notation "Y" => P.run
local notation "L" => P.large
local notation "P₁" => P.par
local notation "V" => P.law
local notation "G" => P.projection
local notation "H" => P.history
local notation "H₁" => P.projection.clipped
local notation "χ" => P.mayChar x j
local notation "I₀" => P.mayHil x j
local notation "J" => P.advocate 3 x j
local notation "X" => P.ColorHil j J
local notation "B" s:max f:max => Selected.bud Y L V s H H₁ j false (C j) χ f
local notation "Ω" => Selected.doorstep Y L V H H₁ j false (C j) χ
local notation "Ωₓ" => P.colorZero j J
/-! CP1 continued: the full real space(time) translations on the selected TWO
**continuity sectors**, real energies, spectrum prices and unique Ground grant
on the same data. Not assuming continuity in X. MayRootX from CP18 agrees with
events in the exact physical Hilbert space picked by `BoostBacking`. -/
local notation "Uₓ" => P.mayIntertwine x j
local notation "U₀" => (Uₓ).toLinearIsometry.toContinuousLinearMap
local notation "T" => timeMesh P.par
local notation "S" => P.seasons j J
local notation "κ" => P.voyageF j J
local notation "κ'" => Selected.turnstile Y L V H H₁ j false (C j) χ
local notation "ℳ" => marks T
local notation "ℓ" => daylight T
local notation "ℙ" => P.maySaunters x j
local notation "J₀" => P.mayFort x j
local notation "πχ" => (ℙ).orthogonalProjectionOnto
local notation "ℤ'" => P.ManyF j J
local notation "𝔽" => P.Viewers j J
local notation "ϑ" => P.enter j J
local notation "Z" => P.mayIntertwineS x j
local notation "R" => Selected.peninsula Y L V H H₁ j false (C j) χ
local notation "δ" => P.physicalEnergy j J
lemma mayRaw (a : List (Trans j)) (v : Trans j → ℳ) (x' : X) :
    Uₓ ((κ).raw a v x') = (κ').raw a v (Uₓ x') := by
  induction a with
  | nil => rfl
  | cons i a h => rw [Alliance.raw_step, ContinuousLinearMap.comp_apply, P.mayPlays, h, Alliance.raw_step, ContinuousLinearMap.comp_apply]
lemma mayAviation (a : Trans j → ℳ) (g : ℤ') :
    Z ((κ).aviation ℓ (look j) (fun i=> (a i:ℝ)) g) =
      (κ').aviation ℓ (look j) (fun i=> (a i:ℝ)) (Z g) := by
  apply Subtype.ext
  change Uₓ ((κ).flight ℓ (look j) _ g.val) = (κ').flight ℓ (look j) (fun i=> (a i:ℝ)) (Z g).val
  rw [Alliance.smooth_notch, Alliance.smooth_notch, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Alliance.grounded _ _ g.property, Alliance.grounded _ _ (Z g).property]
  exact P.mayRaw x j _ a g.val
lemma mayContinental (a : OS.Cross j) (f : ℤ') : Z ((S).U a f) = (R).U a (Z f) := by
  let F(t : Trans j→ℝ):= Z ((κ).aviation ℓ (look j) t f); let Q(t : Trans j→ℝ):= (κ').aviation ℓ (look j) t (Z f)
  suffices F=Q from congrFun this (fun i: Trans j => a.val i.val)
  have vd : DenseRange (fun (u:Trans j→ℳ) (i:Trans j)=> (u i:ℝ)):= DenseRange.piMap (fun _=> (ℓ).denseRange_val)
  refine vd.equalizer ((Z).continuous.comp (Alliance.aviation_cont _ _ _ (fun (u:Trans j→ℝ)=>u)
    (fun i _=> continuous_apply i) f)) (Alliance.aviation_cont _ _ _ (fun u=> u) (fun i _=> continuous_apply i) (Z f)) ?_
  exact funext fun d=> P.mayAviation x j d f
lemma mayEpoch (a : ℝ) (f : ℤ') : Z ((S).edge a f) = (R).edge a (Z f) := by
  apply Subtype.ext
  change Uₓ (ϑ ((S).edge a f)) = ((R).edge a (Z f)).val
  have hu:= P.soleEdge j J a f
  have hz:= Selected.pane_time Y L V H H₁ j false (C j) χ (Z f) a
  exact (congrArg Uₓ hu).trans ((DFunLike.congr_fun (P.mayEdge x j a) (ϑ f)).trans hz.symm)
lemma mayPositiveHeat (t : ℝ≥0) (f : ℤ') : Z ((S).E t f) = (R).E t (Z f) := by
  apply Subtype.ext; exact DFunLike.congr_fun (P.mayClock x j t) (ϑ f)
lemma mayContinues (a : E4) (f : ℤ') : Z ((S).unit.translation a f) = (R).unit.translation a (Z f) := by
  change Z ((S).edge _ ((S).U (OS.Semigroup.SEP j a) f)) = (R).edge _ ((R).U _ (Z f))
  rw [P.mayEpoch, P.mayContinental]
lemma maySpectrum (f : ℤ') : (S).ℚmeasure.diagonal f = (R).ℚmeasure.diagonal (Z f) := by
  apply Measure.ext_of_charFun; funext v; rw [(R).joint,(S).joint,←mayContinues, (Z).inner_map_map]
lemma mayCompassVacuum : Z (P.heaven j J) = Selected.vocation Y L V H H₁ j false (C j) χ := by
  apply Subtype.ext; exact (P.mayVacuum x j).trans (Selected.vocate ..).symm
lemma mayVictory (h : P.lodestarHere j J) : Selected.Victory Y L V H H₁ false j (C j) χ := by
  let A := Selected.procession Y L V H H₁ j false (C j) χ
  suffices r : SingleGround (Selected.atCharacter Y L V H H₁ j false (C j) χ)
      (Selected.traveller Y L V H H₁ j false (C j)) from
    ⟨r, single_is_extreme _ _ (Selected.travellers Y L V H H₁ j false (C j)) (Selected.setupState ..) r⟩
  intro q p; change ∃ z:ℂ, z • Ω = q
  let t:= (Uₓ).symm q; have ht: Uₓ t=q:= (Uₓ).apply_symm_apply _
  have r : Selected.RealJoint Y L V H H₁ j false (C j) χ (Uₓ t):=
    ht.symm ▸ (Selected.true_joint Y L V H H₁ j false (C j) χ q).1 p
  have h₁:= P.selected_physical j J h
  have hg:t∈Submodule.span ℂ {Ωₓ}:= by
    rw [←h₁.2, P.actual_color]
    constructor
    · intro i; apply (Uₓ).injective; exact (DFunLike.congr_fun (P.mayEdge x j i) t).trans (r.1 i)
    rintro ⟨s,i,v⟩; rw [←P.meets]; apply (Uₓ).injective; exact (P.mayPlays x j v _ t).trans (r.2 v _)
  obtain ⟨z,e⟩:= Submodule.mem_span_singleton.mp hg
  exact ⟨z,(congrArg (fun w:I₀=> z • w) (P.mayVacuum x j).symm).trans
    ((map_smul Uₓ z _).symm.trans ((congrArg Uₓ e).trans ht))⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
