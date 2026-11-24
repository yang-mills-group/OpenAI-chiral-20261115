import YM.SU5.Selected.Lodestar
import YM.SU5.Selected.Overview
import YM.SU5.Reconstruct.Regions

/-!
# Pe-pay & selection dictionary (from the supplied library)

* `enrolledCost`: finite resolution price (on the ACTUAL theory, mark even,
  arbitrary finite stencil including both Panes).
* `account_pe`, `pe_takes`, `elected_chart`: physical normalization, unit
  partition and limit prescriptions at all the fixed inputs and the terminal coupling
  on every actual tape. In particular `pe_takes` reads by measurement also at
  the top cutoff, using `atCutoff` from the polynomial apparatus on this same
  course, with EXACTLY the same price. At that top the numerator and denominator
  can be evaluated with just a single U field and the common chiral amplitude
  using all families. At the observing height, already there's a single `city`
  draw—one U and auxiliary, the second Pane *at that draw determined by the history*
  (`drawn` definitionally `(z.1,CapeT s z)`). `Exhibition.taking_formula`
  or `Tapestry.funds` for other inquiries.
* `x` in the main theorems uses the spine compression ensemble from these data and
  `P.Spectrum0 3`. See also `axis_prescription`. Don't confuse
  selecting x with ascribing a component-limit meaning to `sharp` of a fixed Family:
  that limit above is UNELECTED in component sense. Below `account_mean`
  identifies it with the ensemble mean. We use `P.singleState` on all labels, not
  that mean. In another file we also formalize extracting these component
  prices by taking *ratios* of actual readings with vacuum-selection insertions.

This file is just bookkeeping off the verified conductors (`P.law` and
`P.history` + `P.talks`), particularly `Progress` CP1--3 uses EXACTLY those for
its one x. No other sector of the system / no transportation of a history here.
`Gauge` and `compass` names overloaded in package, namespace `Journey`
for this account. Physical `locations` in fermion units.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3600
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Tapestry.Altitude Tapestry.Exhibition
namespace Spine
variable (P : Spine) (R : P.Register) (s t k i j : ℕ) (f : P.Test)
local notation "Y" => P.run
local notation "Λ" => P.par
local notation "H" => P.large
local notation "K" => P.calibration
local notation "κ₁" => P.period
local notation "κ₂" => P.cutoff
local notation "L" => P.law
local notation "A" => P.history
local notation "D" => P.talks R
-- t here an arbitrary period enumeration index, k depth index, s observation level
local notation "r" => P.run.uv k
local notation "W" a:max => (P.run.voyage a).CapeT
local notation "N" a:max b:max => side P.run a b
local notation "X" => (P.run.voyage t).X r
local notation "Γ" a:max => (X).gram a
local notation "κ" a:max => partitionZ ((X).gram a) P.par.U ((W t) a)

def enrolledCost (t k s : ℕ) (f : P.Test) : ℂ := sharp P.run P.large s t k f.val

include R
lemma coupling_confirmed : (Γ 0).beta=P.par.x ∧ Real.exp 1≤P.par.x := (P.certified_register R).pivot t k
omit R

structure PaidPe : Prop where
  paid : Tapestry.Pay P.run s t k
  valid : partitionZ ((X).gram s) P.par.U ((W t) s)≠0
  balance : partitionZ ((X).gram s) P.par.U ((W t) s)=partitionZ ((X).gram r) P.par.U ((W t) r)
  unit_ : P.enrolledCost t k s 1=1
  denominator : partitionZ ((X).gram s) P.par.U ((W t) s)=
    ∫ z, inner ℂ (Dial.mateK (N t s))
      (acts ((1:Mark (N t s)) (drawn ((W t) s) z)) (denZ (Γ s) P.par.U ((W t) s) z)) ∂city (N t s)
  contract (x : P.Test) :
    let I₀ := fun z : Orbit (N t s) ↦ inner ℂ (Dial.mateK (N t s))
      (acts (exhibit Y H s t x.val (drawn ((W t) s) z)) (denZ (Γ s) P.par.U ((W t) s) z))
    Integrable I₀ (city (N t s)) ∧ P.enrolledCost t k s x=(∫ z, I₀ z ∂city (N t s))/κ s

lemma exhibit_pe (f : P.Test) (h : Pay P.run s t k) :
    let I₀ := fun z : Orbit (N t s) ↦ inner ℂ (Dial.mateK (N t s))
      (acts (exhibit Y H s t f.val (drawn ((W t) s) z)) (denZ (Γ s) P.par.U ((W t) s) z))
    Integrable I₀ (city (N t s)) ∧ P.enrolledCost t k s f=(∫ z, I₀ z ∂city (N t s))/κ s := by
  intro I₀
  obtain ⟨S,v⟩ := (show TestFamily (P.calibration) true f.val from f.property).paid
  obtain ⟨q,u,w⟩ := Tapestry.funds Y _ _ _ (exhibited Y H _ _ _ v).env h.1 h.2
  exact ⟨q,(actualRead Y H s t k f.val).trans w⟩

-- unit price even on tori where support not Roomy
variable {s t k} in
lemma account_pe (h : Pay P.run s t k) : P.PaidPe s t k := by
  refine ⟨h,(P.run.each_level t k s h.1 h.2).valid,((X).balance s h.2),
    (actualRead Y H s t k 1).trans (by rw [actual_one]; exact oneReader _ _ _ _ h),?_,fun x ↦ P.exhibit_pe s t k x h⟩
  exact (markvac ((W t) s) (denZ (Γ s) P.par.U ((W t) s))).symm

open Reconstruction
lemma pe_takes (h : Pay P.run s t k) :
    let ν:= prior SU.group (More (side P.run t (P.run.uv k)))
    let A₁:= atCutoff P.run P.large t k (pinhole P.Test s f)
    Integrable (bareAmplitude P.run t k A₁) ν ∧ Integrable (bareAmplitude P.run t k 1) ν ∧
    (∫ x, bareAmplitude P.run t k 1 x ∂ν) ≠ 0 ∧
    P.enrolledCost t k s f = (∫ U : Pane (N t r), bareAmplitude Y t k A₁ U ∂ν)/(∫ U, bareAmplitude Y t k 1 U ∂ν) := by
  intro v A₁
  obtain ⟨p,q,g⟩:= identifyRevenue Y H t k s (short_pinhole s f) h
  exact ⟨p,(partitionIncome Y t k h.1).1, q,(recordedAt (u:=f) Y H s t k h).symm.trans g⟩

local notation "Ω" => followStage
local notation "μ" x:max => κ₁ (WedgeStage.vol x)
local notation "η" x:max => κ₂ (WedgeStage.uv x)
include R
lemma pe_cone : (∀ᶠ n in followStage, P.PaidPe s (μ n) (η n)) ∧
    Tendsto (fun n ↦ P.enrolledCost (μ n) (η n) s f) followStage (𝓝 (P.E s f.val)) := by
  have he := (D).payStage Y H s
  obtain ⟨S,v⟩ := findsBay P.calibration f
  obtain ⟨x,rfl⟩ := accolade P.calibration S f v
  refine ⟨he.mono (fun _ ↦ P.account_pe),?_⟩
  have hv := cn_apply («X»:=Swatch S) («Y»:=ℂ) ((D).coneReader Y H S s) (tendsto_const_nhds (x:=x))
  exact hv.congr' (he.mono fun n h ↦ (tapReader_sharp Y H S s _ _ x h))

lemma pe_polys (u : P.Effect) (p : u ∈ FiniteGaugeDataPoly P.calibration) :
    Tendsto (fun n ↦ taking P.run P.large (μ n) (η n) u) followStage
        (𝓝 (vistaTake Y H (P.talks R) u)) := by
  obtain ⟨n,h⟩ := curve.mp p
  obtain ⟨S,v⟩ := anyWords _ n u h
  obtain ⟨U,k⟩ := Tapestry.issued.mp v
  exact (Fashion.livePocket Y H R.exhibition S n k).2

/-- Include conditioning of selected general even local marks (including this field),
not only narrower. Actual consulting path `G.history`. -/
structure ElectedChart : Prop where
  pre (t : ℕ) : ∀ᶠ k in atTop, P.PaidPe s t (P.cutoff k)
  election : Couplet P.period P.cutoff (fun t k ↦ P.enrolledCost t k s f) (P.ultraviolet s f.val)
    (P.E s f.val) (fun p ↦ ∀ᶠ b in atTop, legacy P.run (P.period b) (P.cutoff (p b)))
  cone : (∀ᶠ n in followStage, P.PaidPe s (μ n) (η n)) ∧
    (∀ n : WedgeStage, legacy P.run (μ n) (η n)) ∧
    Tendsto (fun n ↦ P.enrolledCost (μ n) (η n) s f) followStage (𝓝 (P.E s f.val))
  path : (∀ᶠ n:ℕ in atTop, Ferry Y s (κ₁ (P.projection.rows n)) (κ₂ (P.projection.columns n))) ∧
    Tendsto (fun n ↦ taking Y H (κ₁ (P.projection.rows n)) (κ₂ (P.projection.columns n)) (P.slotHole s f))
      atTop (𝓝 (P.E s f.val)) ∧
    Tendsto (fun n ↦ P.enrolledCost (κ₁ (P.projection.rows n)) (κ₂ (P.projection.columns n)) s f)
      atTop (𝓝 (P.E s f.val))
  operator (S : Finset Cover) : Tendsto (fun n:ℕ ↦ coupon Y H S s
    (κ₁ (P.projection.rows n)) (κ₂ (P.projection.columns n))) atTop (𝓝 (R.loom S s))
  transfer : P.projection.refine s f.val = (P.promote s R f).val

lemma elected_chart : P.ElectedChart R s f := by
  have h:= P.pe_cone R s f
  have f':= P.all_heights_here R
  have t:= (h.2).comp f'
  refine ⟨fun t ↦ ((P.talks R).sharper Y H s t).mono (fun _ ↦ P.account_pe),
    P.law.together s f.val f.property,⟨h.1,fun n ↦ ((D).status ..).2 n.inside,h.2⟩,
      ⟨P.history.finance s,t.congr' ?_,t⟩,fun S ↦ P.limit_witness _ S R,P.identical_transfer s R f⟩
  filter_upwards [f'.eventually h.1] with i v -- `eventually` signature
  exact (recordedAt (u:=f) Y H s _ _ v.paid).symm

omit R
variable (x : P.Spectrum0 3) (a : Axis)

-- No cross-plane economy loss even for ensemble pricing. Intertwiner of
-- the compression algebra representations of the common **unselected ground**,
-- then the Advocate on that data. (not identifying positive-side Hilberts
-- across changing OS directions; we only ask the matching readings.)
local notation "b✓" => P.otherSpectrum 3 a x
open OS.Ground
lemma same_spectrum (x : P.Spectrum0 a) : P.otherSpectrum a a x=x := by
  have hv : ∀ z : P.vacuum a, P.planeChoice a a z=z := by
    intro z
    let E := (P.planeChoice a a).toLinearIsometry.toContinuousLinearMap
    have ht : E=ContinuousLinearMap.id ℂ _ := P.extGroundOperator a E _ (fun k ↦ P.flips_spaces a a k)
    exact DFunLike.congr_fun ht _
  have hu (p : P.Ensemble a) : P.migrateHom a a p=p := by
    apply Subtype.ext; rw [P.migrant]
    apply P.extGroundOperator a
    intro b
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,hv]
    apply congrArg; nth_rw 1 [←hv ((P.labelled a b) (P.groundZero a))]; rw [LinearIsometryEquiv.symm_apply_apply]
  refine (OS.Ground.bij («X»:=P.Ensemble a)).injective ?_
  ext1 z; exact (P.translates a a x z).trans (congrArg _ (hu z))

include R in
lemma axis_prescription : P.singleState 3 s x f = P.chi 3 x (P.reading 3 s f) ∧
    (P.planeChoice 3 a).conjStarAlgEquiv (P.reading 3 s f).val = (P.reading a s f).val ∧
    P.singleState a s (b✓) f = P.singleState 3 s x f ∧
    P.singleState 3 s x (P.reflectTest a f) = star (P.singleState 3 s x f) ∧
    P.spirits R 3 x (P.slotHole s f) = P.singleState 3 s x f := by
  have he : P.singleState a s (b✓) (P.reflectTest a f)=star (P.singleState a s (b✓) f) := by
    rw [P.single_state,P.single_state,← P.reading_star,map_star]
  exact ⟨rfl,P.transports_cap 3 a (s,f),P.single_agrees .., by rwa [P.single_agrees,P.single_agrees] at he,P.oneCup ..⟩

lemma account_mean : (∫ x:P.Spectrum0 3,P.singleState 3 s x f ∂P.pillars 3)=P.E s f.val ∧
    (inner ℂ (P.groundZero 3) ((P.compressed 3 s f) (P.groundZero 3))=P.E s f.val) ∧
    IsProbabilityMeasure (P.pillars 3) :=
  ⟨Eq.trans (P.recovery 3 (P.reading 3 s f)) (P.occupied ..),P.occupied ..,P.normalization 3⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
#print axioms coupling_confirmed
#print axioms account_pe
#print axioms pe_takes
#print axioms elected_chart
#print axioms pe_polys
#print axioms same_spectrum
#print axioms axis_prescription
#print axioms account_mean
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
