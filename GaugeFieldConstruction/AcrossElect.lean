import YM.SU5.MacroSix.TuneSelector
import GaugeFieldConstruction.AcrossCalendar
import YM.SU5.FiniteGaugeData.Tapestry.Concatenation
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4100
set_option synthInstance.maxSize 28000
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
open TopologicalSpace
namespace Spine
variable {P : Spine} {s i k : ℕ}
open AcrossLands
open Py.Rate.AcrossShots VolumeRate
variable (P) (v:ℕ→ℝ)
local notation "Γ" => P.par
local notation "Y" => P.run
local notation "D" => P.tapeDepth
local notation "C" => P.tapeᵢ
local notation "K" => P.tapeₖ
local notation "B" => P.large
open AcrossLands Tapestry Preparation AcrossShots
variable {n:ℕ}
-- uniform quote margin buys transfer through the entire limit, all fixed-resolution
-- effect observables together, including election via any post-Register Poll.
section
variable (R:P.Register){ε:ℕ→ℝ}
variable (E:IntervalsSchedule P n v ε)
include E
open Tapestry.Fashion

-- General elected price by local shots of *mixed heights*. Not paying support boxes on this lemma (next layer: Pinligatures)
variable {j:Axis}{c:P.Poll j}{x:P.Spectrum0 j}
variable (Pξ:P.Selects R j x c)
include Pξ
local notation "pH" => P.pollTicket j c
local notation "xH" => P.spirits R j x
local notation "P_" i:max k:max => P.shoulderTape n ε v i k
abbrev ratioCostSt (n i k:ℕ)(A:P.Effect) := P.torqueBare v (A*P.pollTicket j c n) i k/ P.torqueBare v (P.pollTicket j c n) i k
-- inner tendsto in ratios; denominator >1/2 eventually after removing real tape, *for all such cofinal selectors*
lemma on_paths_st (f:P.Effect)(e:f∈shorter P.Test s): Tendsto (fun n=>P.RatioOn R j c n f) atTop (𝓝 (P.spirits R j x f)) ∧
   ∀ᶠ a:ℕ in atTop, s ≤ (c a).t ∧ ∀ I K':ℕ→ℕ, Tendsto I atTop atTop→ Tendsto K' atTop atTop→ (∀ᶠ r:ℕ in atTop,P_ (I r) (K' r)) →
   (∀ s A,A∈shorter P.Test s→ Tendsto (fun t=>P.torqueBare v A (I t) (K' t)) atTop (𝓝 (vistaTake Y B (P.talks R) A))) →
   (∀ᶠ t:ℕ in atTop,1/2 < ‖P.torqueBare v (P.pollTicket j c a) (I t) (K' t)‖) ∧ Tendsto (fun t:ℕ=>P.ratioCostSt v (c:=c) a (I t) (K' t) f) atTop (𝓝 (P.RatioOn R j c a f)):=by
 refine ⟨(Pξ.poll f _ e).1,?_⟩
 filter_upwards [Pξ.denominator_tends.norm.eventually (lt_mem_nhds (by norm_num : 1/2<(‖(1:ℂ)‖))),(Pξ.poll f _ e).2] with a h h₁
 refine ⟨h₁.1,?_⟩
 intro I K' i k q F
 have ht:(pH) a∈ shorter P.Test (c a).t:=short_pinhole _ _
 let p:=F _ _ ht; refine ⟨p.norm.eventually (lt_mem_nhds h),?_⟩
 exact (F _ _ ((shorter P.Test (c a).t).mul_mem ((climbs P.Test h₁.1) e) ht)).div p h₁.2.1
structure RightsAllSt (f:P.Effect)(s:ℕ) : Prop where
 converge : Tendsto (fun n=>P.RatioOn R j c n f) atTop (𝓝 (P.spirits R j x f))
 sequential : ∀ᶠ a:ℕ in atTop,s ≤ (c a).t ∧
    ((∀ᶠ i:ℕ in atTop,1/2< ‖P.torqueBare v (P.pollTicket j c a) (P.tapeᵢ (2*i)) (P.tapeₖ (2*i))‖) ∧ Tendsto (fun i:ℕ=> P.ratioCostSt v (c:=c) a (P.tapeᵢ (2*i)) (P.tapeₖ (2*i)) f) atTop (𝓝 (P.RatioOn R j c a f)))∧∀ (u:ℕ→ℕ), (∀ᶠ i:ℕ in atTop,legacy Y (P.period i) (P.circuitDepth (P.period i) (u i))) →
    (∀ᶠ i:ℕ in atTop,1/2< ‖P.torqueBare v (P.pollTicket j c a) (P.period i) (P.circuitDepth (P.period i) (u i))‖) ∧ Tendsto (fun i:ℕ=> P.ratioCostSt v (c:=c) a (P.period i) (P.circuitDepth (P.period i) (u i)) f) atTop (𝓝 (P.RatioOn R j c a f))
lemma allocated (f:P.Effect)(e:f∈ shorter P.Test s): RightsAllSt P v R (c:=c) (x:=x) f s:= by
 obtain ⟨h,hv⟩:=on_paths_st P v R E Pξ f e; refine ⟨h,?_⟩
 have w:Tendsto (fun i:ℕ=> 2*i) atTop atTop:= (show StrictMono (fun i:ℕ=>2*i) from (by intro a b h; exact Nat.mul_lt_mul_of_pos_left h (by norm_num))).tendsto_atTop
 filter_upwards [hv] with i H
 refine ⟨H.1,H.2 (fun i=>C (2*i)) (fun i=>K (2*i)) (P.paidᵢ.tendsto_atTop.comp w) (P.paidₖ.tendsto_atTop.comp w) (P.thinPays v E) (fun s A p=>(P.supportsRead v R E A p).2),?_⟩
 intro u v'; obtain ⟨h,h'⟩:=P.jointPays v E v'; exact H.2 P.period _ (P.law.pick.grow_i.tendsto_atTop) h h' (fun s A p=> ((P.supportsRead v R E A p).1.paths u v'))
-- physical script `Results` later pinligature at P.Front.SC
#print axioms allocated
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
