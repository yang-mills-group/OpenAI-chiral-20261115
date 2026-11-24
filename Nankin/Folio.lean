import Nankin.Auric
import Nankin.Faraday
import Nankin.ProdLim
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
namespace Calico
open Py.Dyad Work.E08 AnalyticBridge.VerifiedReset StressFlux PlaqAxes
open VacuumSelection.Spine Py.Dyad Keeping
variable (P:VacuumSelection.Spine)(u:P.Roster)(M:Py.Rate.Pitching.Focus.Morn P.par.K)(Aα:ℝ)(H:P.Foam u M Aα)
local notation "Y"=> P.run
local notation "π" i:max => P.period (P.projection.rows i)
local notation "ζ" i:max => P.cutoff (P.projection.columns i)
local notation "K"=>P.calibration
variable(F s x:ℕ)(C D:ℕ→ℝ)(a:ℕ→ℕ)
-- price only.B rd i. 
structure Ear (P:VacuumSelection.Spine)(M:Py.Rate.Pitching.Focus.Morn P.par.K)(F s x:ℕ)(C D:ℕ→ℝ):Prop where
 uv:s+1 ≤ P.run.uv (P.cutoff (P.projection.columns x))
 kick:(P.run.voyage (P.period (P.projection.rows x))).kick≤ P.cutoff (P.projection.columns x)
 tag(j d:ℕ)(t:F ≤ j)(l:j ≤ s)(a:Axis)(o:Cover)(b:Bool)(t₀:(P.calibration.ℓ:ℤ)+(amount P j)≤nodeC o a)(t₁:nodeC o a ≤ d)(t₂:2*(d+(amount P j))+addgap P.calibration≤ (Papal.count P.run j (P.period (P.projection.rows x))).val) : ‖Chem P (amount P j) a j s (P.period (P.projection.rows x)) (P.cutoff (P.projection.columns x)) C D d o b kick‖≤wafer P M j (amount P j) d
include H
theorem folle: ∀ᶠ F:ℕ in atTop,∀ s:ℕ,F ≤ s→
 ∃ (c d:ℕ→ℕ→ℝ)(a:ℕ→ℕ)(C D:ℕ→ℝ), StrictMono a ∧ Bills F (s+1) s P.par.R.L C D ∧ (∀ k,F ≤ k→ k<s+1→Tendsto (fun i=>c (a i) k) atTop (𝓝 (C k))) ∧ (∀ k,F ≤ k→ k<s→ Tendsto (fun i=>d (a i) k) atTop (𝓝 (D k))) ∧ ∀ᶠ x in atTop,Ear P M F s x (c x) (d x):=by
 filter_upwards [busE P u M _ H] with F h s t
 -- h s ... . reorder props and let. universal filler
 let τ(x:ℕ):Prop:=∃ c d, Bills F (s+1) s P.par.R.L c d ∧ Ear P M F s x c d
 have hv:∀ᶠ x:ℕ in atTop,τ x:=by
    apply (h s (t.trans (Nat.le_succ _))).mono
    intro x h; obtain ⟨w,p,c,d,e,u⟩:=h; exact ⟨_,_,e,p,w,fun j l s t a o b=> u j l s t a o b⟩
 obtain ⟨x,c₀,d₀,f,t₀⟩:=hv.exists
 have he(x:ℕ):∃ c d, Bills F (s+1) s P.par.R.L c d ∧ (τ x→Ear P M F s x c d):=by
    by_cases a:τ x; · obtain ⟨c,d,f,g⟩:=a; exact ⟨_,_,f,fun _=>g⟩
    exact ⟨_,_,f,fun g=> (a g).elim⟩
 choose c d p z using he
 obtain ⟨a,C,D,g,e,h',p'⟩:=squeezeR (Nat.le_succ _) p
 exact ⟨_,_,_,_,_,g,e,h',p',hv.mono z⟩
#print axioms folle
end Calico
end YM.CF.Buffered.Afterglow.Tower
