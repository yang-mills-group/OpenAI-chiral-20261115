import AuroraB.Helict
import AuroraB.Scions
import AuroraB.Clockw
import AuroraB.Xphase
import SatinHeatSpecies
import AuroraB.Gill
import Mussel.Seal
import Mussel.Foil
import Mussel.Super
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Hemlock
open PledgeT MiterT Broker
namespace AuroraB
open PledgeT MiterT Broker Aloft DoseTravel Calico
open _root_.YM.Preen Py.Rate.Pitching.Focus
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
variable (U V:SampleDose)(u:PA (P:=P) d d (flipDose U 3))(v:PA (P:=P) d d V)(M:Morn P.par.K)(h:∀s:ℕ,d ≤ s→ Accordance P M d s (C s) (D s))(p:RobeRoad P d C D x)
local notation "Ωz"=>P.heaven 3 ξ
local notation "Ζ"=> P.calibration
local notation "L"=> flipDose U 3
local notation "μ" t:max=>P.singleState 3 t x
local notation "i₀" s:max t:max i:max V:max=>schema B i d C D s t (score i) V
local notation "ϕ"=>P.reflectTest 3
noncomputable abbrev rate (s t:ℕ)(Q:P.Test→ₗ[ℂ]ℂ):CrossRead:= Matrix.of fun i j=> Q (ϕ (i₀ s t i (L)) * i₀ s t j V)- Q (ϕ (i₀ s t i (L))) * Q (i₀ s t j V)
local notation "W*" s:max t:max Q:max=> wet B d C D U V s t Q
local notation "X*" s:max t:max Q:max=> rate B d C D U V s t Q
local notation "F*"=> forge d C D (x:=x) U V
noncomputable abbrev summer (s:ℕ)(Q:ℕ→P.Test→ₗ[ℂ]ℂ): CrossRead:= limUnder atTop (fun t:ℕ=>(X* s t (μ t))- (X* s t (Q t)))
local notation "wQ" s:max i:max A:max=> works B i d C D s (score i) A
local notation "r₁" s:max i:max=>inner ℂ (wQ s i (L)) (Ωz)
local notation "r₂" s:max i:max=>inner ℂ (Ωz) (wQ s i V)
-- generic CL helper
include u v h p B
variable (Q:ℕ→P.Test→ₗ[ℂ]ℂ)(f:∀t,Comparison P.calibration (P.singleState 3 t x) (Q t))
-- summarize raw & means and centered. margin.RH
lemma paysAll:Tendsto (tidal P d) atTop (𝓝 0):=recessVanish ..
include f
set_option maxHeartbeats 550000 in
lemma eclipses (a:U.Normalized)(b:V.Normalized):
 Tendsto (fun s:ℕ=>limUnder atTop (fun t=>W* s t (μ t))) atTop (𝓝 (F*)) ∧
 (∀ᶠ s:ℕ in atTop,∀t,wide B d C D s t→Cash B d C D U V Q s t) ∧
 (∀ i:Lead.Clan, Tendsto (fun s:ℕ=>limUnder atTop (fun t=>(μ t) (ϕ (i₀ s t i (L))))) atTop (𝓝 0) ∧ Tendsto (fun s:ℕ=>limUnder atTop (fun t=>(μ t) (i₀ s t i V))) atTop (𝓝 0)) ∧
 Tendsto (fun s=>summer B d C D U V s Q) atTop (𝓝 (F*)):=by
 have hp:Tendsto (fun s:ℕ=>4*Hemlock.radius P d s) atTop (𝓝 (0:ℝ)):= by simpa only [mul_zero] using (radiusTiny P d).const_mul 4
 have hs:∀ᶠ s:ℕ in atTop, tidal P d s<1:= (recessVanish P d).eventually (gt_mem_nhds zero_lt_one)
 have he:∀ᶠ s:ℕ in atTop, Thalo B d C D U V s ∧ ∀t:ℕ, wide B d C D s t→Cash B d C D U V Q s t:=
    (hs.and (hp.eventually (ge_mem_nhds zero_lt_one))).mono fun s i=>⟨dataT B d C D U V d u v s i.1,fun t h=>coinHeart B d C D U V Q f d u v s t h i.2⟩
 obtain ⟨t,xL,xR⟩:=width_current B d C D U V d u v M h p a b
 let Φ(s:ℕ)(i j:Lead.Clan):=(r₁ s i)*(r₂ s j)
 let F(s):= grime B d C D U V s
 refine ⟨t.congr' (he.mono fun s i=>i.1.joint.limUnder_eq.symm),he.mono (fun _ i=>i.2),fun i=>⟨(xL i).congr' (he.mono (fun s t=> (t.1.leaf i).limUnder_eq.symm)),(xR i).congr' (he.mono (fun s t=>(t.1.flow i).limUnder_eq.symm))⟩,?_⟩
 have hf:Tendsto (fun s:ℕ=>F s-(Matrix.of (Φ s):CrossRead)) atTop (𝓝 (F*)):=matSad (R:= (P.ManyF 3 ξ)) Ωz (b:=fun s i=> wQ s i (L)) (c:=fun s i=> wQ s i V) t xL xR
 apply hf.congr'
 filter_upwards [he] with s ⟨hS,t⟩
 apply Eq.symm
 apply Filter.Tendsto.limUnder_eq
 refine tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>?_
 have hT:= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (hS.joint) i) j
 have he:= hT.sub ((hS.leaf i).mul (hS.flow j))
 refine he.congr' ((looms B d C D s).mono fun k p=>?_)
 let E:= t k p
 let a:=ϕ (i₀ s k i (L)); let b:=i₀ s k j V
 change (μ k) (a*b)-(μ k) a*(μ k) b = _- (Q k (a*b)-Q k a*Q k b)
 rw [show Q k (a*b)=0 from E.split i j,show Q k a=0 from E.zeroLeft i, show Q k b=0 from E.zeroRight j]; ring; rfl
where matSad{R:Hilbert}(w:R){a:ℕ→CrossRead}{A:CrossRead}{b c:ℕ→Lead.Clan→(R).space}(h:Tendsto a atTop (𝓝 A))(p:∀ i,Tendsto (fun s=>inner ℂ (b s i) w) atTop (𝓝 0))(v:∀ i,Tendsto (fun s=>inner ℂ w (c s i)) atTop (𝓝 0)): Tendsto (fun s=> a s-(Matrix.of fun i j=> inner ℂ (b s i) w *inner ℂ w (c s j))) atTop (𝓝 A):=by
        have he:Tendsto (fun s=>(Matrix.of (fun i j=>inner ℂ (b s i) w *inner ℂ w (c s j)):CrossRead)) atTop (𝓝 0):=by refine tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>?_ ; change Tendsto (fun s=> _*_) atTop (𝓝 (0:ℂ)); simpa only [zero_mul] using (p i).mul (v j)
        simpa only [sub_zero] using h.sub he
#check @dataT
#check @width_current
#print axioms eclipses
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
