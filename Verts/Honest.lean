import Verts.Assay
import Minnow.Output
import AuroraB.Clot
import Minnow.Younger
import Acacia.Loom
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
open PledgeT MiterT Broker Aloft
open Py.Rate.Pitching.Focus (Morn)
namespace AuroraB.Verts
open Calico _root_.Yoland
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "φ" s:max=> (P.macroStep s:ℂ)
local notation "χ" t:max=>P.singleState 3 t x
local notation "isp" v:max=>aislePt (3:Axis) v
local notation "kd" s:max=> offer_update P d C D s B Z
local notation "Τ" s:max => agent P d C D s B Z
local notation "X" s:max t:max n:max U:max=> schema B Z d C D s t n U
local notation "Ψ"=> P.seasons 3 ξ
local notation "Λ"=> P.wealth 3 ξ
open PledgeT MiterT
open Spine.RulingL
variable (U V:SampleDose)(δ:ℝ)
variable{A R:Doorway} (u:tsupport U.val ⊆ A.invites)(v:tsupport V.val ⊆ R.invites)(l:A.upper 3 ≤ -1)(r₁:1 ≤ R.lower 3)
variable (f:Swept B d C D U V δ)(M:Morn P.par.K)(p:∀ s:ℕ,d ≤ s → Accordance P M d s (C s) (D s))(hq:RobeRoad P d C D x)
local notation "Q₀"=> flipDose U 3
noncomputable def billU (x:P.Spectrum0 3):CrossRead:= Matrix.of fun i j=> inner ℂ (fieldLimit x d C D (score i) (flipDose U 3)) (fieldLimit x d C D (score j) V)
include u v l r₁
lemma alignedTw : claimV 1 (flipDose U 3) ∧ claimV 1 V:=by
 refine ⟨fun i h=>?_,fun i p=>lt_of_le_of_lt r₁ ((v p) 3 (Set.mem_univ _)).1⟩
 rw [flipBudget] at h; have e:=lt_of_lt_of_le (((u h) 3 (Set.mem_univ _)).2) l
 change opposeR 3 i 3 < -1 at e; rw [show opposeR 3 i 3= -i 3 from if_pos rfl] at e; linarith
#check @Swept.forte
#check @presented
include f M p hq B
set_option maxHeartbeats 750000 in
lemma tariff_cost : tariffen d C D (x:=x) U V δ=billU d C D U V x:=by
 let Tv(i j: Lead.Clan)(s t:ℕ):=(χ t) ((P.reflectTest 3 (schema B i d C D s t (score i) (Q₀)))*schema B j d C D s t (score j) V)
 let F(s t:ℕ):CrossRead:=Matrix.of (fun i j=>Tv i j s t)
 have hp:Tendsto (fun s:ℕ=>limUnder atTop (F s)) atTop (𝓝 (tariffen d C D (x:=x) U V δ)):=f.forte
 let g:= alignedTw U V u v l r₁
 let K:= billU d C D U V x
 have hf:Tendsto (fun s=>limUnder atTop (F s)) atTop (𝓝 K):=by
    refine matrixTol K F (fun i j=>?_)
    have hM:= (presented B i d C D j 1 (score i) (score j) (Q₀) V M p hq zero_lt_one g.1 g.2)
    let W(s):= Thalo B d C D U V s
    have he:∀ᶠ s:ℕ in atTop,W s:=f.needs.mono fun i p=>p.1
    have hr:Tendsto (fun s=>limUnder atTop (Tv i j s)) atTop (𝓝 (K i j)):= hM.present
    refine hr.congr' (he.mono fun s z=>?_)
    have hp:Tendsto (F s) atTop _:=z.joint
    exact commutes (F s) hp i j
 exact tendsto_nhds_unique hp hf
where matrixTol (A:CrossRead)(F:ℕ→ℕ→CrossRead)(p:∀i j:Lead.Clan,Tendsto (fun s=>limUnder atTop (F s) i j) atTop (𝓝 (A i j))): Tendsto (fun s=>limUnder atTop (F s)) atTop (𝓝 A):= by exact tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mpr (p i))
      commutes (F:ℕ→ CrossRead){A:CrossRead}(p:Tendsto F atTop (𝓝 A))(i j:Lead.Clan):limUnder atTop (fun t:ℕ=>F t i j)= (limUnder atTop F) i j:=by rw [p.limUnder_eq]; exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp p i) j).limUnder_eq
#print axioms tariff_cost
#check @alignedTw
#check @billU
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
