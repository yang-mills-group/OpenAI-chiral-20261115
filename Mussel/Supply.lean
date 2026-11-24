import Mussel.Thread
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
variable (s:ℕ){f:P.Test}(Kpp:Sentry P s f)(z:ℕ → Cover)
private lemma apply_cost {U:Hilbert}(F:U.Op)(D:ℕ→U.Op)(ω':U)(a:ℕ→U)(f1:∀ i,D i ω'=ω')(g:∀ i (x:U),‖D i x‖=‖x‖)(e:Tendsto a atTop (𝓝 ω')) : Tendsto (fun i=> F (D i (a i))) atTop (𝓝 (F ω')) :=by
 apply F.continuous.continuousAt.tendsto.comp (f:=fun i=> D i (a i))
 apply tendsto_iff_norm_sub_tendsto_zero.mpr
 refine (tendsto_iff_norm_sub_tendsto_zero.mp e).congr fun i=>?_
 nth_rw 2 [←f1 i]; rw [←map_sub,g]
local notation "S"=>P.physicalEnergy 3 ξ
include B
private lemma primary :
 let b := whenly (timeMesh P.par) s Kpp.w
 let p(i:ℕ):= (purity Z)⁻¹ • P.shard x Z (c i) (r i)
 Tendsto (fun i:ℕ=> Kpp.beam ξ (P.truck 3 ξ (P.vtile (c i) (z i)) ((S).E b (p i)))) atTop (𝓝 (Kpp.beam ξ ω)):=
 apply_cost (U:=(G)) (Kpp.beam ξ) (fun i=>P.truck 3 ξ (P.vtile (c i) (z i))) (ω) _ (fun i=> P.truck_empty ..) (fun i v=>P.truck_norm ..) (short_born B Z _ (when_pos _ _ _ Kpp.ok))

section
omit B
private lemma bLoan {U:Hilbert}{r:ℕ → Prop}(g:(i:ℕ) → r i → U)(x:U)(f:ℕ → U)(e:Tendsto f atTop (𝓝 x))(c:∀ᶠ i in atTop,r i)(u:∀ i p,g i p=f i):∀ ε:ℝ,0<ε  →  ∀ᶠ i:ℕ in atTop,∃ p:r i, ‖g i p-x‖ < ε := by
 intro ε p
 have h:= (tendsto_iff_norm_sub_tendsto_zero.mp e).eventually (gt_mem_nhds p)
 exact (c.and h).mono fun i ⟨hi,h⟩=> ⟨hi,by rw [u]; exact h⟩
end
set_option maxHeartbeats 600000 in
lemma ribbons_exposed(covers:∀ᶠ i:ℕ in atTop,s ≤ c i):
    ∀ ε:ℝ,0<ε → ∀ᶠ i:ℕ in atTop,∃ h:s ≤ c i,
      ‖P.viewF 3 (P.otherSpectrum 3 3 x) (c i) (playClock Z (c i) (r i) (z i) s Kpp h).born - Kpp.beam ξ ω‖ < ε:=by
 let F(i:ℕ)(h:s ≤ c i):= playClock Z (c i) (r i) (z i) s Kpp h
 let b(i:ℕ)(h:s ≤ c i):= P.viewF 3 ξ (c i) (F i h).born
 exact bLoan (U:=(G)) b _ _ (primary B Z s Kpp z) covers (fun i h=> receipt_transfer Z (c i) (r i) _ s Kpp h) -- implicit x
end Habitat
#print axioms Habitat.ribbons_exposed
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
