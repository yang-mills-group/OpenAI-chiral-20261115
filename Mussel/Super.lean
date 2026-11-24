import Mussel.Union
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
open PledgeT MiterT
open Broker
open Py.Rate.Pitching.Focus (Morn)
private lemma disposers (A:SampleDose)(p:A.Normalized)(y:Vantage):(dealt A y).Normalized:=⟨fun _=>p.1 _,(integral_add_right_eq_self A.val y).trans p.2⟩
open Calico
variable (F:ℕ)(C D:ℕ→ℕ→ℝ)(M:Morn P.par.K)(hM:∀i:ℕ,F ≤ i → Accordance P M F i (C i) (D i))(hq:RobeRoad P F C D x)(A:SampleDose)(p:∀i∈tsupport A.val,(1:ℝ) < i 3)(w:A.Normalized)
local notation "L0"=> P.physicalEnergy 3 ξ
local notation "ε" i:max=> Hemlock.radius P F i
local notation "qz" i:max => (central P F i)
local notation "Ap" i:max=> (dealt A (central P F i))
local notation "α" i:max=>agent P F C D i B Z
-- Lip peg ≤cost <= norm
include w
private lemma pegBound (i:ℕ)(v:(G))(u:(G))(h:∀ y∈tsupport (dealt A (central P F i)).val, 0 ≤ y 3):‖peg x v (Ap i)-peg x u (Ap i)‖ ≤ 2 * ‖v-u‖:= by
 have m:= objective x (Ap i) (disposers A w _) (b:=0) (fun y k=>h y k) v u
 let E0 := (L0).E 0
 have eq:E0 (v-u)=E0 v-E0 u:= map_sub ..
 let f(z:(G)):=‖z‖
 have he:= ((congrArg f eq).symm.trans_le (YM.ThinLoss.cost_le (L0) 0 (v-u)))
 exact m.trans (he.trans (le_mul_of_one_le_left (norm_nonneg _) (by norm_num)))
omit w
include B -- not for next
omit B in
private lemma pace_v (i:ℕ)(h:F ≤ i):
 peg x (P.viewF 3 ξ i (canvas P F C D i).born) (dealt A (central P F i))= estimate P F C D x A i :=by
 let v:=recoup P F C D (ξ) i i
 refine (congrArg (fun z:(G)=>peg x z (Ap i)) (show P.viewF 3 ξ i _ = v from round_r ..)).trans (reserve_here P F C D (ξ) i h A)
omit B
include p
lemma inside_d(i:ℕ)(v:tidal P F i < 1):∀ y∈tsupport (dealt A (central P F i)).val,0 ≤ y 3:=by
 intro y h
 have l:=p _ (pay_shift A (central P F i) h)
 rw [Pi.add_apply,MiterT.center3] at l; linarith
private lemma closish{U:Hilbert}(f g:ℕ→U)(r:ℕ→ℝ)(t:Tendsto r atTop (𝓝 0))(q:∀ᶠ i:ℕ in atTop, ‖f i - g i‖ ≤ 2*r i)(u:U)(l:Tendsto g atTop (𝓝 u)):Tendsto f atTop (𝓝 u) :=by
 have tr:Tendsto (fun i=>f i-g i) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) q (by simpa using t.const_mul (2:ℝ)))
 have h:=tr.add l; rw [zero_add] at h; exact h.congr fun i=> sub_add_cancel ..
include B hM hq w
lemma tailored:Tendsto (fun i:ℕ=>(agent P F C D i B Z).delivery (dealt A (central P F i)) x (agentBorn P F C D i B Z)) atTop (𝓝 (MiterT.cloud P F C D x A)):=by
 let g(i):= estimate P F C D x A i
 apply closish A p _ g (Hemlock.radius P F) (radiusTiny P F) _ _ (MiterT.cotton P F C D x M hM hq A ⟨1,by norm_num,p⟩)
 filter_upwards [eventually_ge_atTop F, (recessVanish P F).eventually (gt_mem_nhds zero_lt_one)] with i m h
 let a:= P.viewF 3 ξ (offer_update ..) (agentBorn P F C D i B Z); let z:=P.viewF 3 ξ i (canvas P F C D i).born
 have H': ‖a-z‖ ≤ Hemlock.radius P F i:= (deputized P F C D i B Z).arrive.le
 have eq: ‖peg x a (Ap i)- g i‖ = ‖peg x a (Ap i)-peg x z (Ap i)‖:= congrArg (fun y:(H)=> ‖peg x a (Ap i)-y‖) (pace_v F C D A i m).symm
 exact eq.trans_le ((pegBound F A w i a z (inside_d F A p i h)).trans (by gcongr))
#print axioms tailored
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
