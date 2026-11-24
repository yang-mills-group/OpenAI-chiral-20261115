import Verts.Mains
import Verts.Whirr
import AuroraB.Clot
import Minnow.Younger
import Acacia.Loom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 550000
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
open _root_.YM.Preen DoseTravel _root_.Acacia
variable (j:ℕ)(y:P.ManyF 3 (P.otherSpectrum 3 3 x))(v:PeriodS P d C D x j y)(w:ℝ)(l:tidal P d j < w)
local notation "θ"=>tidal P d j
local notation "T"=>P.cartage 3 ξ
local notation "ς" z:max=>MiterT.cloud P d C D x z
local notation "p0"=>crest P d
local notation "ν" s:max=> Λ (recoup P d C D ξ s j)
local notation "fieldJ" A:max n:max t:max=>_root_.Yoland.pay (Ψ) n t (MiterT.cloud P d C D x (shuf A (-t)))
variable (U:SampleDose)(s:ℕ)(N:ℕ)
#check @yield0
#check @main_ready
include B v
lemma earnedQ(h:d ≤ j)(e:j ≤ s)(b:tidal P d s ≤ θ)(u:claimV (tidal P d j) U): ‖vistaH B Z d C D s U- MiterT.cloud P d C D x U‖ ≤ allowanceV U *(Hemlock.radius P d s + ‖ν s-y‖):=
 differential0 (R:=H) (vistaH B Z d C D s U) (MiterT.cloud P d C D x U) (estimate P d C D x U s) (yield0 x B Z d C D U s (h.trans e)) (main_ready x d C D j y v U u s h e b)
where differential0{R:Hilbert}(z y' e':R){a b c:ℝ}(h:‖z-e'‖≤a*b)(p:‖e'-y'‖≤a*c):‖z-y'‖≤a*(b+c):=by
        rw [show z-y'=z-e'+(e'-y') from by abel,mul_add]; exact (norm_add_le _ _).trans (add_le_add h p)
local notation "Rj" s:max=>Hemlock.radius P d s+‖ν s-y‖
local notation "κ"=> w-tidal P d j -- conflict parameter K:P.Register; rename.
local notation "pQ" s:max=> _root_.Yoland.frame (Ψ) N (P.macroStep s) (_root_.Yoland.dawn (Ψ) (κ))
local notation "tQ"=> _root_.Yoland.pay (Ψ) N (κ)
include l
lemma teen(h:d ≤ j)(e:j ≤ s)(b:tidal P d s ≤ θ)(u:claimV w U): ‖works B Z d C D s N U - fieldJ U N (κ)‖ ≤ allowanceV U * (‖pQ s‖ * (Rj s) + ‖pQ s-tQ‖ * ‖y‖):=by
 let W:= shuf U (-(κ)); have he:claimV θ W:=by intro i h; have v:=u _ ((shuf_iff ..).mp h); rw [Pi.sub_apply,location₁] at v; linarith only [v]
 have hp:claimV θ U:=fun i p=>l.trans (u i p)
 have ht:= charged_pay B Z d C D s N θ b U hp (w- tidal P d j) (sub_nonneg.mpr l.le) (by rw [add_sub_cancel ..]; exact u)
 let b₁:=vistaH B Z d C D s W; let b₂:= MiterT.cloud P d C D x W
 have hc:‖b₁-b₂‖≤allowanceV U*(Rj s):=by
    have hx:=earnedQ B Z d C D j y v W s h e b he -- order, explicit v
    exact hx.trans_eq (congrArg (fun i:ℝ=>i*(Rj s)) (show allowanceV W=allowanceV U from shuf_charge U _))
 have hv:‖b₂‖ ≤ allowanceV U * ‖y‖:=by
    have h0:= cloud_cost x d C D j y v W he
    exact h0.trans_eq (congrArg (fun i:ℝ=>i*(‖y‖)) (show allowanceV W=allowanceV U from shuf_charge U _))
 exact abs_q (R:=H) (pQ s) tQ b₁ b₂ _ (allowanceV U) (‖y‖) _ ht hc hv
where abs_q{R:Hilbert}(A E:R.Op)(b x k:R)(a₀ v w:ℝ)(h:k=A b)(v':‖b-x‖≤a₀*w)(l:‖x‖ ≤ a₀*v): ‖k-E x‖ ≤ a₀*(‖A‖*w+‖A-E‖*v):=by
       rw [h,show A b-E x=A (b-x)+(A-E) x from by rw [map_sub,ContinuousLinearMap.sub_apply]; abel]
       refine (norm_add_le ..).trans ((add_le_add ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left v' (norm_nonneg _))) (((A-E).le_opNorm _).trans (mul_le_mul_of_nonneg_left l (norm_nonneg _)))).trans ?_)
       apply le_of_eq; ring
#print axioms earnedQ
#print axioms teen
#check @lobeR
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
