import Verts.Forte
import Verts.Born
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
open _root_.YM.Preen DoseTravel
variable (x) (j:ℕ)(y:P.ManyF 3 (P.otherSpectrum 3 3 x))(v:PeriodS P d C D x j y)
local notation "θ"=>tidal P d j
local notation "Q"=> MiterT.pointT P d C D ξ
local notation "p0"=>crest P d
local notation "T"=>P.cartage 3 ξ
local notation "μ" s:max=> vistaH B Z d C D s
local notation "ν" s:max=> Λ (recoup P d C D ξ s j)
local notation "income" z:max w:max=>tempoV x d z w
lemma victory (k z:H) (w:ℝ)(n:Vantage): ‖(income k w) n-(income z w) n‖ ≤ ‖k-z‖:=by
 let S:=Ψ; let U:=(T (n-p0)); let b:=(n 3-w).toNNReal
 change ‖U (S.E b k)-U (S.E b z)‖≤ _
 exact sqC (R₀:=H) S b _ (fun y=>P.cart_norm ..) k z
where sqC{R₀:Hilbert}{a:Axis}(S:OS.Semigroup R₀ a)(w:ℝ≥0)(A:R₀.Op)(h0:∀x:R₀, ‖A x‖=‖x‖)(y z:R₀): ‖A (S.E w y)-A (S.E w z)‖ ≤ ‖y-z‖:=by rw [←map_sub,←map_sub,h0]; exact YM.ThinLoss.cost_le S _ _
variable(A:SampleDose)(l:claimV (tidal P d j) A)
#check @cloud_exact
#check @guess_exact
#check @incomeFeed
#check @pace_also
include v l
local notation "valueQ"=>MiterT.cloud P d C D x A
lemma main_ready (s:ℕ)(h:d ≤ j)(e:j ≤ s)(b:tidal P d s ≤ θ): ‖estimate P d C D x A s-MiterT.cloud P d C D x A‖ ≤ allowanceV A * ‖ν s - y‖:=
 (congrArg₂ (fun r v:H=> ‖r-v‖) (guess_exact x d C D j A l h e b) (cloud_exact x d C D j y v A l)).trans_le (differential A (tempoV x d (ν s) θ) (tempoV x d y θ) (incomeFeed x d j _ _) (incomeFeed x d j _ _) (fun i _=>victory x d (ν s) y _ i))
lemma cloud_cost : ‖MiterT.cloud P d C D x A‖ ≤ allowanceV A * ‖y‖:=by
 let Q₀:=income (0:H) θ
 let f(i:Vantage):=(A.val i:ℂ) • Q₀ i
 have e:= differential A (income y θ) Q₀ (incomeFeed x d j _ _) (incomeFeed x d j 0 _) (fun i _=>victory x d y 0 _ i)
 have hz(i:Vantage):f i=0:=smul_eq (c:=(A.val i:ℂ)) (T (i-p0)) ((Ψ).E _) -- helper
 have hr: (∫ i:Vantage, f i)=(0:H):= integral_eq hz
 have he:=cloud_exact x d C D j y v A l
 exact zero_proj (R:=H) (MiterT.cloud P d C D x A) _ _ y (allowanceV A) he hr e
where smul_eq{R:Hilbert}{c:ℂ}(f g:R.Op): c • f (g 0)=0:=by simp only [map_zero,smul_zero]
      integral_eq{R:Hilbert}{f:Vantage→R}(h:∀i,f i=0): ∫ i:Vantage,f i=(0:R):=by rw [funext h]; simp
      zero_proj{R:Hilbert}(x x' y b:R)(r:ℝ)(h:x=x')(p:y=0)(t:‖x'-y‖≤r*‖b-0‖):‖x‖≤r*‖b‖:=by simpa [h,p] using t
omit v l
include B
set_option maxHeartbeats 650000 in
lemma yield0(s:ℕ)(h₀:d ≤ s) : ‖vistaH B Z d C D s A-estimate P d C D x A s‖ ≤ allowanceV A * Hemlock.radius P d s :=by
 let V:=dealt A (central P d s)
 let a:=P.viewF 3 ξ (offer_update ..) (agentBorn P d C D s B Z); let b:=P.viewF 3 ξ s (canvas P d C D s).born
 have he:=pegCharge x V a b
 have hB:‖a-b‖ ≤ Hemlock.radius P d s:= (deputized P d C D s B Z).arrive.le
 have hx:= pace_also x d C D s h₀ A
 refine (congrArg (fun z:H=> ‖peg x a V-z‖) hx.symm).trans_le (he.trans ?_)
 dsimp only [V]; rw [deal_charge]; exact mul_le_mul_of_nonneg_left hB (no_neg _)
#print axioms main_ready
#print axioms yield0
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
