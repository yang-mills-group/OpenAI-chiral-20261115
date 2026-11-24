import AuroraB.Clot
import Minnow.Younger
import Acacia.Loom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 530000
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
variable (x)(F:SampleDose)
def allowanceV(U:SampleDose):ℝ:= ∫ i:Vantage,|U.val i|
lemma no_neg(A:SampleDose):0≤ allowanceV A:= integral_nonneg fun _=>abs_nonneg _
lemma shuf_charge (A:SampleDose)(r:ℝ): allowanceV (shuf A r)=allowanceV A:= integral_add_right_eq_self (fun i:Vantage=>|A.val i|) _
lemma deal_charge(A:SampleDose)(y:Vantage): allowanceV (dealt A y)=allowanceV A:= integral_add_right_eq_self (fun i:Vantage=>|A.val i|) _
section
omit x
variable {R₁:Hilbert}
lemma differential (f g : Vantage→(R₁).space)
 (u:Integrable fun q:Vantage=> (F.val q:ℂ) • f q)
 (v: Integrable fun q:Vantage=> (F.val q:ℂ) • g q)
 {R:ℝ}(h: ∀ i ∈ tsupport F.val, ‖f i-g i‖ ≤ R): ‖(∫ z:Vantage,(F.val z:ℂ) • f z) - (∫ z:Vantage,(F.val z:ℂ) • g z)‖ ≤ allowanceV F * R:=by
 rw [←integral_sub u v]; apply (norm_integral_le_integral_norm _).trans
 let D(q:Vantage):=|F.val q|
 have k(q:Vantage): ‖(F.val q:ℂ) • f q - (F.val q:ℂ) • g q‖ ≤ D q * R:=by
    rw [←smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs]
    by_cases p:F.val q=0
    · simp only [D,p,abs_zero,zero_mul,le_refl]
    exact mul_le_mul_of_nonneg_left (h _ (subset_closure p)) (abs_nonneg _)
 have B:=integral_mono ( (u.sub v).norm) (((F.smooth.continuous.integrable_of_hasCompactSupport F.budget).abs).mul_const R) k
 simpa only [integral_mul_const,Pi.sub_apply,D,allowanceV] using B
end
lemma pegCharge (y z:G): ‖peg x y F-peg x z F‖ ≤ allowanceV F * ‖y-z‖:=by
 let fy(v:G)(i):=beacon x v i
 let f(v:G)(q:Vantage):=(F.val q:ℂ) • fy v q
 have hv(v:G): Integrable (fun q:Vantage=> (F.val q:ℂ) • fy v q):= weightedMoney F _ _ (beaming x v)
 have h(q:Vantage):‖fy y q - fy z q‖ ≤ ‖y-z‖:=by
    let U:=P.cartage 3 ξ q; let B:=P.wealth 3 ξ; let S:= (P.physicalEnergy 3 ξ); let P':= S.E (Real.toNNReal (q 3))
    change ‖U (B (P' y))-U (B (P' z))‖ ≤_
    exact sqB (R₀:=(H)) (T₀:=G) S _ (P.cartage 3 ξ q) (fun z=>P.cart_norm ..) (P.wealth 3 ξ) (fun z=>P.bank_cost ..) _ _
 unfold peg; simp_rw [wire]; exact differential F (fy y) (fy z) (hv y) (hv z) (fun q _=>h q)
where sqB{R₀ T₀:Hilbert}{a:Axis}(S:OS.Semigroup T₀ a)(w:ℝ≥0)(A:R₀.Op)(h0:∀x:R₀, ‖A x‖=‖x‖)(B:T₀→L[ℂ]R₀)(h1:∀x:T₀,‖B x‖≤‖x‖)(y z:T₀): ‖A (B (S.E w y))-A (B (S.E w z))‖ ≤ ‖y-z‖:=by rw [←map_sub,←map_sub,←map_sub,h0]; exact (h1 _).trans (YM.ThinLoss.cost_le S _ _) 
lemma pace_also(i:ℕ)(hd:d ≤ i)(A:SampleDose): peg x (P.viewF 3 ξ i (canvas P d C D i).born) (dealt A (central P d i))= estimate P d C D x A i :=by
 let v:=recoup P d C D ξ i i
 refine (congrArg (fun z:G=>peg x z (dealt A (central P d i))) (show P.viewF 3 ξ i _ = v from round_r ..)).trans (reserve_here P d C D ξ i hd _)
#print axioms pegCharge
#print estimate
#check reserve_here
#check outingP
#print MiterT.cloud
#check cotton
end AuroraB.Verts
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
