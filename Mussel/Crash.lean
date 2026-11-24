import Mussel.Dome
import Mussel.Pad
import Mussel.Spread
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
variable (T:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
open PledgeT.MiterT
local notation "S"=> P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "E"=> (P.physicalEnergy 3 (P.otherSpectrum 3 3 x)).E
local notation "U"=>P.cartage 3 (P.otherSpectrum 3 3 x)
local notation "B"=>P.wealth 3 (P.otherSpectrum 3 3 x)
variable (x)(F:SampleDose)(p:F.Normalized)
noncomputable def beacon(y:G)(q:Vantage):= U q (B (E (Real.toNNReal (q 3)) y))
lemma beaming(y:G): Continuous (fun q=>beacon x y q):= P.caravan 3 ξ id _ continuous_id ((B).continuous.comp (((P.physicalEnergy 3 ξ).continuousE y).comp (continuous_real_toNNReal.comp (continuous_apply _))))
lemma wire (y:G)(q:Vantage): scoop P x y F q=(F.val q:ℂ) • beacon x y q :=
 (map_smul ((U q).comp B) (F.val q:ℂ) ((E (Real.toNNReal (q 3))) y))
lemma scoop_empty(q:Vantage):beacon x ω q= Ω:=
 (congrArg (U q) ((P.bankHeat 3 ξ (Real.toNNReal (q 3)) ω).trans ((congrArg ((S).E (Real.toNNReal (q 3))) (P.stone_mark 3 ξ)).trans (P.heaven_hot 3 ξ (Real.toNNReal (q 3)))))).trans (P.cart_empty 3 ξ q)
private lemma conserved {X Y:Hilbert}{a:Axis}(J:OS.Semigroup X a)(D:X →L[ℂ] Y)(U':Y.Op)(v:∀ y:Y, ‖U' y‖=‖y‖)(p:∀ x:X, ‖D x‖≤‖x‖){b t:ℝ≥0}(h:b≤ t)(y z:X): ‖U' (D (J.E t y))-U' (D (J.E t z))‖ ≤ ‖J.E b y-J.E b z‖:=by
 rw [←map_sub,←map_sub,←map_sub,←map_sub (J.E b),v]; exact (p _).trans (YM.ThinLoss.cost_mono J h _)
lemma conservation(q:Vantage){b:ℝ≥0}(h:(b:ℝ) ≤ q 3)(y z:G): ‖beacon x y q-beacon x z q‖ ≤ ‖E b y-E b z‖:= conserved (P.physicalEnergy 3 ξ) B (U q) (fun y=> P.cart_norm ..) (fun y=> P.bank_cost ..)
 ((Real.le_toNNReal_iff_coe_le ((NNReal.coe_nonneg _).trans h)).mpr h) y z

variable {X:Hilbert}
include p
private lemma endeavor (f g:Vantage→X)(α β:Vantage→X)(ef:∀ z,α z=(F.val z:ℂ) • f z)(eg:∀ z,β z=(F.val z:ℂ) • g z)(u:Continuous f)(v:Continuous g)(C:ℝ)(e:∀z∈tsupport F.val, ‖f z-g z‖ ≤ C): ‖(∫ z,α z)-(∫ z,β z)‖ ≤ C:=by
 let ψ(f:Vantage→X)(z:Vantage):=(F.val z:ℂ) • f z
 have hi(f:Vantage→X)(h:Continuous f): Integrable (ψ f):= weightedMoney F _ _ h
 rw [show α=ψ f from funext ef,show β=ψ g from funext eg,←integral_sub (hi f u) (hi g v)]
 apply (norm_integral_le_integral_norm _).trans
 have d:Integrable F.val:= F.smooth.continuous.integrable_of_hasCompactSupport F.budget
 have hv:Integrable (fun q=> ‖ψ f q-ψ g q‖):=((hi f u).sub (hi g v)).norm
 suffices ∀ q, ‖ψ f q-ψ g q‖ ≤ F.val q*C by
    have hs:=integral_mono hv (d.mul_const _) this; rwa [integral_mul_const,p.2,one_mul] at hs
 intro q; unfold ψ; rw [←smul_sub,norm_smul,Complex.norm_real,Real.norm_of_nonneg (p.1 q)]
 by_cases h:F.val q=0
 · rw [h,zero_mul,zero_mul]
 exact mul_le_mul_of_nonneg_left (e _ (subset_closure h)) (p.1 q)
lemma objective (b:ℝ≥0)(h:∀ i∈ tsupport F.val,(b:ℝ)≤ i 3)(y z:G): ‖peg x y F - peg x z F‖ ≤ ‖E b y-E b z‖:=
 endeavor F p (beacon x y) (beacon x z) _ _ (wire x F y) (wire x F z) (beaming x y) (beaming x z) _ (fun i H'=>conservation x i (h i H') y z)
private lemma settle (f:Vantage→X)(a:X)(g:∀ z,f z=(F.val z:ℂ) • a):∫ z,f z=a:=by simp_rw [g,Complex.coe_smul]; rw [integral_smul_const,p.2,one_smul]
lemma objective0 : peg x ω F= Ω:= settle F p _ (Ω) (fun q=> (wire x F ω q).trans (congrArg (fun a:(H)=> (F.val q:ℂ) • a) (scoop_empty x q)))
-- abstract again
omit p in
private lemma closing {X Y:Hilbert} (ω':X)(Ω':Y)(R:X→Y)(f:X.Op)(eq:R ω'=Ω')(hf:f ω'=ω')(g:∀ x:X, ‖R x - R ω'‖ ≤ ‖f x-f ω'‖)(a:ℕ→X)(h:Tendsto (fun i=> f (a i)) atTop (𝓝 ω')) : Tendsto (fun i=>R (a i)) atTop (𝓝 Ω'):=by
 have q:Tendsto (fun i=> ‖f (a i)- ω'‖) atTop (𝓝 0):=tendsto_iff_norm_sub_tendsto_zero.mp h
 apply tendsto_iff_norm_sub_tendsto_zero.mpr
 exact squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (Eventually.of_forall fun i=> by simpa only [eq,hf] using g (a i)) q
lemma tailPeg (b:ℝ≥0)(_hp:0<b)(h:∀ i∈ tsupport F.val,(b:ℝ) ≤ i 3)(Y:ℕ→G)(t:Tendsto (fun i=> E b (Y i)) atTop (𝓝 ω)) : Tendsto (fun i=>peg x (Y i) F) atTop (𝓝 Ω):= closing (X:=G) (Y:=H) (ω) Ω (fun g=>peg x g F) (E b) (objective0 x F p) (congrArg (P.enter 3 ξ) (P.heaven_hot 3 ξ b)) (fun y=>objective x F p b h y ω) Y t
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
