import HectorA.InShift
import AuroraB.Gill
import Mussel.Seal
import Mussel.Foil
import Mussel.Super
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 480000
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
open PledgeT MiterT
open _root_.Yoland
local notation "ι"=>(3:Axis)
local notation "𝕌"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "Λ"=> P.wealth 3 ξ
local notation "t₀" r:max=>aislePt ι r
-- forward shifts inside clover test positions
variable (Q:SampleDose)(r:ℝ)
lemma plusShift(c:Vantage): dealt (shuf Q r) c=shuf (dealt Q c) r:=by
 obtain ⟨f,h,g⟩:=Q; unfold shuf dealt; congr 1; funext x; apply congrArg f; abel
variable (x)
abbrev beamL (D:SampleDose)(y:H):=∫ z:Vantage, (D.val z:ℂ) • (𝕌 z ((Θ).E ((z 3).toNNReal) y))
lemma callsL (D:SampleDose)(y:G): peg x y D=beamL x D (Λ y):=by
 unfold peg beamL; simp_rw [wire x D,beacon]; apply integral_congr_ae; filter_upwards with z; exact congrArg (fun i:(H)=> (D.val z:ℂ) • (𝕌 z i)) (P.bankHeat 3 ξ _ y)
lemma caesium(z:Vantage)(r:ℝ):𝕌 (z+t₀ r)=𝕌 z:=(P.cart_paves 3 ξ z (aislePt 3 r)).trans ((congrArg (fun g₀:(H).Op=> (P.cartage 3 ξ z).comp g₀) (P.cart_aisle 3 ξ r)).trans rfl)
lemma pathH(y:H)(z:Vantage)(r:ℝ)(p:0 ≤ z 3)(h:0≤r): let v:=z+t₀ r; 𝕌 v ((Θ).E ((v ι).toNNReal) y)= dawn (Θ) r (𝕌 z ((Θ).E ((z 3).toNNReal) y)):=by
 intro v; unfold dawn v
 have hp: ((z+t₀ r) 3).toNNReal=r.toNNReal+(z 3).toNNReal:=by rw [Pi.add_apply,location₁]; apply NNReal.eq; rw [NNReal.coe_add,Real.coe_toNNReal _ h,Real.coe_toNNReal _ p,Real.coe_toNNReal _ (by linarith),add_comm]
 exact timeFlux (R:=(H)) (Θ) hp (caesium x z r) y (P.warm_drive 3 ξ z _)
where timeFlux{R:Hilbert}(E:OS.Semigroup R (3:Axis)){a b t:ℝ≥0}{f g:R.Op}(u:t=a+b)(e:f=g)(y:R)(p:∀z:R,E.E a (g z)=g (E.E a z)): f (E.E t y)=E.E a (g (E.E b y)):=by rw [e,u,p,E.time]; rfl
lemma speak(D:SampleDose)(y:H)(r:ℝ)(h:0 ≤ r)(a:∀ z∈tsupport D.val,0 ≤ z 3):beamL x (shuf D r) y=dawn (Θ) r (beamL x D y):=by
 let X(z:Vantage):= ((Θ).E ((z 3).toNNReal) y); let f(z:Vantage):=𝕌 z (X z); have he:Continuous f:=P.caravan 3 ξ id X continuous_id (((Θ).continuousE _).comp (continuous_real_toNNReal.comp (continuous_apply _)))
 have hv:Integrable (fun z=>(D.val z:ℂ) • f z):= weightedMoney D _ _ he
 exact ink (R:=H) f (dawn (Θ) r) _ r hv (fun z p=>pathH x y z r p h) a
where ink{R:Hilbert}(f:Vantage→ R)(F:R.Op)(D:SampleDose)(r:ℝ)(hv:Integrable (fun z:Vantage=>(D.val z:ℂ) • f z))(h:∀z:Vantage,0 ≤ z 3→f (z+aislePt 3 r)=F (f z))(p:∀z∈tsupport D.val,0 ≤ z 3): (∫ z:Vantage, ((shuf D r).val z:ℂ) • f z)=F (∫ z:Vantage,(D.val z:ℂ) • f z):=by
        rw [← ContinuousLinearMap.integral_comp_comm _ hv,← integral_add_right_eq_self (fun z:Vantage=>((shuf D r).val z:ℂ) • f z) (aislePt 3 r)]; apply integral_congr_ae; filter_upwards with z
        rw [map_smul,show (shuf D r).val (z+aislePt 3 r)=D.val z from congrArg D.val (add_neg_cancel_right z _)]
        by_cases hz:D.val z=0; · simp only [hz,Complex.ofReal_zero,zero_smul]
        exact congrArg _ (h z (p z (subset_closure hz)))
lemma apronShift(s:ℕ)(p:ℝ)(v:0≤p){W:Bool}{L:FrameZ P W s}(e:P.birthF 3 s L.question)(F:SampleDose)(z:Vantage)(h:∀ y∈tsupport (dealt F z).val,0 ≤ y 3):L.delivery (dealt (shuf F p) z) x e=dawn (Θ) p (L.delivery (dealt F z) x e):=by
 let q:=P.viewF 3 ξ s e
 let T:=Λ q; let A:=dealt (shuf F p) z; let U:= dealt F z
 have he:peg x q A= beamL x (shuf U p) T:= (callsL x _ q).trans (congrArg (fun D:SampleDose=> beamL x D T) (plusShift F p z))
 exact he.trans ((speak x U T p v h).trans (congrArg (fun z:(H)=>dawn (Θ) p z) (callsL x U q).symm))
#print axioms apronShift
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
