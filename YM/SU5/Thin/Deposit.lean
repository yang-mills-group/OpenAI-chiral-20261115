import SatinFixedContrastNovember4
import YM.SU5.Thin.Magister

set_option autoImplicit false
set_option maxHeartbeats 190000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
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
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
/-!
# Lower-bound track

Don't normalize by read signs after extraction etc. Earn bound from estimated
weakly damped time mark price at this very registration and for every repeat
used. For the reader this means pay the SAME purchases (`Cost price pupil`);
for the product competitor use also THESE new mixtures, all stamps etc.
-/
open DoseBill Sifter VoucherOp Theatre PadThin
open StrongStamp
namespace StrongStamp
lemma polarFlow (X Y:Hilbert)(S:OS.Semigroup X (3:Axis))(A:X.Op)(C:Y.Op)(G: Y.Op)(z:Y.Op→ X.Op)(e d:ℝ≥0)(h:A=sent X S e d (z C))(q:∀ x, (z x).adjoint= z x.adjoint)(v: C= G.adjoint) : A.adjoint= sent X S d e (z G):=by rw [h,halfStar,q,v,ContinuousLinearMap.adjoint_adjoint]
lemma mirrorPage (X:Hilbert)(S:OS.Semigroup X (3:Axis))(e d:ℝ)(A:Vantage→X.Op)(T:Vantage→X.Op)(v:X)(h:∀ y: Vantage→X, Continuous y→ Continuous fun i=> T i (y i))(q:∀ p,A p=sent X S (d-p 3).toNNReal (p 3-e).toNNReal (T p)): Continuous (fun i=> A i v) :=by
  have he: Continuous (fun p:Vantage=>p 3-e):=(continuous_apply (3:Axis)).sub continuous_const
  simp_rw [q]
  exact central_contHeat X _ _ S (continuous_const.sub (continuous_apply (3:Axis))) (h _ (((S).continuousE v).comp (continuous_real_toNNReal.comp he)))
def dualOp (X:Hilbert)(A:X.Op) : X.Op:= A.adjoint
def CoMove (X:Hilbert)(A: Vantage→ X.Op): Prop:= ∀ x:X,Continuous (fun p=> A p x)
end StrongStamp
namespace VoucherOp
variable {P:Spine}{x:P.Spectrum0 3}{b:ℕ→ℕ}{Z:Lead.Clan}{n:ℕ}(K:P.VoucherOp x Z n b)(F:SampleDose)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "H'"=> P.ColorHil 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "ω"=>P.colorZero 3 ξ
local notation "ν"=>P.heaven 3 ξ
local notation "σ"=>P.seasons 3 ξ
local notation "μ"=> P.physicalEnergy 3 ξ
local notation "E"=> (P.physicalEnergy 3 ξ).E
local notation "π"=> P.wealth 3 ξ
local notation "τ"=>P.tableau 3 ξ
local notation "R"=> purePrice Z
local notation "ρ"=> (↑(purePrice Z):ℂ)
local notation "B" i:max => P.thinString Z (b i) n
local notation "κ" p:max => P.cartage 3 ξ p

-- use ν' on full H', need h∈ℝ estimator
variable (t:ℝ≥0)(ε:ℝ)
variable (G:Weather P x t ε n b)(p:Vantage)(lo hi:ℝ){a d:ℝ≥0}(u:t≤a)
include u G
lemma alongTrue :
    dist ((sent H σ a d (τ p (K.operator true))) ν) (ρ • ν) ≤ ε * R  := walk H' H μ a d K.issue ω ν ρ (sent H σ a d (τ p K.issue)) π (κ p) (κ (-p)) ((P.enter 3 ξ).toContinuousLinearMap) (ε*R) (K.pricedSource t ε G u) (P.stone_mark 3 ξ) (P.cart_empty 3 ξ p) (P.cart_empty 3 ξ (-p)) rfl (P.enter_wealth 3 ξ) (P.cart_pay 3 ξ p) (P.sector_hot 3 ξ d) ((P.plateauThermal x p K.issue a d).trans (P.pivot_eval x p (sent H' μ a d K.issue)))
-- careful sign/time of reaching θ, twisted by oppose on budgets.
omit u G
private lemma orientation_false : K.operator false = ContinuousLinearMap.adjoint K.issue:= rfl
lemma adjBackward : (dualOp H (K.reachedPillar false p lo hi))= sent H σ (hi-p 3).toNNReal (p 3-lo).toNNReal (τ p K.issue) := polarFlow H H' σ (K.reachedPillar false p lo hi) (K.operator false) K.issue (τ p) _ _ (K.reached_unad false p lo hi) (P.boards_star 3 ξ p) (orientation_false K)
lemma adjCont : CoMove H (fun p=> dualOp H (K.reachedPillar false p lo hi)) := fun y=> mirrorPage H σ lo hi _ (fun p=> τ p K.issue) y (fun f t=>P.tablets 3 ξ _ id f continuous_id t) (fun p=> K.adjBackward p lo hi)
end VoucherOp
#print axioms VoucherOp.pricedSource
#print axioms VoucherOp.adjBackward
#print axioms VoucherOp.alongTrue
#print axioms VoucherOp.adjCont
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
