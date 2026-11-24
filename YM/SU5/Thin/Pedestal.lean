import SatinFixedContrastNovember4
import YM.SU5.Thin.Raze

set_option autoImplicit false
set_option maxHeartbeats 150000
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
# Passage in the strong operator topology to zero intrinsic width

When operators round to the presentation in an axis-3 slab, audit with its
endpoints explicitly, on either side of each center. This is the price appropriate
to the ACTUAL resolution algebra (see `Pillar` and qualified prices on x, Aria).
Never sum raw charges at different widths and call that the physical price
on [lo,hi] if those widths weren't each paid with the right left and right heat
expenditure. Also no claim of investing in an arbitrary relation with Minkowski-space
positions. We'll check the smearability and price agreements separately NEXT.
-/
open Sifter PadThin
namespace VoucherOp
variable {P:Spine}{x:P.Spectrum0 3}{Z:Lead.Clan}{n:ℕ}{b:ℕ→ℕ} (A:P.VoucherOp x Z n b) (a:Bool) (s:ℕ) (p:Vantage) (lo hi:ℝ)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "H'"=> P.ColorHil 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "ω"=> P.wealth 3 ξ
local notation "κ"=> P.enter 3 ξ
local notation "ν"=> P.physicalEnergy 3 ξ
local notation "σ"=> P.seasons 3 ξ
local notation "R"=> P.cartage 3 ξ
local notation "V"=> P.tableau 3 ξ
local notation "F" j:max=> P.cardSchedule Z n (b j) a
local notation "W" i:max=> (A.cost i)
local notation "C" i:max=> (F i).engine P 3 ξ
local notation "X"=> A.operator a

def unpadded : (H').Op:= (A.cost s).recipe fun k=> (F (s+k)).engine P 3 ξ
private lemma negativeAt (D:P.Apron): (D.kiss P 3).engine P 3 ξ=(D.engine P 3 ξ).adjoint:= (D.peer P 3 ξ).symm
lemma arrivalOriented (y:H') : Tendsto (fun s:ℕ=> A.unpadded a s y) atTop (𝓝 ((A.operator a) y)) := by
  cases a
  · exact (A.arrival y).2.congr fun i=>congrArg (fun z:(H').Op => z y) ((Scoop.reflects H' _ _).trans (congrArg (fun f:ℕ→ (H').Op=> (A.cost i).recipe f) (funext fun k=> (negativeAt (x:=x) (P.thinString Z (b (i+k)) n)).symm)))
  exact (A.arrival y).1

-- allow arbitrary asymmetry but always pay >0 on both sides when
-- getting the limit from width-retaining (THIS sequence of) charges.
def pageSource : (H').Op:= (A.cost s).recipe fun k=>P.centralPage x p lo hi (F (s+k))
def pageFinal : (H').Op := sent H' ν (p 3-lo).toNNReal (hi-p 3).toNNReal X
lemma src_pass (u:lo<p 3)(v:p 3<hi)(y:H') : Tendsto (fun s:ℕ=> A.pageSource a s p lo hi y) atTop (𝓝 (A.pageFinal a p lo hi y)):= by
  let L(i):=(F i).realWidth P 3; have Ht:Tendsto L atTop (𝓝 0):= ((P.probeWidth_static n 3).comp A.safe.tendsto_atTop).congr fun i=>(P.schedule_width Z n (b i) 3 a).symm
  let W₁(i):= p 3-L i-lo; let W₂(i):= hi-(p 3+L i)
  apply PadThin.splits (H') ν (A.cost) (fun i=>C i) X (A.arrivalOriented a) W₁ W₂ _ _ _ _ (sub_pos.mpr u) (sub_pos.mpr v) y A.bound (A.pays a) -- tune exact?
  · exact Eq.mp (congrArg (fun x=>Tendsto W₁ atTop (𝓝 x)) (show p 3-0-lo=p 3-lo by rw [sub_zero])) ((Ht.const_sub _).sub_const _)
  exact Eq.mp (congrArg (fun x=>Tendsto W₂ atTop (𝓝 x)) (show hi-(p 3+0)=hi-p 3 by rw [add_zero])) ((Ht.const_add _).const_sub hi)

-- to projected: price for a continuum pose in that time slab.
def mixPillar : (P.ManyF 3 ξ).Op:= (A.cost s).recipe fun k=> P.pillar 3 ξ (F (s+k)) lo hi p
def reachedPillar : (H).Op:= V p (A.pageFinal a p lo hi)
lemma page_eval : A.mixPillar a s p lo hi=V p (A.pageSource a s p lo hi):=
  let Y(i:ℕ):= P.centralPage x p lo hi (F (s+i)); let D:= (R p).comp ω; let T:= ((κ).toContinuousLinearMap.comp (R (-p)))
  (congrArg (fun g:ℕ→ (H).Op=> (A.cost s).recipe g) (show (fun k=> P.pillar 3 ξ (F (s+k)) lo hi p)= (fun k=> carries («X»:=H') (Y:=H) D T (Y k)) from funext fun i=>(P.real_eval x p lo hi (F (s+i))))).trans (scooped H' H D T Y (W s)).symm
lemma reached_unad : A.reachedPillar a p lo hi = sent H σ (p 3-lo).toNNReal (hi-p 3).toNNReal (V p X):= (P.plateauThermal x p X _ _).symm
lemma page_pass (u:lo<p 3)(v:p 3<hi)(y:H) : Tendsto (fun s:ℕ=> A.mixPillar a s p lo hi y) atTop (𝓝 (A.reachedPillar a p lo hi y)) :=
  let D:= (R p).comp ω; let T:= ((κ).toContinuousLinearMap.comp (R (-p)))
  (intoCarries («X»:=H') (Y:=H) D T _ (A.src_pass a p lo hi u v) y).congr fun i=> congrArg (fun z:(H).Op=> z y) (A.page_eval a i p lo hi).symm

lemma capPillar : ‖A.mixPillar a s p lo hi‖ ≤ A.bound:= (Scoop.cap _ fun i _ => (P.pillarPay x p lo hi (F (s+i))).trans (A.pays a _))
lemma finalPay : ‖A.reachedPillar a p lo hi‖≤ ‖A.operator a‖:= (P.tableau_pay 3 ξ _ _).trans (halfNorm H' ν _ _ X) -- tune
private lemma continuousScoop (X':Hilbert)(u:Scoop)(D:ℕ→ Vantage→ X'.Op)(y:X')(h:∀ i:ℕ,Continuous (fun p=>D i p y)) : Continuous (fun p=>u.recipe (fun i=> D i p) y) := by
  simp_rw [Scoop.evaluates X']; exact continuous_finsetSum _ fun i _=> continuous_const.smul (h i)
lemma contPillar (y:H): Continuous (fun p=> A.mixPillar a s p lo hi y) := continuousScoop (H) (W s) (fun k:ℕ=>P.pillar 3 ξ (F (s+k)) lo hi) y (fun i=> P.pillar_cont x lo hi (F (s+i)) _ _ continuous_id continuous_const) -- order
lemma contFinal (y:H): Continuous (fun p=> A.reachedPillar a p lo hi y) := by
  let T (t:ℝ):= (σ).E t.toNNReal; let v(p:Vantage):= T (hi-p 3) y
  have he: Continuous v:= ((σ).continuousE _).comp (continuous_real_toNNReal.comp (continuous_const.sub (continuous_apply 3)))
  let F':= X
  let g(p:Vantage):= T (p 3-lo) (V p F' (v p))
  have hv : Continuous g:= central_contHeat H _ _ σ ((continuous_apply (3:Axis)).sub continuous_const) (P.tablets 3 ξ F' id v continuous_id he)
  exact Eq.mp (congrArg (fun g: Vantage→H=> Continuous g) (funext fun p=> (show A.reachedPillar a p lo hi y= g p from congrArg (fun z:(H).Op=> z y) (A.reached_unad a p lo hi)).symm)) hv
end VoucherOp
#print axioms VoucherOp.page_pass
#print axioms VoucherOp.contFinal
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
