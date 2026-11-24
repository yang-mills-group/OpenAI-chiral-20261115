import NeedleW.Tends
import NeedleW.Rays
import Aloft.Resolve
import NeedleW.Line
import Aloft.Spoon
import Aloft.BudgetA
import Aloft.Ride
import Aloft.Conceit
import Aloft.ZL
import Aloft.Canon
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 750000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) 
namespace Aloft
open Py.Dyad Keeping Py.Rate.Pitching.Focus
open _root_.YM.Preen
local notation "j0"=> (3:Axis)
variable (M:Morn P.par.K)(α:ℝ)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(p:∀ s,F ≤ s→ Accordance P M F s (C s) (D s))(u:RobeRoad P F C D x)(v:Jones P M α F C D x)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "Ψ"=> P.seasons 3 ξ
local notation "H"=>P.ManyF 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "A₀"=>paster (Ω)
local notation "U"=>P.cartage 3 ξ
namespace Anchovy
open _root_.NeedleW
variable (J:P.Ellis 3 x)
open Habitat.Hemlock.AuroraB Verts
open _root_.Yoland _root_.NeedleW
attribute [local instance] InnerProductSpace.complexToReal
variable (v0:Enviro P x)(q:Fever P F C D x)(G:ℕ→ (P.ManyF 3 (P.otherSpectrum 3 3 x)).space)(g:∀ i,F ≤ i→PeriodS P F C D x i (G i))
local notation "τ" j:max=> (tidal P F j).toNNReal
local notation "ϑ" j:max=> tidal P F j
local notation "Q"=>pointT P F C D ξ
local notation "N" i:max p:max=>zoomV x F C D i p
local notation "isp" v:max=>aislePt (3:Axis) v
variable (y:Vantage)
local notation "R"=>textQ P F C D x y
local notation "zQ" j:max=> A₀ (G j)
include g
-- lower grant for true point norm across all spatial variables. nearer than θ_j.
set_option maxHeartbeats 650000 in
lemma cellar_income(j:ℕ)(e:F ≤ j){t:ℝ}(h:0<t)(r:t ≤ ϑ j): ‖zQ j‖ ≤ ‖R t‖:=by
 let v:= y+isp (t-y 3); have hv:v 3=t:=by unfold v; rw [Pi.add_apply,location₁]; ring
 let m:= ((eventually_ge_atTop F).and ((recessVanish P F).eventually (gt_mem_nhds h))).exists
 let i:=m.choose; have p:=m.choose_spec
 let S:= (Ψ); let a:= (t-ϑ i).toNNReal; let b:= (ϑ j-t).toNNReal
 let Z:= (U (v-crest P F)); let k:= zQ i
 have hp:τ i ≤ τ j:= Real.toNNReal_le_toNNReal (p.2.le.trans r)
 have ht:b+a=(τ j)-(τ i):=by
    apply NNReal.eq; unfold a b; rw [NNReal.coe_sub hp,NNReal.coe_add,Real.coe_toNNReal _ (sub_nonneg.mpr r),Real.coe_toNNReal _ (sub_nonneg.mpr p.2.le), Real.coe_toNNReal _ (tide_price P F j).le, Real.coe_toNNReal _ (tide_price P F i).le]; ring
 have hz:S.E b (S.E a k)=zQ j:=Eq.trans ((DFunLike.congr_fun (S.time b a).symm k).trans (congrArg (fun t:ℝ≥0=>S.E t k) ht)) (parcelH P F C D x G g p.1 e hp)
 have he:R t=Z (S.E a (G i)):=by
    unfold textQ; change Q v=Z _; exact ((g i p.1).2 v (p.2.trans_le (le_of_eq hv.symm))).trans (congrArg (fun t:ℝ=>Z (S.E (t-ϑ i).toNNReal (G i))) hv)
 have hK:= keep_heat (X:=(H)) _ (P.stone_norm 3 ξ) S (P.heaven_hot 3 ξ) a (G i)
 have hl: ‖S.E a k‖ ≤ ‖R t‖:= struck (T:=(H)) a S k _ _ k (A₀) Z hK he (fun y=>P.cart_norm ..) (pasted_cost (X:=(H)) Ω)
 exact (le_of_eq ((congrArg (fun z_:H=>‖z_‖) hz.symm))).trans ((( (S.E b).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks b))).trans hl)
where struck{T:Hilbert}(t:ℝ≥0)(S:OS.Semigroup T (3:Axis))(k y x z:T)(F A:T.Op)(h:S.E t k= F (S.E t y))(v:x=A (S.E t y))(u:∀x:T,‖A x‖=‖x‖)(w:‖F‖≤1):‖S.E t k‖ ≤ ‖x‖:=by rw [h,v,u]; exact (F.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) w)
-- struck has unused z, give k
lemma exit : ∀i:ℕ,AntitoneOn (fun t=> ‖iteratedDeriv i (R) t‖) (Ioi 0):=by
 rintro i t h1 p h2 e; rcases lt_or_eq_of_le e with h|hEq
 · let r:ℝ≥0:=(p-t).toNNReal
   let S:=(Ψ)
   have hz:=ferryN P F C D x G g y i t p h1 h
   let f:= iteratedDeriv i (R)
   exact (le_of_eq (congrArg (fun z':H=> ‖z'‖) hz.symm)).trans (((S.E r).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)))
 exact le_of_eq (congrArg (fun t:ℝ=>‖iteratedDeriv i (R) t‖) hEq.symm)
include q p J v v0
lemma leaves : Tendsto (fun t=> ‖(R) t‖) (𝓝[>] (0:ℝ)) atTop:=by
 refine Filter.tendsto_atTop.mpr fun b=>?_
 obtain ⟨j,h,hL⟩:= ((eventually_ge_atTop F).and ((tendency P M α F C D x p v J v0 q G g).eventually_ge_atTop b)).exists -- order ?
 have hx:∀ᶠ i:ℝ in 𝓝[>] (0:ℝ),0 < i∧i≤(ϑ j):= (show ∀ᶠ i:ℝ in 𝓝[>] (0:ℝ),0 < i from self_mem_nhdsWithin).and (eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (tide_price P F j))) -- same elaboration issue
 exact hx.mono fun t ⟨e,k⟩=> hL.trans (cellar_income P F C D x G g y j h e k)
#print axioms exit
#print axioms leaves
#check @tendency
end Anchovy
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
