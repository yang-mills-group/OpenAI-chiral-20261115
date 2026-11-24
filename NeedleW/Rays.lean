import Verts.Dot
import NeedleW.Coh
import NeedleW.Typhon
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
set_option maxHeartbeats 360000
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
open _root_.Yoland
attribute [local instance] InnerProductSpace.complexToReal
variable (G:ℕ→ (P.ManyF 3 (P.otherSpectrum 3 3 x)).space)(g:∀ i,F ≤ i→PeriodS P F C D x i (G i))
local notation "τ" j:max=> (tidal P F j).toNNReal
local notation "ϑ" j:max=> tidal P F j
local notation "z" j:max=>A₀ (G j)
local notation "Q"=>pointT P F C D ξ
local notation "N" i:max p:max=>zoomV x F C D i p
local notation "isp" v:max=>aislePt (3:Axis) v
variable (y:Vantage)
abbrev textQ (t:ℝ):H:= Q (y+isp (t-y 3))
local notation "R"=>textQ P F C D x y
include g
lemma jet (i:ℕ)(t:ℝ):iteratedDeriv i (R) t=N i (y+isp (t-y 3)):=by
 let t₀:=y+isp (t-y 3)
 unfold zoomV
 have he(r:ℝ):t₀+(isp r)=y+isp ((t+r)-y 3):=by
    ext a; unfold t₀; simp only [Pi.add_apply,location]; split_ifs<;>ring
 exact (show iteratedDeriv i (R) t=iteratedDeriv i (fun r:ℝ=>R (t+r)) 0 from by simp only [iteratedDeriv_comp_const_add,add_zero]).trans (congrArg (fun p:ℝ→H=>iteratedDeriv i p 0) (funext fun r=>congrArg (Q) (he r).symm))
variable {j:ℕ}(e:F ≤ j)
local notation "TZ"=>U (y-crest P F)
local notation "Jj" i:max t:max=> _root_.Yoland.pay (Ψ) i t
include e
lemma beaconR(i:ℕ){t:ℝ}(q:ϑ j<t):iteratedDeriv i (R) t= (TZ) ((Jj i (t- ϑ j)) (G j)):=by
 let p:=y+isp (t-y 3)
 have he:p 3=t:=by unfold p; rw [Pi.add_apply,location₁]; ring
 have ht:U (p-crest P F)= TZ:= by
    rw [show (p-crest P F)=(y-crest P F)+isp (t-y 3) from by unfold p; ext; simp only [Pi.sub_apply,Pi.add_apply]; ring]
    exact caesium x _ _
 exact (jet P F C D x G g y i t).trans ((dot_port x F C D j (G j) (g j e) i p (q.trans_le (le_of_eq he.symm))).trans (congrArg₂ (fun (f:(H).Op) (t:ℝ)=> f ((Jj i (t-ϑ j)) (G j))) ht he))
omit e
lemma mate (i:ℕ){t:ℝ}(q:0<t):AnalyticAt ℝ (iteratedDeriv i (R)) t:=by
 suffices h:AnalyticOnNhd ℝ (R) (Ioi 0) from aoe h _ q
 intro s a
 have hr:= ((eventually_ge_atTop F).and ((recessVanish P F).eventually (gt_mem_nhds a))).exists
 let j:=hr.choose; have hj:= hr.choose_spec
 let f(r:ℝ):=(r-ϑ j)
 let T:= dawn (Ψ)
 let op:= (TZ).comp (ContinuousLinearMap.apply ℂ _ (G j))
 let hA(r:ℝ):= (TZ) (T (f r) (G j))
 have he:R =ᶠ[𝓝 s] hA:=by
    refine (lt_mem_nhds hj.2).mono fun r g₀=>?_ -- z timeline
    simpa only [iteratedDeriv_zero,_root_.Yoland.pay] using beaconR P F C D x G g y hj.1 0 g₀
 have hD:AnalyticAt ℝ (op.restrictScalars ℝ) (T (f s)):= (op.restrictScalars ℝ).analyticAt _
 exact (hD.comp (f:=T ∘ f) ((dawnRise (Ψ) _ (sub_pos.mpr hj.2)).comp (f:=fun r:ℝ=>r-ϑ j) (analyticAt_id.sub analyticAt_const))).congr he.symm
lemma ferryN(i:ℕ)(t w:ℝ)(q:0<t)(l:t<w): dawn (Ψ) (w-t) (iteratedDeriv i (R) t)=iteratedDeriv i (R) w :=by
 let e':= ((eventually_ge_atTop F).and ((recessVanish P F).eventually (gt_mem_nhds q))).exists
 let j:=e'.choose; have p:= e'.choose_spec
 let hT:=TZ; let S:=Ψ; let q0:=(w-t).toNNReal
 let u:=t-ϑ j; let v':=w-t
 have h₀: 0<u:=sub_pos.mpr p.2; have ht: 0<v':=sub_pos.mpr l
 have hp:=P.warm_drive 3 ξ (y-crest P F) q0 ((Jj i u) (G j))
 -- transport z
 exact (Eq.trans (congrArg (fun k:H=>dawn S v' k) (beaconR P F C D x G g y p.1 i p.2)) hp).trans ((congrArg hT (cash (G:=(H)) S _ i h₀ ht)).trans ((congrArg (fun v'':ℝ=> hT ((Jj i v'') (G j))) (show u+v'=w-ϑ j from by unfold u v'; ring)).trans (beaconR P F C D x G g y p.1 i (p.2.trans l)).symm))
where cash{G:Hilbert}(S:OS.Semigroup G (3:Axis))(x:G)(i:ℕ){u v':ℝ}(h:0<u)(t:0<v') : dawn S v' (_root_.Yoland.pay S i u x)=_root_.Yoland.pay S i (u+v') x:=by
        have he:=DFunLike.congr_fun (earns_asset S i 0 u v' h t) x
        simpa only [_root_.Yoland.pay,iteratedDeriv_zero,zero_add,ContinuousLinearMap.comp_apply] using he
#check AnalyticAt.congr
#print axioms ferryN
#print axioms mate
end Anchovy
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
