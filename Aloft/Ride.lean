import Aloft.Drive
import Aloft.Frugal
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 500000
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
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
namespace Aloft
open Py.Dyad Keeping Py.Rate.Pitching.Focus
open _root_.YM.Preen
variable (x:P.Spectrum0 3)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "Ψ"=> P.seasons 3 ξ
local notation "H"=>P.ManyF 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "A₀"=>paster (Ω)
local notation "U"=>P.cartage 3 ξ
local notation "sQ" d:max=> stackW d
local notation "gL" d:max=> ((girder P d):ℝ)
variable (J:P.Ellis 3 x)(d m:ℕ)(o:Cover)(q:Enrolled P d (stairW d) o)(g:1 ≤ m)
include g
lemma bootV(i:Axis): spindle P d (stairW d) i ≤ bootH P m d i :=by
 unfold bootH; split_ifs with he
 · subst i; apply le_mul_of_one_le_left (spin_k (P:=P) _).1; exact_mod_cast ‹1 ≤ m› -- not included
 exact le_rfl
include q
lemma gap_duration: nhot P d m o = ((spotL P d m) 3).toNNReal:=by
 let j0:=3; let x:= (spotL P d m) (3:Axis); let b:=heatU P (sQ d) o; let v:= (fitting P (sQ d) o).realWidth P 3
 have he:(b:ℝ)=v:=heatU_correct ..
 let a:ℕ:=beamU P o 3
 have hf : (a:ℤ)+(a:ℤ) ≤ bootH P m d (3:Axis):= by
    have hy:=ribbon_ms P q 3; rw [Pi.zero_apply,sub_zero] at hy; exact hy.le.trans (bootV P d m g _)
 have hv :v+v ≤x:=by
    unfold x spotL; rw [Pi.sub_apply,P.gridSpot_mul,P.gridSpot_mul,Pi.zero_apply,Int.cast_zero,zero_mul,sub_zero]
    have hp:v= (a:ℝ)*P.spotMesh (sQ d):= by unfold v a spotMesh Apron.realWidth; norm_cast
    rw [hp,← add_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hf) (P.spotMesh_pos _|>.le)
 have hg:0≤v:= he ▸ NNReal.coe_nonneg _
 apply NNReal.eq; unfold nhot; change ((b+((x-(v+v)).toNNReal + b):ℝ≥0):ℝ)=(↑(x.toNNReal):ℝ); simp only [NNReal.coe_add,he,Real.coe_toNNReal _ (sub_nonneg.mpr hv),Real.coe_toNNReal _ ((add_nonneg hg hg).trans hv)]; linarith
include J
lemma evo {a z:H}{r:Vantage}(p:U r z=a)(h:a=amber P x 0 (sQ d) o q.clock.1) : gem P d m x o = inner ℂ z (terrain P x d m o z):=by
 let f:= terrain P x d m o
 have he: f a=U r (f z):=by
    let i:=nhot P d m o; let v:= spotL P d m
    have hv(a b:Vantage)(y:H): U a (U b y)=U b (U a y):=by
       have hf:= DFunLike.congr_fun (P.cart_paves 3 ξ a b).symm y
       exact Eq.trans hf ((congrArg (fun q:Vantage=> (P.cartage 3 ξ q) y) (add_comm a b)).trans (DFunLike.congr_fun (P.cart_paves 3 ξ b a) y))
    change (Ψ).E _ (U v a)= _
    exact (congrArg (fun k:(H)=> (Ψ).E i k) ((congrArg (U v) p.symm).trans (hv v r z))).trans (P.warm_drive 3 ξ r i (U v z))
 exact (portal_next P x o J d m q g a h).trans ((congrArg₂ (fun p q':H=>inner ℂ p q') p.symm he).trans (P.inner_pay 3 ξ r z (f z)))
omit J q
variable {Y:ℕ→ℕ}(Yt:Tendsto Y atTop atTop)(o':ℕ→ Cover)(qt:∀i,Enrolled P (Y i) (stairW (Y i)) (o' i))
lemma rideTx(i:ℕ): ‖terrain P x (Y i) m (o' i)‖ ≤ 1:= (ContinuousLinearMap.opNorm_comp_le ((Ψ).E _) (U _)).trans (mul_le_one₀ ((Ψ).shrinks _) (norm_nonneg _) (P.cart_pay ..))
include Yt qt
lemma riding (z:H): Tendsto (fun i:ℕ=> (terrain P x (Y i) m (o' i)) z) atTop (𝓝 z):=by
 let b(i):=nhot P (Y i) m (o' i); let k(i):= spotL P (Y i) m
 have hf:Tendsto k atTop (𝓝 0):=(portal_small P m).comp Yt
 have hs:Tendsto b atTop (𝓝 0):=by unfold b; simp_rw [gap_duration P _ _ _ (qt _) g]; have hx:= (continuous_real_toNNReal.comp (continuous_apply (A:=fun _:Axis=>ℝ) 3)).continuousAt.tendsto.comp hf; simpa only [Function.comp_def,Pi.zero_apply,Real.toNNReal_zero] using hx -- name X tune
 let sxt(i):=(Ψ).E (b i); have hw(i): ‖sxt i‖ ≤1:=(Ψ).shrinks _
 let f(i):=U (k i) z
 have hu:Tendsto f atTop (𝓝 z):= by
    have ht:((P.cartage 3 ξ 0) z)=z:= DFunLike.congr_fun (P.cart_zero 3 ξ) z
    have he : Tendsto f atTop (𝓝 ((P.cartage 3 ξ 0) z)):= (P.cart_cont 3 ξ z).continuousAt.tendsto.comp hf
    exact hmeli (R:=(H)) ht he
 have hy:Tendsto (fun i=> sxt i z) atTop (𝓝 z):= by
    have ht:((Ψ).E 0 z)=z:=DFunLike.congr_fun ((Ψ).eZero) z
    exact hmeli (R:=(H)) ht (show Tendsto (fun i=>sxt i z) atTop (𝓝 ((Ψ).E 0 z)) from ((Ψ).continuousE z).continuousAt.tendsto.comp hs)
 exact bike (R:=H) sxt f z hw hu hy
where
 hmeli {R:Hilbert}{a b:R}{f:ℕ→R}(h:a=b)(t:Tendsto f atTop (𝓝 a)): Tendsto f atTop (𝓝 b):=h ▸ t
 bike {R:Hilbert}(S:ℕ→R.Op)(f:ℕ→R)(z:R)(hw:∀i,‖S i‖≤1)(hu:Tendsto f atTop (𝓝 z))(hy:Tendsto (fun i=>S i z) atTop (𝓝 z)): Tendsto (fun i=>S i (f i)) atTop (𝓝 z):=by
  have he:Tendsto (fun i=> S i (f i)-S i z) atTop (𝓝 (0:R)):=by
     rw [tendsto_zero_iff_norm_tendsto_zero]
     apply squeeze_zero (fun _=> norm_nonneg _) (g:=fun i=>‖f i-z‖) (fun i=>?_ )
     · simpa only [sub_self,norm_zero] using (hu.sub_const z).norm
     rw [← map_sub]; exact ((S i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hw i))
  simpa only [zero_add,sub_add_cancel] using he.add hy
#print axioms gap_duration
#print axioms riding
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
