import Verts.DotFeed
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
local notation "Hp"=>P.ManyF 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "A₀"=>paster (Ω)
local notation "U"=>P.cartage 3 ξ
namespace Anchovy
open _root_.NeedleW
variable (J:P.Ellis 3 x)
open Habitat.Hemlock.AuroraB Verts _root_.Yoland _root_.NeedleW
open MeasureTheory
attribute [local instance] InnerProductSpace.complexToReal
variable (G:ℕ→ (P.ManyF 3 (P.otherSpectrum 3 3 x)).space)(g:∀ i,F ≤ i→PeriodS P F C D x i (G i))(n m:ℕ)
local notation "Y" z:max x':max=> ((z:ℝ):ℂ) • (x':(Hp))
local notation "N" i:max p:max=> zoomV x F C D i p
local notation "UQ" i:max p:max=> (fieldLimit x F C D i p)
-- hull sufficient even claimV clearance
variable (A B:SampleDose)(w:ℝ)(e:0 < w)(h:claimV w A)(b:claimV w B)
include g e h b
lemma gram_at : inner ℂ (UQ n A) (UQ m B)=∫ a:Vantage,∫ z':Vantage, ((A.val a:ℝ):ℂ)*((B.val z':ℝ):ℂ)*inner ℂ (N n a) (N m z'):=by
 let a(z:Vantage):=(A.val z:ℂ) • N n z; let f(z:Vantage):=(B.val z:ℂ) • N m z
 let H1:= ((eventually_ge_atTop F).and ((recessVanish P F).eventually (gt_mem_nhds e))).exists; let j:=H1.choose; have hp:=H1.choose_spec
 let v:= G j; have hv:=g j hp.1
 have ha:Integrable a:= integrationV x F C D j v hv A w h hp.2 n
 have hb:Integrable f:= integrationV x F C D j v hv B w b hp.2 m
 have he:inner ℂ (UQ n A) (UQ m B)=∫ i:Vantage,∫ j:Vantage,inner ℂ (a i) (f j):=dual (R:=Hp) a f ha hb
 refine he.trans (integral_congr_ae (Eventually.of_forall (fun i=>integral_congr_ae (Eventually.of_forall (fun z=>currency (R:=Hp) _ _ _ _)))))
where currency {R:Hilbert}(t r:ℝ)(x y:R):inner ℂ ((t:ℂ) • x) ((r:ℂ) • y)=(↑t:ℂ)*↑r*inner ℂ x y:=by rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]; ring
      dual{R:Hilbert}(p q:Vantage→R)(u:Integrable p)(v:Integrable q):inner ℂ (∫ i:Vantage,p i) (∫ i:Vantage,q i)=∫ i:Vantage,∫ j:Vantage,inner ℂ (p i) (q j):=by
        let p':=∫ i:Vantage,p i; let q':= ∫ i:Vantage,q i
        let L(x:R):R→L[ℝ]ℂ:= (innerSL ℂ x).restrictScalars ℝ
        have hg(i:R): inner ℂ i q'=∫ j:Vantage,inner ℂ i (q j):=(ContinuousLinearMap.integral_comp_comm (L i) v).symm
        let c:=Complex.conjCLE.toContinuousLinearMap
        let Q':=c.comp (L q')
        have H0(z:R):Q' z=inner ℂ z q':=inner_conj_symm (𝕜:=ℂ) z q'
        exact (H0 p').symm.trans ((ContinuousLinearMap.integral_comp_comm Q' u).symm.trans ((integral_congr_ae (Eventually.of_forall (fun i=> (H0 _).trans (hg _))))))
#print axioms gram_at
end Anchovy
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
