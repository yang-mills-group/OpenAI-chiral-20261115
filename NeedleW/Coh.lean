import SatinHeatSpecies
import NeedleW.Grow
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
set_option maxHeartbeats 600000
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
variable (G:ℕ→ (P.ManyF 3 (P.otherSpectrum 3 3 x)).space)(g:∀ i,F ≤ i→PeriodS P F C D x i (G i))
local notation "z" j:max=>A₀ (G j)
local notation "τ" j:max=> (tidal P F j).toNNReal
variable (q:Fever P F C D x) -- in MiterT? #check
include g q
lemma unlocked{j:ℕ}(h:F ≤ j): z j≠ 0:=by
 let v:=q j h
 let u0:= v.choose; have hv:=v.choose_spec
 intro k
 have he:u0=G j:=tendsto_nhds_unique hv.1.1 (g j h).1
 let S:=Ψ; let L:= asset P x (A₀ u0)
 have hp':A₀ u0=0:=(congrArg (A₀) he).trans k
 have hp:FiniteDimensional ℂ L:=nilGraph (R:=H) S _ hp'
 exact hv.2 hp
where nilGraph{R:Hilbert}(S:OS.Semigroup R (3:Axis))(x:R)(v:x=0) : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun t:ℝ≥0=>S.E t x))):=by
       have h:(fun t:ℝ≥0=>S.E t x)=fun t=>0:=funext fun t=>by rw [v,map_zero]
       rw [h,Set.range_const]; exact Module.Finite.span_singleton _ _
omit q
-- backwards match heat
private lemma cease (w w':H)(k:Vantage)(u:U k w=U k w'):w=w':=eqAid (R:=H) _ (fun y=>P.cart_norm ..) w w' u
where eqAid{R:Hilbert}(p:R.Op)(h:∀y:R,‖p y‖=‖y‖)(w v:R)(e:p w=p v):w=v:=sub_eq_zero.mp (norm_eq_zero.mp (show ‖w-v‖=0 from by rw [←h,map_sub,e,sub_self,norm_zero]))
lemma parcelH{n k:ℕ}(q₀:F ≤ n)(q₁:F ≤ k)(e:τ n ≤ τ k): (Ψ).E ((τ k)-(τ n)) (z n)=z k:=by
 let t:=tidal P F k+1
 let v':Vantage:=fun _=>t
 have hτ(j:ℕ): ((τ j):ℝ)=tidal P F j:=Real.coe_toNNReal _ (tide_price P F j).le
 have h₂:tidal P F n ≤ tidal P F k:=by rw [← hτ n, ←hτ k]; exact_mod_cast e
 have hx:tidal P F k<v' 3:=lt_add_one _
 have ht: U (v'-crest P F) ((Ψ).E ((v' 3-tidal P F n).toNNReal) (G n))=U (v'-crest P F) ((Ψ).E ((v' 3-tidal P F k).toNNReal) (G k)):= ((g n q₀).2 v' (h₂.trans_lt hx)).symm.trans ((g k q₁).2 v' hx)
 have hu:= cease P F C D x G g _ _ _ ht -- ceil include variables? declaration cease includes g; F C D G etc
 let a:=(v' 3-tidal P F k).toNNReal; let b:=(v' 3-tidal P F n).toNNReal; let c:=(τ k)-(τ n); let T:=Ψ
 have he: b=a+c:=by
    apply NNReal.eq; unfold a b; rw [NNReal.coe_add,Real.coe_toNNReal _ (sub_nonneg.mpr (h₂.trans hx.le)),Real.coe_toNNReal _ (sub_nonneg.mpr hx.le)]; unfold c; rw [NNReal.coe_sub e,hτ,hτ]; ring -- unfold a b?
 have hv:T.E b (A₀ (G n))=T.E a (A₀ (G k)):= (keep_heat _ (P.stone_norm 3 ξ) T (P.heaven_hot 3 ξ) b (G n)).trans ((congrArg (A₀) hu).trans (keep_heat _ (P.stone_norm 3 ξ) T (P.heaven_hot 3 ξ) a (G k)).symm)
 let k':=DFunLike.congr_fun (T.time a c) (z n)
 exact T.heat_alive a ((k':T.E (a+c) (z n)= T.E a (T.E c (z n))).symm.trans ((congrArg (fun x:ℝ≥0=> T.E x (z n)) he.symm).trans hv))
#check @Fever
#check @cease
#check NNReal.coe_sub
#check Module.Finite.span_of_finite
#print axioms parcelH
#print axioms unlocked
end Anchovy
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
