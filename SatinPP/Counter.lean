import SatinPP.Bolts
import SatinPP.Dahlia
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

open TopologicalSpace SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Γ"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth 3 ξ
local notation "D%" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

open DoseTravel Set

/-! # Rights to smooth pressure, at fixed and smaller moves -/
def dials (b:Bool)(p:Vantage):ℝ:= if b then p 3 else -(p 3)
def morning(b:Bool)(q:ℝ)(p:Vantage):=max q (dials b p)
lemma good_hours (b:Bool)(q:ℝ):Continuous (morning b q):=
 continuous_const.max (by cases b;exact (continuous_apply _).neg; exact continuous_apply _)
lemma good_face (b:Bool)(a p:Vantage):|dials b p - dials b a| ≤ dist p a:=by
 have h: |p 3-a 3| ≤ dist p a:=(Real.dist_eq ..|>.symm).trans_le (dist_le_pi_dist ..)
 cases b
 · simp only [dials, Bool.false_eq_true,↓reduceIte, sub_neg_eq_add] -- tune
   rw [show -(p 3) + a 3=a 3-p 3 by ring,abs_sub_comm]
   exact h
 exact h


lemma dose_int (F:SampleDose): Integrable F.val:= F.smooth.continuous.integrable_of_hasCompactSupport F.budget
section
variable {X:Hilbert}(u:Vantage→X)(F:SampleDose)(e:Continuous u)
lemma beam_int (g:Continuous u): Integrable (fun p=>(F.val p :ℂ) • u p):=by
 simp_rw [Complex.coe_smul]
 exact (F.smooth.continuous.smul g).integrable_of_hasCompactSupport F.budget.smul_right
/-- norm estimate with arbitrary fixed target incl zero -/
lemma stern {f:Vantage→X} {L:ℝ}(v:F.Normalized)
 (w:∀p:Vantage,‖f p‖≤L*F.val p): ‖∫p,f p‖≤L:=by
 exact (norm_integral_le_of_norm_le ((dose_int F).const_mul L)
    (Eventually.of_forall w)).trans (by rw [integral_const_mul,v.2,mul_one])

include e
lemma bead (a:F.Normalized)(c:X){L:ℝ}(g:∀p∈tsupport F.val,dist (u p) c≤L):dist (DoseTravel.beam X F u) c ≤ L:=by
 have h:(∫p,(F.val p:ℂ) • c)=c:=by simp_rw [Complex.coe_smul];rw [integral_smul_const,a.2,one_smul]
 rw [dist_eq_norm,DoseTravel.beam,←show (∫p,(F.val p:ℂ) • c) =c from h,←integral_sub (beam_int u F e) (beam_int _ F continuous_const)]
 refine stern F a (fun p=>?_);rw [←smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs]

 rw [←dist_eq_norm,abs_of_nonneg (a.1 p), mul_comm (F.val p)]
 by_cases z:F.val p=0; · rw [z,mul_zero,mul_zero]
 exact mul_le_mul_of_nonneg_right (g p (subset_closure z)) (a.1 p)

lemma bead_move (a:F.Normalized)(U:X.Op){L:ℝ}(g:∀p,dist (u p) (U (u p))≤L):
 dist (DoseTravel.beam X F u) (U (DoseTravel.beam X F u)) ≤L:=by
 have h:=beam_int u F e
 rw [dist_eq_norm,DoseTravel.beam,←U.integral_comp_comm h,←integral_sub h (U.integrable_comp h)]
 exact stern F a fun p=>by
    rw [map_smul,←smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs,←dist_eq_norm,abs_of_nonneg (a.1 p),mul_comm (F.val p)]
    exact mul_le_mul_of_nonneg_right (g _) (a.1 _)
end

lemma pull_beam_ounce (Y:ℒ→Vantage→G)(c:∀a,Continuous (Y a))
 (F:SampleDose)(m:ℒ→ℂ):
 ounce m (fun a=>DoseTravel.beam (G) F (Y a))=DoseTravel.beam (G) F (fun p=>ounce m fun a=>Y a p):=by
 simp_rw [DoseTravel.beam,ounce,smul_sum]
 rw [integral_finsetSum]
 · apply sum_congr rfl; intro a _
   rw [←integral_smul]
   exact integral_congr_ae (Eventually.of_forall fun p:Vantage=>by dsimp only;rw [smul_smul,smul_smul,mul_comm])
 exact fun a _=>beam_int (fun t=>m a • Y a t) F ((continuous_const (y:=m a)).smul (c a))

lemma cycle_beam (Y:Vantage→G)(c:Continuous Y)(F:SampleDose)(j:Vantage)
 (h:ℝ)(w:∀p,Γ (h • j) (Y (p-h • j))=Y p):
 DoseTravel.beam (G) (bike j F h) Y=
 h⁻¹ • (DoseTravel.beam (G) F Y - Γ (h • j) (DoseTravel.beam (G) F Y)):=by
 let A:=Γ (h • j)
 let k:= DoseTravel.beam (G) F Y
 let e(p):= (F.val p:ℂ) • (A (Y p))
 have b:=beam_int Y F c
 have z:=beam_int _ F (A.continuous.comp c)
 have t:(∫ p,e (p-h • j))= A k:=by
    rw [integral_sub_right_eq_self]
    unfold k DoseTravel.beam
    rw [←A.integral_comp_comm b];simp_rw [map_smul];rfl
 have g:Integrable (fun p=>e (p-h • j)):= ?_
 change _= h⁻¹ • (_ - A k)
 rw [←t, DoseTravel.beam,DoseTravel.beam,←integral_sub b g, ←integral_smul]
 refine integral_congr_ae (Eventually.of_forall fun p=>?_)

 · change (nick j h p F:ℂ) • Y p = h⁻¹ • ((F.val p:ℂ) • Y p - (F.val (p-h • j):ℂ) • Γ (h • j) (Y (p-h • j)))
   simp_rw [Complex.coe_smul,w,←sub_smul]
   rw [smul_smul, ←div_eq_inv_mul]
 exact z.comp_sub_right _

lemma weigh_beams (Y:Vantage→G)(c:Continuous Y)(F F' U:SampleDose)(u:U.Normalized)
    {M B:ℝ}(c₁:∀p,‖Y p‖≤M)(c₂:∀p,|F.val p-F'.val p|≤B*U.val p):
 dist (DoseTravel.beam (G) F Y) (DoseTravel.beam (G) F' Y) ≤ B*M:=by
 rw [dist_eq_norm,DoseTravel.beam,DoseTravel.beam,←integral_sub (beam_int _ _ c) (beam_int _ _ c)]
 refine stern U u fun p=>?_
 rw [←sub_smul,norm_smul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,mul_right_comm]
 exact mul_le_mul (c₂ _) (c₁ _) (norm_nonneg _) ((abs_nonneg _).trans (c₂ _))
