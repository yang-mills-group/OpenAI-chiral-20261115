import SatinPP.Lady
import SatinPP.Cornice
import SatinThinJetsPurchase
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
local notation "D" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

open OS ConePrice
local notation "L"=> Θ
variable {H:Hilbert}
def oneBox (f g:ℒ→H)(A:H.Op):CrossRead:=Matrix.of fun i j=> inner ℂ (f i) (A (g j))

lemma posts_zero {m:ℒ→ℂ}(q:m≠0) :
 ∃ c:ℂ, fanSet (fun i=>c*m i):=by
 obtain ⟨i,u⟩:∃i,m i≠0:=not_forall.mp (fun p=>q (funext p))
 let a:=∑i,‖m i‖^2
 have h:0<a:=lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr u)) (Finset.single_le_sum (f:=fun i=>‖m i‖^2) (fun _ _=>sq_nonneg _) (Finset.mem_univ i))
 refine ⟨(√a:ℂ)⁻¹,?_⟩
 unfold fanSet
 simp_rw [norm_mul,mul_pow, norm_inv,Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt h.le]
 exact (Finset.mul_sum ..).symm.trans (inv_mul_cancel₀ h.ne')

lemma bellring(f g:ℒ→H)(A:H.Op)
 (h:∀m,fanSet m→inner ℂ (ounce m f) (A (ounce m g))≠0) :
 ReadsSix (oneBox f g A):=by
 constructor
 · intro t
   obtain ⟨v,v₀,w⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr t
   obtain ⟨c,p⟩:=posts_zero v₀
   let m:=fun i=>c*v i
   refine h m p ?_
   have a (i:ℒ):inner ℂ (f i) (A (ounce m g))= c*((oneBox f g A *ᵥ v) i):=by
      rw [ounce,map_sum,inner_sum]
      unfold Matrix.mulVec dotProduct
      rw [Finset.mul_sum]
      refine sum_congr rfl fun j _=>?_
      rw [map_smul,inner_smul_right]
      change c*v j*_ = c*((inner ℂ (f i) (A (g j)))*v j);ring
   rw [ounce,sum_inner]
   exact Finset.sum_eq_zero fun i _=>by rw [inner_smul_left,a,w,Pi.zero_apply,mul_zero,mul_zero]
 intro i
 let m:=fun j:ℒ=>if j=i then (1:ℂ) else 0
 have a(t:ℒ→H):ounce m t=t i:=by
   unfold ounce m;rw [sum_eq_single i,if_pos rfl,one_smul]
   · intro j _ u;rw [if_neg u,zero_smul]
   simp
 have p:=h m (by simp [fanSet,m,apply_ite norm,apply_ite (fun x:ℝ=>x^2)])
 rw [a,a] at p;exact p

variable (S:OS.Semigroup H 3)
local notation "Z"=> guards S
open Multiplier
lemma guard_proj:IsStarProjection (Z):=by
  refine ⟨show (Z).comp (Z)= (Z) from by rw [S.ℚmeasure.joins velvet_meas velvet_meas, Set.inter_self],S.ℚmeasure.real velvet_meas⟩

lemma overlap (v w:H)
 (h:dist v w < ‖Z v‖): inner ℂ v (Z w) ≠0:=by
 have u: Z=ContinuousLinearMap.adjoint Z := (S.ℚmeasure.real velvet_meas).symm
 have i: (Z).comp Z=Z:=(guard_proj S).1
 have g:= (norm_inner_le_norm (𝕜:=ℂ) (Z v) (v-w))
 have a : inner ℂ (Z v) v=inner ℂ (Z v) (Z v):=by
   conv_rhs => arg 3;rw [u]
   rw [ContinuousLinearMap.adjoint_inner_right,←ContinuousLinearMap.comp_apply,i]
 have b: inner ℂ (Z v) w=inner ℂ v (Z w):=by
   conv_lhs => rw [u]
   rw [ContinuousLinearMap.adjoint_inner_left]
 intro e
 rw [inner_sub_right,b,e,sub_zero,a,inner_self_eq_norm_sq_to_K,norm_pow,
    RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)] at g
 rw [dist_eq_norm] at h
 nlinarith [norm_nonneg (v-w)]

abbrev pennies(f:CrossRead):=f.det*(∏i:ℒ,f i i)
lemma pennies_iff(f:CrossRead): pennies f ≠0 ↔ ReadsSix f:=by
 change _*_ ≠0 ↔ _
 rw [mul_ne_zero_iff, Finset.prod_ne_zero_iff]
 simp only [mem_univ,true_implies, ReadsSix]

/-- Timelike intermediate spectral weighting, leaves spatial placements unchanged. -/
structure Feather (Q:H.Op):Prop where
  leaves :∃y:E4→ℂ, Registers (S.ℚmeasure) y Q ∧ ∀p,(0≤y p ∧ y p≤1) ∧ (p∉velvetSector→y p=0)
lemma incense_fan(f g:ℒ→H)(y:Cross 3)
 (h:∀ m,fanSet m→ dist (ounce m f) (S.U y (ounce m g)) < ‖Z (ounce m f)‖):
 ∃Q:H.Op, Feather S Q ∧ ReadsSix (oneBox f g Q) := by
 let A z:=oneBox f g (shade S y z)
 have tE: ReadsSix (A Complex.I):=by
   refine bellring _ _ _ ?_
   intro m p
   rw [shade_i,smul_apply,inner_smul_right]
   exact mul_ne_zero (by norm_num) (overlap S _ _ (h m p))

 have hAt(z:ℂ)(i j:ℒ):AnalyticAt ℂ (fun z=>A z i j) z :=by
    let F: H.Op→L[ℂ]ℂ:= (innerSL ℂ (f i)).comp (ContinuousLinearMap.apply ℂ H (g j))
    exact (show AnalyticAt ℂ F _ from ContinuousLinearMap.analyticAt F _).comp (shade_ana S y z)
 have a(z:ℂ):AnalyticAt ℂ (pennies ∘ A) z := by
    unfold pennies Function.comp
    simp_rw [Matrix.det_apply']
 
    fun_prop


 obtain ⟨s,k,v⟩ : ∃ s:ℝ, |s|<1 ∧ pennies (A s)≠0:=by
    by_contra! he
    have G' : ∃ᶠ z in 𝓝[≠] (0:ℂ), (pennies ∘ A) z =0 := by
       
       have y' : Tendsto Complex.ofReal (𝓝[>] (0:ℝ)) (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr
          ⟨Complex.ofReal_zero ▸ (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds),
           Eventually.mono self_mem_nhdsWithin fun r h=>
            show (r:ℂ) ≠0 from Complex.ofReal_ne_zero.mpr (show 0<r from h).ne'⟩
       apply y'.frequently
       exact (eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds (0:ℝ) (show 0<(1:ℝ) by norm_num))).frequently.mono fun x hx=>he x (by simpa using hx) -- better via tendsto_nhdsWithin with coe real.
    exact (pennies_iff _ |>.mpr tE)
       (AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (fun z (_:z∈(Set.univ:Set ℂ))=>a z) analyticOnNhd_const isPreconnected_univ (Set.mem_univ _) G' (Set.mem_univ _))
 refine ⟨_,⟨_, shade_pay S y s,shade_good y k⟩,(pennies_iff _).mp v⟩
#print axioms incense_fan
