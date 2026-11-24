import SatinPP.Grenadier
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

variable {H:Hilbert}
def fanSet(m:ℒ→ℂ):Prop:=(∑ i,‖m i‖^2) =1
def ounce (m:ℒ→ℂ)(v:ℒ→H):H:= ∑ i,m i • v i
lemma ounces_map(m:ℒ→ℂ)(v:ℒ→H)(A:H.Op):ounce m (A ∘ v)=A (ounce m v):=by simp_rw [ounce,map_sum,map_smul,Function.comp_apply]
def Snug {I:Type}(f:I→ H) (b:ℝ):Prop:=∀ i, ‖f i‖ ≤ b
lemma mass_one' {m:ℒ→ℂ}(t:fanSet m)(i:ℒ):‖m i‖ ≤ 1:=
   by nlinarith only [show ‖m i‖^2≤1 from (Finset.single_le_sum (f:=fun j=>‖m j‖^2) (fun _ _=>sq_nonneg _) (Finset.mem_univ i)).trans_eq t]
lemma ounce_bound (m:ℒ→ℂ){v:ℒ→ H}(p:fanSet m) {d:ℝ}
   (h:Snug v d): ‖ounce m v‖ ≤ 6*d:=by
 have q i:‖m i • v i‖≤d:= by rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (mass_one' p i)).trans (h i)
 exact (norm_sum_le ..).trans ((Finset.sum_le_card_nsmul _ _ d (fun i _=>q i)).trans_eq (by rw [Finset.card_univ,show Fintype.card ℒ=6 from by decide,nsmul_eq_mul]; norm_num))

lemma postage {v:ℒ→ H}{a:ℝ}(p:∀ i j:ℒ, dist (inner ℂ (v i) (v j)) (shadowPay a i j)< 1/100)
    {m:ℒ→ℂ}(t:fanSet m): |(‖ounce m v‖^2-a)| ≤ 4/10:=by
 let W (f:ℒ→ℒ→ℂ):= ∑ i, ∑ j, star (m i)*(m j)* f i j
 let A:= shadowPay a
 let B:=fun i j=> inner ℂ (v i) (v j)
 have d: W A = a:=by
    have e: W A = ((∑ i:ℒ, (‖m i‖:ℝ)^2:ℝ):ℂ)*a:=by
       unfold W A shadowPay
       push_cast;rw [Finset.sum_mul]
       refine sum_congr rfl fun i _=>?_
       rw [sum_eq_single i]
       · rw [if_pos rfl, Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq];push_cast;rfl
       · intro j _ e;rw [if_neg e.symm,mul_zero]
       intro h;exact (h (Finset.mem_univ _)).elim
    unfold fanSet at t;rw [e,t,Complex.ofReal_one,one_mul]
 have r: W B = ((‖ounce m v‖:ℝ)^2:ℝ):= by
    rw [show (↑(‖ounce m v‖^2:ℝ):ℂ)= inner ℂ (ounce m v) (ounce m v) by simp [inner_self_eq_norm_sq_to_K]]
    unfold W B ounce; rw [sum_inner]; simp only [inner_sum,inner_smul_left,inner_smul_right, Complex.star_def,mul_assoc]
    exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>mul_left_comm ..
  
 have T i j:‖star (m i)*m j*B i j-star (m i)*m j*A i j‖≤ 1/100:=by
    rw [←mul_sub,norm_mul,norm_mul,norm_star]
    rw [←dist_eq_norm]
    exact (mul_le_of_le_one_left dist_nonneg (mul_le_one₀ (mass_one' t _) (norm_nonneg _) (mass_one' t _))).trans (p i j).le
 rw [←Real.norm_eq_abs,←Complex.norm_real,Complex.ofReal_sub,←r,←d]
 unfold W; rw [←sum_sub_distrib]; simp_rw [←sum_sub_distrib]
 have hcard: (univ:Finset ℒ).card=6:=by decide
 refine (norm_sum_le ..).trans ((sum_le_card_nsmul _ _ (6/100) (fun i _=> ?_)).trans ?_)
 swap
 · rw [hcard];norm_num
 exact (norm_sum_le ..).trans ((sum_le_card_nsmul _ _ _ (fun j _=>T i j)).trans (by rw [hcard];norm_num))


def toe (A:H.Op)(z:ℝ):H.Op:= (z:ℂ)⁻¹ • (ContinuousLinearMap.id ℂ H-A)
lemma toe_gram (A:H.Op)(z:ℝ)(p q:H):
 inner ℂ (toe A z p) (toe A z q)=(inner ℂ p q-inner ℂ (A p) q-inner ℂ p (A q) +inner ℂ (A p) (A q))/(z:ℂ)^2:=by
 unfold toe
 simp only [smul_apply, sub_apply, ContinuousLinearMap.id_apply, inner_smul_left,inner_smul_right, map_inv₀,Complex.conj_ofReal,inner_sub_left,inner_sub_right]
 ring
lemma toe_norm (A:H.Op) {z:ℝ}(e:0<z) (v:H): ‖toe A z v‖ = dist v (A v)/z:=by
 unfold toe;rw [smul_apply, norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos e,dist_eq_norm,div_eq_inv_mul]
 rfl
lemma lipschitz {A:H.Op}(p:‖A‖ ≤ 1)(v w:H):|dist v (A v)-dist w (A w)|≤ 2*dist v w:=by
 have e: dist (A v) (A w)≤dist v w:= by
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact (A.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) p)
 apply abs_le.mpr
 constructor <;> linarith only [e,dist_triangle w v (A w),dist_triangle v w (A v),dist_triangle v (A v) (A w),dist_triangle w (A w) (A v),dist_comm w v,dist_comm (A w) (A v)]


lemma whip {A:H.Op}{z:ℝ}(e:0<z){v:ℒ→H}
 (h:∀i j,dist (inner ℂ (toe A z (v i)) (toe A z (v j))) (shadowPay 72 i j)<1/100)
 {m:ℒ→ℂ}(p:fanSet m): (84/10)*z < dist (ounce m v) (A (ounce m v)):=by
 have t:= abs_le.mp (postage (v:=toe A z ∘ v) h p)|>.1
 rw [ounces_map] at t
 rw [←lt_div_iff₀ e,←toe_norm A e]
 nlinarith only [t,norm_nonneg (toe A z (ounce m v))]
def slack(j:Axis):ℝ:= if j=2 then 5 else 36/10
lemma slack_price(j:Axis):slack j ≤ 21/4:=by unfold slack;split_ifs<;>norm_num

lemma swish {A:H.Op}{z:ℝ}(e:0<z){v:ℒ→H}(j':Axis)
 (h:∀i j,dist (inner ℂ (toe A z (v i)) (toe A z (v j))) (shadowPay (sLeg j') i j)<1/100)
 {m:ℒ→ℂ}(p:fanSet m): dist (ounce m v) (A (ounce m v)) < (slack j'-1/20)*z:=by
 have t:= abs_le.mp (postage (v:=toe A z ∘ v) h p)|>.2
 rw [ounces_map] at t
 rw [←div_lt_iff₀ e,←toe_norm A e]
 have w:= norm_nonneg (toe A z (ounce m v))
 unfold slack
 unfold sLeg leg at t
 split_ifs at * <;> nlinarith only [t,w]

