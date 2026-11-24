import YM.SU5.SatinWard.Resolution.Cambrette
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.MeshClock
open Function Set Filter Metric Finset Asymptotics Topology
open scoped Topology NNReal
namespace Carousel
variable (M: Mesh) {α C:ℝ} {X I:Type*} [NormedAddCommGroup X][NormedSpace ℝ X][Fintype I][DecidableEq I][CompleteSpace X]
variable (p:0<α)(e:α<1) {f:(I→ℝ)→X} (K: Spark M (realLn M) C f α) (hc:Continuous f)
local notation "σ" v:max=> (mill M v:ℝ)
local notation "Λ"=> (M.L:ℝ)
local notation "σρ" i:max v:max=> realLn M i v
local notation "δ" i:max t:max=> axisLn i t
local notation "D" i:max => gradPrice (f:=f) M (realLn M) i
local notation "fee"=> C*gateLand M α
local notation "P"=> I→ℝ
variable (x y: I→ℝ) -- `y` duplicate. remove
local notation "Dx"=>Fintype.card I
-- linear map explicit.op norm with dimension factors. HasFDerivAt.W.Tx. can use for all older v.Leg budget.T.
noncomputable def fullD (x:I→ℝ) : (I→ℝ) →L[ℝ] X:= LinearMap.toContinuousLinearMap (show (I→ℝ) →ₗ[ℝ] X from {toFun u:=∑ i:I,u i • (D i) x,map_add' u v:= by simp [add_smul,sum_add_distrib], map_smul' a u:=by simp [Finset.smul_sum,mul_smul]}) -- linter complete instance needed? gradPrice no.
lemma cycles : fullD (f:=f) M x y=∑ i:I,y i • (gradPrice (f:=f) M (realLn M) i x):=rfl
lemma fullD_one(x:I→ℝ)(i:I) : fullD (f:=f) M x (axisLn i 1)=(D i) x:=by
 rw [cycles,sum_eq_single i] <;> simp_all [axisLn]
include p K
lemma fullD_cost (x:I→ℝ): ‖fullD (f:=f) M x‖ ≤ Fintype.card I*(C* expense M α):= by
 let V:=fullD (f:=f) M x; have h0:0≤ C*expense M α:=mul_nonneg K.pos (expense_pos M p).le; apply ContinuousLinearMap.opNorm_le_bound V (mul_nonneg (by positivity) h0); intro y; change ‖fullD (f:=f) M x y‖ ≤ _ -- f hidden
 rw [cycles]; refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun i:I=> ‖y‖* (C*expense M α)) (fun i _=>?_)) ?_)
 · rw [norm_smul]; exact mul_le_mul (norm_le_pi_norm y i) ((overhead M (realLn M) C p (realpaid M) K i x 0).1) (norm_nonneg _) (norm_nonneg _)
 simp only [sum_const,card_univ,nsmul_eq_mul]; exact le_of_eq (by ring)
include e hc
noncomputable abbrev unitToll (M:Mesh)(I:Type*)[Fintype I](α:ℝ):= gateLand M α*((Fintype.card I:ℝ)+2)*(Fintype.card I)
lemma fullD_vari : ‖fullD (f:=f) M x-fullD (f:=f) M y‖ ≤ Fintype.card I*(Fintype.card I*(C*gateLand M α)*‖x-y‖^α):=by
 let V:=fullD (f:=f) M; let t:= ‖x-y‖^α; let q:=Fintype.card I*(C*gateLand M α)*t; have ht:0≤ t:=Real.rpow_nonneg (norm_nonneg _) _; have hq:0 ≤ q:=by have hx:=K.pos; have hv:=land_nonneg M p e; unfold q; positivity
 apply ContinuousLinearMap.opNorm_le_bound (V x-V y) (mul_nonneg (by positivity) hq); intro z; let U(i):= (D i) x-(D i) y
 change ‖fullD (f:=f) M x z - fullD (f:=f) M y z‖≤_ -- ambiguous elabor
 rw [cycles,cycles]; simp_rw [←sum_sub_distrib, ←smul_sub]; refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun i:I=> ‖z‖*q) (fun i _=>?_)) ?_)
 · rw [norm_smul]; exact mul_le_mul (norm_le_pi_norm z i) (gather M p e K hc i x y) (norm_nonneg _) (norm_nonneg _)
 simp only [sum_const,card_univ,nsmul_eq_mul]; exact le_of_eq (by unfold q t; ring)
omit p e K hc in
private lemma downFrame (y:I→ℝ)(S:Finset I)(i:I): (∑ j∈S,axisLn j (y j)) i= if i∈S then y i else 0:=by

 rw [Finset.sum_apply]; by_cases h:i∈S
 · rw [if_pos h,sum_eq_single i]; · exact Pi.single_eq_same i _
   · intro j _ k; exact Pi.single_eq_of_ne (Ne.symm k) _
   simp [h]
 rw [if_neg h]; exact Finset.sum_eq_zero fun j v=>Pi.single_eq_of_ne (show i≠ j from (fun e=> h (e.symm ▸ v))) _

lemma frameTaylor : ‖f (x+y)-f x-fullD (f:=f) M x y‖ ≤ unitToll M I α*C*‖y‖*‖y‖^α:=by
 let A:=(fee); let g:= Dx*A*‖y‖^α; let B(a:Finset I):=∑ i∈a,axisLn i (y i); have hp(a:Finset I):‖B a‖≤‖y‖:=by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 (fun i=>?_); unfold B; rw [downFrame y a]; split; exact norm_le_pi_norm y i; simp
 let V:=(2+(Dx:ℝ))*A*‖y‖*‖y‖^α; have h₀:0≤ A:=mul_nonneg K.pos (land_nonneg M p e); let Q(a:Finset I):=∑ i∈ a,y i • (D i) x
 have ht(a:Finset I):‖f (x+B a)-f x-Q a‖≤ a.card*V:=by
    induction a using Finset.induction_on with
    | empty=> simp [B,Q]
    | insert i a v h=>
       let z:=x+B a; let w:= axisLn i (y i); let D0:=‖y‖; have hx:|y i| ≤ D0:= (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm y i); let Y:=D0^α; have h1:0≤Y:=Real.rpow_nonneg (norm_nonneg _) _; have hA:‖z-x‖≤D0:=by unfold z; rw [add_sub_cancel_left]; exact hp a
       let W:=‖f (z+w)- f z-y i • (D i) z‖; let W₁:=(D i) z-(D i) x
       have hv₁:W ≤ 2*A*D0*Y:=by refine (cadence M p e K hc i z (y i)).trans ?_; rw [mul_assoc 2]; exact mul_le_mul (mul_le_mul_of_nonneg_left hx (mul_nonneg zero_le_two h₀)) (Real.rpow_le_rpow (abs_nonneg _) hx p.le) (Real.rpow_nonneg (abs_nonneg _) _) (mul_nonneg (mul_nonneg zero_le_two h₀) (norm_nonneg _))
       have hq:‖y i • W₁‖ ≤ D0*g := by rw [norm_smul,Real.norm_eq_abs]; refine mul_le_mul hx ((gather M p e K hc i z x).trans ?_) (norm_nonneg _) (norm_nonneg _); exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hA p.le) (mul_nonneg (by positivity) h₀)
       rw [card_insert_of_notMem v,show x+B (insert i a)= z+w from (by unfold B z w; rw [Finset.sum_insert v]; dsimp only [B]; abel),show f (z+w)-f x-Q (insert i a)=(f (z+w)-f z-y i• (D i) z)+ y i • W₁ + (f z-f x-Q a) from (by unfold Q W₁; rw [sum_insert v]; module)]
       exact (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add hv₁ hq)) h).trans_eq (by unfold g Y V D0; push_cast; ring))
 nth_rw 1 [← show B univ=y from funext (fun i=>by unfold B; rw [downFrame y univ,if_pos (Finset.mem_univ _)])]
 rw [cycles]; exact (ht univ).trans_eq (by rw [Finset.card_univ]; unfold V A unitToll; ring) -- A inside V. unfold order
-- joint real Taylor and norm partial derivatives. HasFDerivAt from littleO directly.
lemma trulyReal (x:I→ℝ): HasFDerivAt f (fullD (f:=f) M x) x:=by
 rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
 intro c hc'
 have h: ContinuousAt (fun y:I→ℝ=> unitToll M I α*C*‖y‖^α) 0:= continuousAt_const.mul (ContinuousAt.rpow_const continuous_norm.continuousAt (Or.inr p.le))
 filter_upwards [h.tendsto.eventually (ge_mem_nhds (by simp [p.ne',hc'] : unitToll M I α*C*‖(0:I→ℝ)‖^α<c))] with y h
 refine (frameTaylor M p e K hc x y).trans ?_; change unitToll M I α*C*‖y‖^α≤ c at h; rw [mul_right_comm (unitToll M I α*C)]; exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
#print axioms trulyReal
end Carousel
end YM.CF.Buffered.Afterglow.Tower.MeshClock
