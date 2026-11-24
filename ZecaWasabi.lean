import ZecaShoyu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 360000
noncomputable section
namespace YM.ZecaSky
open Function Filter Metric Set MeasureTheory Measure Spectral OS Semigroup Balloon Boundary Probe
open Six
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}(S:OS.Semigroup H timeAxis)
local notation "Q"=> S.ℚmeasure


open CF.Buffered.Afterglow.Hierarchy.Seld
open Zeca Poin
local notation "YPR"=>S.ℚmeasure.region

variable (Ω:Bench S) (D:Zeca.Moment H)
local notation "O"=>Ω.val
variable (h:saucer S Ω.val=Ω.val) (e:∀p,M S p Ω.val=Ω.val)
local notation "P" => parabola S D.n
variable (f:Test4)

lemma fresh_lower(δ E r T:ℝ)(d:E4)
 (p:0<δ)(t:0<T)(x:H):
 Real.exp (-(T*E)) * ‖YPR (Off δ E r d) x‖ ≤
   ‖YPR (Off δ E r d) ((S.E (δ*T).toNNReal) x)‖:=by
 refine near_net (rep_heat S _) (Off_m _ _ _ _) (Real.exp_nonneg _) (fun y m=>?_) x
 rw [fade,Complex.norm_real]; unfold tinct
 rw [Real.norm_of_nonneg (Real.exp_nonneg _),
       Real.coe_toNNReal _ ((mul_pos p t).le)]
 exact Real.exp_le_exp.mpr (neg_le_neg
    ((le_of_eq (show (δ*T)*(y timeAxis) = T*(δ*y timeAxis) by ring)).trans
     (mul_le_mul_of_nonneg_left m.1 t.le)))

include h e
lemma wasabi
 {δ E r T η:ℝ}{d:E4}
 (p:0<δ)(t:0<T)
 {z:ℂ} {y:Cross timeAxis}
 (j:‖YPR (Off δ E r d)
    (S.U y (z•P (duration (δ*T).toNNReal) (D.op O)))‖ ≤ η * Real.exp (-(T*E))):
 ‖YPR (Off δ E r d) (z•awake S Ω D f)‖ ≤ η * ∫x, ‖f x‖:=by
 let A:=Off δ E r d
 have b:MeasurableSet A:=Off_m ..
 change ‖YPR A (S.U y _)‖ ≤ _ at j
 rw [← ContinuousLinearMap.comp_apply,show (YPR A).comp _=(S.U y).comp (YPR A) from ((rep_space S y).comm_region b).symm,
      ContinuousLinearMap.comp_apply, S.unitary] at j
 refine le_of_mul_le_mul_left ?_ (Real.exp_pos (-(T*E)))
 refine (le_trans (fresh_lower S δ E r T d p t _) ?_)
 refine le_trans (shoyu S Ω D h e f A b z _ (Real.toNNReal_pos.mpr (mul_pos p t))) ?_
 have a:0 ≤ ∫ x,‖f x‖:=integral_nonneg (fun _=>norm_nonneg _)
 refine (mul_le_mul_of_nonneg_left j a).trans (le_of_eq ?_)
 ring
#print axioms wasabi
#check @shoyu
