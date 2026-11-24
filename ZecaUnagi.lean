import ZecaEaglefin
import YM.SU5.Six.JointPM
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


/-- Band for outside-price. δ=q's pitch unit. qh required threshold. -/
def Off (δ E hq:ℝ)(d:E4):Set E4:=
 {p | δ * p 3 ≤ E ∧ hq≤‖plane p (δ • d)-1‖}

#check plane
lemma near_net {X:Type} [MeasurableSpace X] {P:PVM H X}
   {f:X→ℂ} {T:H.Op} (a:P.Represents f T)
   {A:Set X} (b:MeasurableSet A) {c:ℝ} (p:0≤c)
   (e: ∀x∈A, c≤‖f x‖) (v:H):
 c*‖P.region A v‖ ≤ ‖P.region A (T v)‖:=by
 -- Represent c*Proj
 have s:= (P.represents_indicator A b).smul (c:ℂ)
 have k:=a.indicator b
 -- positivity via squared norm cmp
 have j:= s.square.mono k.square v (Filter.Eventually.of_forall (fun y=>by
   dsimp only
   norm_cast
   by_cases t:y∈A
   · simp only [indicator_of_mem t,Pi.smul_apply,norm_smul,norm_one,mul_one,
       Real.norm_of_nonneg p]
     exact pow_le_pow_left₀ p (e y t) 2
   simp [t]))
 simp only [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K,
    _root_.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg p] at j
 exact le_of_sq_le_sq (by exact_mod_cast j) (norm_nonneg _)
#print axioms near_net
#check PVM

lemma Off_m(δ E l:ℝ)(d:E4):MeasurableSet (Off δ E l d) :=
  (isClosed_le (f:=fun p:E4=>δ*p 3) (g:=fun _=>E) (by fun_prop) continuous_const).measurableSet.inter
     (isClosed_le (f:=fun _=>l) (g:=fun p:E4=>‖plane p (δ•d)-1‖) continuous_const (by unfold plane; fun_prop)).measurableSet

lemma Off_bask{δ h E q:ℝ}{d:E4}
 (u:0≤δ)(a:0≤h*q):
 Bask h q E (S.unit.translation (δ•d)) (S.E δ.toNNReal)
    (fun x=>‖(Q).region (Off δ E (h*q) d) x‖):=by
 have k:=Off_m δ E (h*q) d
 constructor
 · intro x
   apply le_trans
    (((Q).represents_indicator _ k).norm_le zero_le_one x (ae_of_all _ fun y=>by
        by_cases i:y∈(Off δ E (h*q) d)<;> simp [i]))
   simp
 · intro v
   exact near_net ((rep_unit S _).sub (Q).represents_one) k a (fun p e=>e.2) v
 · intro v
   refine near_net (rep_heat S _) k (Real.exp_nonneg _) (fun y t=>?_ ) _
   rw [fade,Complex.norm_real]
   unfold tinct
   rw [Real.norm_of_nonneg (Real.exp_nonneg _),Real.coe_toNNReal _ u]
   exact Real.exp_le_exp.mpr (neg_le_neg t.1)
#print axioms Off_bask
