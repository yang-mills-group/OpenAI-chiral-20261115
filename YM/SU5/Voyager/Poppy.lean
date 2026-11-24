import YM.SU5.Voyager.Embers
import Mathlib.Analysis.Calculus.ParametricIntegral
/-! # Costs of harmonic analytic window. Phase as chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Caino
open Function Filter Set Metric NormedSpace Bornology Complex ContinuousLinearMap
open MeasureTheory Measure Boundary.Probe Boundary
open scoped NNReal ENNReal Topology InnerProductSpace ComplexConjugate ComplexOrder BigOperators
variable {X:Type*}[NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
variable (p w:X)(A:ℝ)(i:ℕ)
def lunar (w y:X):= (((inner ℝ w (-y)):ℝ):ℂ)*I
def comet (z:ℂ)(y:X):= plane p (-y)*cexp (z*lunar w y)
lemma comet_at (b:ℝ)(y:X): comet p w b y=plane (p+b • w) (-y):= by rw [comet,plane,plane,inner_add_left,real_inner_smul_left, ofReal_add,add_mul,Complex.exp_add,lunar]; push_cast; rw [mul_assoc ((b:ℝ):ℂ)]
local notation "H"=> rim (X:=X) A i
lemma rimNorm {x:X}(p:x∈rim (X:=X) A i): ‖x‖≤ A*i:= mem_closedBall_zero_iff.mp p
local notation "q"=> A*i
local notation "ξ"=> comet p w
private lemma cone_bound{z:ℂ}{b:ℝ}(v:‖z‖ ≤ b)(y:X)(e:y∈H): ‖ξ z y‖≤ Real.exp (b*‖w‖*q):=by
 have he:‖lunar w y‖ ≤ ‖w‖*q:=by simp only [lunar,norm_mul,Complex.norm_real,norm_I,mul_one]; have hu:= norm_inner_le_norm (𝕜:=ℝ) w (-y); exact hu.trans (mul_le_mul_of_nonneg_left ( (by simpa using rimNorm A i e): ‖-y‖≤q) (norm_nonneg _)) -- inner args tune
 rw [comet,norm_mul,plane_norm,one_mul,Complex.norm_exp]; apply Real.exp_le_exp.mpr; apply (Complex.re_le_norm _).trans; rw [norm_mul,mul_assoc]; exact mul_le_mul v he (norm_nonneg _) (by linarith [norm_nonneg z]) -- q notation precedence
variable (μ:ℕ→Measure X)[∀ n,IsFiniteMeasure (μ n)]
local notation "χ"=> charFun (μ i)
-- operator accountant pref fixed all grid
local notation "κ"=> ((pref X)⁻¹:ℝ)
def gesture (z:ℂ):= ((pref X:ℂ))⁻¹*∫ y in rim A i,(χ y*ξ z y)
local notation "f"=> gesture p w A i μ
local notation "N"=> Module.finrank ℝ X
private lemma smoothBound (h:0<A)(z:ℂ): DifferentiableAt ℂ f z:=by
 have hz:0≤q:=(by positivity); have hm:IsCompact H:=isCompact_closedBall ..; haveI : IsFiniteMeasure ((volume:Measure X).restrict H):= ⟨by simp [hm.measure_lt_top]⟩
 let F(z:ℂ)(y:X):=χ y * ξ z y; let F'(z:ℂ)(y:X):=F z y*lunar w y; let r:=‖z‖+1; let s:=closedBall (0:ℂ) r
 have hp':s∈𝓝 z:=mem_of_superset (isOpen_ball.mem_nhds (by exact mem_ball_zero_iff.mpr (lt_add_one _) : z∈ ball 0 r)) ball_subset_closedBall
 have hf(z x):HasDerivAt (fun t=>F t x) (F' z x) z:=by unfold F' F comet; convert ((((hasDerivAt_id z).mul_const (lunar w x)).cexp.const_mul (plane p (-x))).const_mul (χ x)) using 1 <;> first | rfl | simp [id_eq, mul_assoc]
 have hv(z): AEStronglyMeasurable (F z) (volume.restrict H):=by unfold F comet lunar plane; fun_prop
 let b:= (μ i).real Set.univ *Real.exp (r*‖w‖*q)
 have h' :0≤b:=by positivity
 have hg(z:ℂ)(h: z∈s): ∀ᵐ x∂(volume.restrict H), ‖F z x‖ ≤ b:=(ae_restrict_mem hm.measurableSet).mono fun x p'=> by unfold F; rw [norm_mul]; exact mul_le_mul (norm_charFun_le _) (cone_bound p w A i (mem_closedBall_zero_iff.mp h) x p') (norm_nonneg _) measureReal_nonneg
 have he:Integrable (F z) (volume.restrict H):=(integrable_const b).mono' (hv _) (hg z (mem_of_mem_nhds hp'))
 have hu: ∀ᵐ x∂(volume.restrict H), ∀ z∈s,‖F' z x‖≤ b*(‖w‖*q):=(ae_restrict_mem hm.measurableSet).mono fun x p'=>by
    intro z l; have u:‖F z x‖ ≤ b:=by unfold F; rw [norm_mul]; exact mul_le_mul (norm_charFun_le _) (cone_bound p w A i (mem_closedBall_zero_iff.mp l) x p') (norm_nonneg _) measureReal_nonneg
    unfold F'; rw [norm_mul]; apply mul_le_mul u _ (norm_nonneg _) h'; unfold lunar; simp only [norm_mul,Complex.norm_real,norm_I,mul_one]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (by simpa using rimNorm A i p') (norm_nonneg _))
 exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hp' (Eventually.of_forall hv) he (by unfold F' F comet lunar plane; fun_prop) hu (integrable_const _) (ae_of_all _ (fun x z _=> hf z x))).2.differentiableAt.const_mul _
variable {μ}
lemma flourishes (h:FlairC (fun n=> charFun (μ n)))(R:ℝ)(p':0<R)(g:0<A): ∃ C:ℝ,0<C∧ ∀ᶠ n:ℕ in atTop, Differentiable ℂ (gesture p w A n μ) ∧ ∀ z∈ closedBall (0:ℂ) R, ‖gesture p w A n μ z‖≤ C^n:=by
 obtain ⟨c,hc,t⟩:=h.localC; let b:= Real.exp (R*‖w‖*A); let Q:=(volume:Measure X).real (closedBall 0 1)
 have hb:0<c*b:=by positivity
 refine ⟨c*b+1,(by positivity),?_⟩; filter_upwards [t,blossoms hb (lt_add_one (c*b)) (κ*A^N*Q) N] with i t e; refine ⟨smoothBound p w A i μ g,fun z hz=>?_⟩
 unfold gesture; rw [norm_mul, norm_inv, Complex.norm_real,Real.norm_eq_abs, abs_of_pos prepos]
 have he : (volume:Measure X).real (rim A i)=(A*i)^N*Q:= addHaar_real_closedBall' _ _ (by positivity:A*i≥(0:ℝ))
 have hv(y:X)(u:y∈rim A i): ‖charFun (μ i) y*ξ z y‖≤ (c*b)^i:= by
    rw [norm_mul,mul_pow]; apply mul_le_mul (t _) ?_ (norm_nonneg _) (by positivity); apply (cone_bound p w A i (mem_closedBall_zero_iff.mp hz) y u).trans_eq; unfold b; rw [← Real.exp_nat_mul]; ring_nf
 have hw := norm_setIntegral_le_of_norm_le_const (s:=rim (X:=X) A i) (μ:=(volume:Measure X)) (C:=(c*b)^i) ((isCompact_closedBall ..).measure_lt_top) hv; rw [he] at hw
 refine (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr prepos.le)).trans ?_; apply le_trans _ e; exact Eq.le (by rw [mul_pow A]; ring)
lemma harvest_crops (h:FlairC (fun n=> charFun (μ n)))(c:ℝ)(p':0<c):∃ A:ℝ,0<A∧∀ᶠ i:ℕ in atTop, Integrable (charFun (μ i))∧ ∀ z:ℝ,‖gesture p w A i μ z - inverted (μ i) (p+z • w)‖ ≤ c^i:=by
 obtain ⟨A,hA,E⟩:= dustFare h (show 0<c/2 by positivity) (zero_lt_one); refine ⟨A,zero_lt_one.trans_le hA,?_⟩; filter_upwards [E,least (show 0<c/2 by positivity) (half_lt_self p') κ] with i ⟨hx,ht⟩ l; refine ⟨hx,fun z=>?_⟩
 let t(y:X):= charFun (μ i) y* ξ z y; have he(y:X): ξ z y=plane (p+z • w) (-y):=comet_at ..
 let S:Set X:= (rim A i); unfold gesture inverted; simp only [← Complex.ofReal_inv]; simp_rw [←he]; rw [Complex.real_smul, ← mul_sub]
 have hv(y):‖t y‖= ‖charFun (μ i) y‖:=by unfold t; rw [norm_mul,he,plane_norm,mul_one]
 have hg:Integrable t:=hx.norm.mono' (by unfold t comet lunar plane; fun_prop) (ae_of_all _ fun y=>Eq.le (hv y))
 have hy:(∫ y in S,t y)-(∫ y,t y)= -(∫ y in Sᶜ,t y):=by rw [← integral_add_compl (s:=S) measurableSet_closedBall hg]; abel
 change ‖(↑κ:ℂ)*((∫ y in S,t y)-∫ y,t y)‖≤_; rw [hy,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr prepos.le),norm_neg]; apply le_trans _ l; refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm ..).trans ?_) (inv_nonneg.mpr prepos.le); simp_rw [hv]; exact ht
end YM.Caino
#print axioms YM.Caino.flourishes
#print axioms YM.Caino.harvest_crops
