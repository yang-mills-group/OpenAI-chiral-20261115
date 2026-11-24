import GaugeFieldConstruction.Scone
/- Differentiating gaussian weighted moments -/
set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
namespace YM.Gleam.Guide
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian CF
open Fineness Matrix Module Regis Regis.Head ProbabilityTheory Hood
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal InnerProductSpace
namespace Prims
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
local notation "J" => StrongDual ℝ E
abbrev rub(x y:E):ℝ:=inner ℝ x y
abbrev dais (W:List E)(x:E):= factorV W (rub · x)
def lipW(A:E)(L:List E)(x:E):= Real.exp (rub A x) * dais L x
lemma linc(A:E)(L:List E) : Continuous (lipW A L):=by
 apply Continuous.mul ((continuous_const.inner continuous_id').rexp)
 induction L with |nil=>exact continuous_const|cons v l ih=> exact (continuous_const.inner continuous_id').mul ih
def grimes (L:List E)(x:E):= Real.exp ((L.map fun i=> |rub i x|).sum)
lemma bar_mg (L:List E): Integrable (grimes L) (stdGaussian E):=by
 let u:=InnerProductSpace.toDual ℝ E; let X:=L.map (u ·); have he:grimes L=horus 0 X 1:=by funext i; unfold grimes horus X; simp [List.map_map,comp_def,u, rub,real_inner_comm i]
 rw [he]; let C:ℝ:=∑ i∈X.toFinset,‖i‖
 exact (dome_v C (Finset.sum_nonneg fun _ _=>norm_nonneg _) X (fun i h=> single_le_sum (f:=fun i:J=>‖i‖) (fun _ _=>norm_nonneg _) (List.mem_toFinset.mpr h)) (le_refl _) 1 zero_le_one).1
lemma dais_abs (L:List E)(x:E): |dais L x|≤ grimes L x:=by
 induction L with
 | nil=> simp [dais,factorV,grimes]
 | cons i l ih=>
   rw [show dais (i::l) x=rub i x*dais l x from rfl,abs_mul]; apply (mul_le_mul ((by linarith: |rub i x|≤ |rub i x|+1)|>.trans (Real.add_one_le_exp _)) ih (abs_nonneg _) (Real.exp_pos _|>.le)).trans; exact le_of_eq (by simp [grimes,Real.exp_add])
def arch (A y:E)(t:ℝ):= A+t • y
lemma line_pay (A y:E)(L:List E)(x:E)(s:ℝ)(p: |s| ≤ 1) : ‖lipW (arch A y s) L x‖ ≤ grimes (A::y::L) x:=by
 let i:=rub y x; have he: rub (arch A y s) x=rub A x +s*i:=by simp [arch,rub,i,inner_add_left,real_inner_smul_left];
 unfold lipW; rw [norm_mul, he,Real.norm_of_nonneg (Real.exp_pos _|>.le)]
 refine (mul_le_mul (b:=Real.exp (|rub A x|+|i|)) (d:=grimes L x) (Real.exp_monotone ?_) (dais_abs ..) (abs_nonneg _) (Real.exp_pos _|>.le)).trans_eq (by simp [grimes,i,add_assoc,Real.exp_add,mul_assoc])
 exact add_le_add (le_abs_self _) ((le_abs_self _).trans ((abs_mul s i).le.trans (mul_le_of_le_one_left (abs_nonneg _) p)))
lemma arch_at (A y:E): arch A y 0=A:=by simp [arch]
lemma lip_int (A:E)(L:List E): Integrable (lipW A L) (stdGaussian E):=by
 refine (bar_mg (A::A::L)).mono' (linc A L).aestronglyMeasurable (Eventually.of_forall fun x=>?_); rw [← show arch A A 0=A from arch_at ..] -- rewrites RHS too tune
 simpa only [arch_at] using line_pay A A L x 0 (by norm_num)
abbrev χfund (A:E)(L: List E):ℝ:=∫ x,lipW A L x∂stdGaussian E
lemma fund_Q (A y:E)(L:List E): HasDerivAt (fun t=>χfund (arch A y t) L) (χfund A (y::L)) 0:=by
 let Q:= Metric.ball (0:ℝ) 1; let P(t:ℝ)(x:E):= lipW (arch A y t) L x; let F(t:ℝ)(x:E):= lipW (arch A y t) (y::L) x
 have hx(t:ℝ)(x:E): HasDerivAt (P · x) (F t x) t:=by
    have he(s:ℝ):rub (arch A y s) x=rub A x+s*rub y x:=by simp [arch,rub,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
    unfold P F lipW; simp_rw [he]; rw [show dais (y::L) _=rub y x*dais L x from rfl]; convert (((hasDerivAt_const t (rub A x)).add ((hasDerivAt_id' t).mul_const (rub y x))).exp.mul_const
     (dais L x)) using 1 <;> first|rfl|simp [mul_assoc]
 have he:= (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=P) (μ:=stdGaussian E) (F':=F) (bound:=grimes (A::y::y::L)) (Metric.ball_mem_nhds (0:ℝ) one_pos) (Eventually.of_forall fun x=> (lip_int (arch A y x) L).aestronglyMeasurable) (lip_int (arch A y 0) L) (linc (arch A y 0) _|>.aestronglyMeasurable) (Eventually.of_forall fun i t p=> line_pay A y (y::L) i t (by simpa [Real.dist_eq] using (show _ from (Metric.mem_ball.mp p).le))) (bar_mg (A::y::y::L)) (Eventually.of_forall fun i t _=> hx t i)).2
 change HasDerivAt (fun t=>χfund (arch A y t) L) (χfund (arch A y 0) _) 0 at he; rwa [arch_at] at he
-- Wick recursive without removals list: accumulate front for differentiation.
def charm (j:E)(X Y:List E)(A:E):ℝ:= match Y with
| [] => 0
| i::Y => rub j i * χfund A (X++Y)+charm j (X++[i]) Y A
lemma arch_rub (A y j:E)(t:ℝ):rub j (arch A y t)=rub j A+t*rub j y:=by simp [arch,rub,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
lemma deriv_charm (A y j:E)(X Y:List E) : HasDerivAt (fun t=>charm j X Y (arch A y t)) (charm j (y::X) Y A) 0:=by
 induction Y generalizing X with
 | nil=> exact hasDerivAt_const _ _
 | cons i L ih=>
    rw [charm]; exact ((fund_Q A y (X++L)).const_mul (rub j i)).add (ih (X:=X++[i])) -- tune
lemma grantZ (A:E): χfund A []= Real.exp (‖A‖^2/2):=by
 let F:= InnerProductSpace.toDual ℝ E; have hx:= Regis.exp_linear 1 (F A) -- tune order
 change _=_; unfold χfund lipW; change (∫ x, (Real.exp (rub A x)) * 1 ∂stdGaussian E)=_; simp_rw [mul_one]
 simpa [mgf,F,rub] using hx
lemma stitch (L:List E)(A j:E): χfund A (j::L) = rub j A * χfund A L+charm j [] L A:=by
 induction L generalizing A with
 | nil=>
   let Y:=fun s:ℝ=> (χfund (arch A j s) []); rw [charm,add_zero,grantZ]; have h:= fund_Q A j ([]: List E)
   simp_rw [grantZ] at h; have hp(s:ℝ): ‖arch A j s‖^2= ‖A‖^2+ s*(2*rub j A)+s^2*‖j‖^2:=by simp only [arch,norm_add_sq_real, real_inner_smul_right,norm_smul,Real.norm_eq_abs, mul_pow,sq_abs]; unfold rub; rw [real_inner_comm A]; ring
   simp_rw [hp] at h; let B:=2*rub j A; exact h.unique (by convert ((((hasDerivAt_const (0:ℝ) (‖A‖^2)).add ((hasDerivAt_id' _).mul_const B)).add (((hasDerivAt_id' (0:ℝ)).pow 2).mul_const (‖j‖^2))).div_const 2|>.exp) using 1 <;> (try simp [B]) <;> (first|rfl|funext s;rfl|ring))
 | cons i l ih=>
    rw [show χfund A (j::i::l)=χfund A (i::j::l) from ?_,charm,List.nil_append]; swap
    · unfold χfund; congr; ext x; unfold lipW; change _*(rub j x*(rub i x*dais l x))= _*(rub i x*(rub j x*dais l x)); ring
    have he:=fund_Q A i (j::l); simp_rw [ih] at he
    have hh:= ((((hasDerivAt_const (0:ℝ) (rub j A)).add ((hasDerivAt_id' _).mul_const (rub j i))).mul (fund_Q A i l)).add (deriv_charm A i j [] l)); simp only [arch_rub] at he; apply he.unique
    convert hh using 1 <;> (try simp [arch_at,add_left_comm,add_assoc]) <;> rfl -- tune
lemma entryD (L:List E): χfund 0 L= ∫ x,dais L x ∂stdGaussian E:=by unfold χfund lipW; simp [rub]
lemma lockW (L:List E)(j:E): χfund 0 (j::L) = charm j [] L 0:=by simp [stitch L,rub]
lemma χØ : χfund (0:E) []=1:=by rw [grantZ]; simp
#print axioms lockW
end Prims
end YM.Gleam.Guide
end
