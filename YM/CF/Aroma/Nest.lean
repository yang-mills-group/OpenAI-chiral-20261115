import YM.CF.Aroma.Prize
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{N:Side}
def sand(t:Cover):ℝ:= ∑ a:Axis,(t a).natAbs
def idea(a:ℝ)(x: Site N):= Real.exp (a*sand (lift x))
lemma mode_v (p:Momentum)(a:ℝ)(h:p∈cube a)(x:Cover): ‖mode p x‖≤ Real.exp (a*sand x):=by
 rw [mode,Complex.norm_exp]; apply Real.exp_le_exp.mpr
 have he(j) : -((p j).im*(x j))≤ a * ↑(x j).natAbs:=by
    have hh: |(p j).im|≤a:= (h.1 j).le
    refine (neg_le_abs ((p j).im*↑(x j))).trans ?_; rw [abs_mul,←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast]; gcongr
 simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul, one_mul,zero_sub,Complex.re_sum, ← sum_neg_distrib,sand,Finset.mul_sum]; apply sum_le_sum; intro i _; simpa [Complex.mul_im] using he i
lemma pet_p(p:Momentum)(a:ℝ)(h:p∈cube a)(x: Site N):‖pet x p‖≤ idea a x:=by unfold pet idea; rw [norm_mul,Rush.wind,fee_norm,one_mul]; exact mode_v p a h _
lemma log_p(p:Momentum)(a:ℝ)(g:0≤a)(h:p∈cube a)(x y: Site N): ‖logA p (lift x-lift y)‖≤ idea a x*idea a y:=by
 let t:= lift x-lift y; let u:=idea a x*idea a y
 have hx:sand t≤sand (lift x)+sand (lift y):=by
   unfold sand; rw [←sum_add_distrib]; apply sum_le_sum; intro i _; change (↑((_ - _ :ℤ).natAbs):ℝ)≤ _; exact_mod_cast Int.natAbs_sub_le .. -- tune
 have he (p: Momentum)(h:p∈cube a): ‖mode p t‖≤ u:= by apply (mode_v p a h _).trans; unfold u idea; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; rw [← mul_add]; gcongr
 change ‖(_+_)/2‖≤ u; rw [norm_div, show ‖(2:ℂ)‖=2 by norm_num,div_le_iff₀ (by norm_num : (0:ℝ)<2),mul_two]; exact (norm_add_le ..).trans (add_le_add (he p h) (he _ (cube_neg _ h)))

def rook (A:Cab n N)(x:Site N):Op (coneA n):=Matrix.of fun i j=> A (0,i) (x,j)
def oak (J:InJ n N)(x:TestX):Op (coneA n):=∑ k:Site N,∑ i:Site (More N), (mode x.1 (lift i)*pet k x.2) • rook (JD J (spur i)) k
def float (J:InJ n N)(x:TestX):Op (coneA n):=∑ k:Site N,∑ i:Site (More N),∑ j:Site (More N), (logA x.1 (lift i-lift j)*pet k x.2) • rook (JG J (spur i) (spur j)) k
def bill (J:InJ n N)(a:ℝ):=∑ k:Site N,∑ i:Site (More N), idea a k*idea a i* ‖rook (JD J (spur i)) k‖
def b2 (J:InJ n N)(a:ℝ):=∑ k:Site N,∑ i:Site (More N),∑ j:Site (More N), idea a k*idea a i*idea a j*‖rook (JG J (spur i) (spur j)) k‖
lemma paidL(J: InJ n N){a C:ℝ}(h:0<a)(p:0<C)(e:bill J a≤C):SkinH a C (oak J):=by
 constructor <;> try assumption
 · unfold oak pet mode; intros; fun_prop
 intro x hx hg; apply le_trans _ e; unfold oak bill; refine (norm_sum_le ..).trans (sum_le_sum fun k _=> (norm_sum_le ..).trans (sum_le_sum (fun i _=>?_))); rw [norm_smul,norm_mul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); rw [mul_comm (idea a k)]; exact mul_le_mul (mode_v x.1 a hx (lift i)) (pet_p x.2 a hg k) (norm_nonneg _) (Real.exp_pos _ |>.le)
lemma petals(J: InJ n N){a C:ℝ}(h:0<a)(p:0<C)(e:b2 J a ≤C):SkinH a C (float J):=by
 constructor <;> try assumption
 · unfold float pet logA mode; intros; fun_prop
 intro x hx hg; apply le_trans _ e; unfold float b2; refine (norm_sum_le ..).trans (sum_le_sum fun k _=> (norm_sum_le ..).trans (sum_le_sum (fun i _=> (norm_sum_le ..).trans (sum_le_sum (fun j _=>?_))))); rw [norm_smul,norm_mul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); rw [mul_assoc (idea a k),mul_comm (idea a k)]; exact mul_le_mul (log_p x.1 a h.le hx i j) (pet_p x.2 a hg k) (norm_nonneg _) (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le))
lemma oak_per (J: InJ n N)(p q:Momentum)(x:Cover): oak J (q,p+reciprocal x)=oak J (q,p):=by simp [oak,pet]
lemma oak_bind(J:InJ n N)(h:ContDiffAt ℝ ω J 0)(k:CurveH J)(q)(F:Tide N q): firstH J q =hub F.σ fun i => oak J (q,mel i) :=by
 apply tunnel F _ (coneA1 F J h k); intro l i j; simp_rw [oak,rook,Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,stem_w J q,Matrix.sum_apply,Matrix.smul_apply,sum_mul, F.fresh,smul_eq_mul]; apply sum_congr rfl; intro k _; apply sum_congr rfl; intro x _; ring
lemma float_bind(J:InJ n N)(h:ContDiffAt ℝ ω J 0)(k:CurveH J)(q)(F:Tide N q): secondH J q =subHub fun i => float J (q,mel i) :=by
 let Q:Tide N 0:=⟨by simp [physical],fun _=>by simp [mode],Equiv.refl _,fun i=>⟨0,by ext; simp [spoon,reciprocal]⟩⟩
 apply tunnel Q _ (coneB1 F J h k); intro l i j; simp_rw [float,rook,Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,pine_w J q F,Matrix.sum_apply,Matrix.smul_apply,sum_mul, smul_eq_mul]; apply sum_congr rfl; intro k _; apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; ring
end YM.CF.Aroma
