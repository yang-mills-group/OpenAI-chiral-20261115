import ZecaFoam
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open MeasureTheory
open Complex (I)
variable {A:ℕ→ℂ→ℂ} {T:ℝ}{W:ℕ→ℝ→ℂ}
abbrev squareI (A:ℕ→ℂ→ℂ)(T:ℝ)(W:ℕ→ℝ→ℂ) (i n:ℕ)(r:ℝ):=
   shellI (A i) T (W n) (r^2)

variable (h:Seaward A) (p:0<T) (q:Temporal T W)
include h q p
lemma square_s (r:ℝ)(e:0<r)(n i:ℕ):
 HasDerivAt (squareI A T W i n) ((2*r:ℝ) •(-I*squareI A T W i (n+1) r)) r:= by
  have hd:HasDerivAt (fun r:ℝ=>r^2) (2*r) r:=by rw [two_mul];simp_rw [pow_two]; have y:= (hasDerivAt_id' r).mul (hasDerivAt_id' r); beta_reduce at y; rw [one_mul,mul_one] at y;exact y
  exact ((redshift (h.enters i) p q n (pow_pos e _)).scomp r hd)
def Standing(A:ℕ→ℂ→ℂ)(T:ℝ)(W:ℕ→ℝ→ℂ)(d:ℕ):Prop:=
   ∀n,∃ B:ℝ,0≤B ∧ ∀ r∈Set.Ioc (0:ℝ) 1,∀ i, ‖squareI A T W i n r‖ ≤ B/r^d


lemma standing_born:∃d,Standing A T W d:=by
 obtain ⟨d,C,hC,t⟩:=h.cost
 let μ:=volume.restrict (Set.Icc (-T) T)
 refine ⟨2*d,fun n=> ⟨(∫ y,‖W n y‖ ∂μ)*(2*C),
      mul_nonneg (integral_nonneg (fun _=>norm_nonneg _)) (by positivity),
      fun r e i=>?_⟩⟩
 have e0:0<r:=e.1
 have t1:Integrable (fun y=>‖W n y‖) μ:=(q.slow _).norm.continuousOn.integrableOn_Icc
 apply le_trans (norm_integral_le_of_norm_le
     (t1.mul_const (2*C/r^(2*d))) (ae_of_all _ ?_))
 · rw [integral_mul_const,← mul_div_assoc]
 intro y
 simp only [norm_mul]
 apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 apply (t i _ (tide_p (pow_pos e0 2) y)).trans
 rw [tide_re,spur,pow_mul]
 have e1:1≤(1/r^2)^d:=one_le_pow₀ ((one_le_div (pow_pos e0 2)).mpr (pow_le_one₀ e0.le e.2))
 have e2: 1+(1/r^2)^d ≤ 2*(1/r^2)^d:=by linarith
 apply (mul_le_mul_of_nonneg_left e2 hC.le).trans
 rw [div_pow, one_pow]
 ring_nf; rfl

lemma standing_shift {d:ℕ}(t:Standing A T W (d+1)): Standing A T W d:=by
 intro n
 obtain ⟨C,c₀,c⟩:=t n
 obtain ⟨B,b₀,b⟩:=t (n+1)
 refine ⟨2*B+C,by positivity,fun r e i=>?_⟩
 have e0:=e.1
 let y v:= (2*v:ℝ) •(-I*squareI A T W i (n+1) v)
 have hp(v)(u:v∈Icc r 1):
    HasDerivWithinAt (squareI A T W i n) (y v) (Icc r 1) v:=
   (square_s h p q v (e0.trans_le u.1) n i).hasDerivWithinAt
 have v1(v)(u:v∈Icc r 1): ‖y v‖≤2*B/r^d:=by
    have a:=e0.trans_le u.1
    unfold y
    rw [norm_smul, Real.norm_of_nonneg (by positivity), norm_mul,norm_neg,Complex.norm_I,one_mul]
    apply (mul_le_mul_of_nonneg_left (b v ⟨a,u.2⟩ i) (by positivity)).trans
    rw [show 2*v*(B/v^(d+1))=2*B/v^d by rw [pow_succ];field_simp]
    have vv:=pow_pos e0 d
    gcongr
    exact u.1
 have e1:=e.2
 have m:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hp v1
     (convex_Icc ..) ⟨e1,le_rfl⟩ ⟨le_rfl,e1⟩
 have a:‖squareI A T W i n r - squareI A T W i n 1‖≤ 2*B/r^d:=by
     exact m.trans (mul_le_of_le_one_right (by positivity) (show ‖r-1‖≤1 from by
        rw [Real.norm_of_nonpos (sub_nonpos.mpr e1)]
        linarith only [e0]))
 rw [add_div]
 refine (norm_le_norm_sub_add ..).trans (add_le_add a ((c 1 ⟨zero_lt_one,le_rfl⟩ i).trans ?_))
 rw [one_pow]; have u:=pow_pos e0 d
 exact div_le_div_of_nonneg_left c₀ u (pow_le_one₀ e0.le e.2)

lemma standing_room:Standing A T W 0:=by
 obtain ⟨d,g⟩:=standing_born h p q
 induction d with
 | zero=> exact g
 | succ d ih=>exact ih (standing_shift h p q g)
#print axioms standing_room
