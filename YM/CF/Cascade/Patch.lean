import YM.CF.Cascade.Seat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Pec
lemma mild_b (p:3≤(More n).val)(x:Orig n)(v:Step):‖hike (Aroma.port n) (x+v.vec)-hike (Aroma.port n) x‖ ≤ Cascade.pulse n:=by
 let k:= step 0 (S:=Per (More n)); have he(b:Axis): ‖cell k (step b)-1‖≤ Cascade.pulse n:=by
    rw [cell_step,show mon k=Aroma.port n from mon0 p]; by_cases h:b=0; · subst b; rw [show Aroma.port n 0=(Cascade.pulse n:ℂ) by simp [Aroma.port,Ember.spark,Cascade.pulse]]; refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_); exact Real.norm_of_nonneg (pinch_pos _).le
    simpa [Aroma.port,Ember.spark,h] using (pinch_pos n).le
 have hx(i:Orig n)(b:Axis):‖hike (Aroma.port n) (i + step b)-hike (Aroma.port n) i‖≤ Cascade.pulse n:=by rw [← mon0 p]; change ‖cell k _-cell k i‖≤_; rw [cell_add,← show cell k i * (cell k (step b)-1)= cell k i*cell k (step b)- cell k i by rw [mul_sub,mul_one],norm_mul,show ‖cell k i‖=1 from mode_real (mon k) (lift i) (real_frequency k),one_mul]; exact he b
 rcases v with ⟨i,b⟩; cases b; exact hx ..; change ‖hike _ (x+ -(step i:Orig n))-hike _ x‖≤ Cascade.pulse n; rw [norm_sub_rev]; have he:= hx (x+ -(step i)) i; rw [add_assoc,neg_add_cancel,add_zero] at he; exact he
lemma loud(t:Momentum)(p:physical t){F: ℂ→L[ℝ]ℝ}(h:∀ x,‖F x‖≤‖x‖) :‖groan (n:=n) F (hike t)‖≤ 1:=(pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=> (h _).trans (le_of_eq (mode_real _ _ p))
lemma milder(l:3≤(More n).val){F:ℂ→L[ℝ]ℝ}(h:∀ x,‖F x‖≤‖x‖) (x:Orig n) (t:Step):‖groan F (hike (Aroma.port n)) (x+t.vec) -groan F (hike (Aroma.port n)) x‖≤ Cascade.pulse n:=by change ‖F (hike _ _)-F (hike _ _)‖≤ _; rw [←map_sub]; exact (h _).trans (mild_b l x t)
lemma bulk(t:ℝ)(A:Pride n)(h: Lac A a b)(g:0<a)(v:Cloud n)(hw:‖v‖≤1)(hp:Sway (collect group v) t)(z:Cascade.pulse n≤t):‖trim 2 (Pec.pigment A∘ represent) v‖≤ Fintype.card (Site n)*(4*t^2*momentPrice 4 a * b):=by
 have he:=zpark A; rw [← (asideF ((tuck A).of_le le_top) _ he).2 v]; unfold diem; let X:=4*t^2*momentPrice 4 a; let C:= (Fintype.card (Site n):ℝ)*(X*b)
 have hk(i: Signed): ‖pays i (∑ j:Site n, datam (node j) (A j) (litX i v))‖≤ C:=by
    have hy(y):‖Pec.pays i y‖=‖y‖:=by cases q:detX i<;> simp [Pec.pays,q]
    rw [hy]; apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun _=> X*b) fun j _=> (dataFee v t hw hp z g _ i _).trans (mul_le_mul_of_nonneg_left (h.pay j) (by have H:=momentPrice_pos 4 g; positivity))).trans; simp only [sum_const,card_univ,nsmul_eq_mul]; rfl
 rw [norm_smul,Real.norm_of_nonneg (by positivity)]; apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=>hk i))) (by positivity)).trans; rw [sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ (by positivity)]
lemma iceL(A:Pride n)(h:Lac A a b)(g:0<a)(u:CoreX)(w:‖u‖=1)(x:Air n)(hx:‖x‖≤1): ‖trim 2 (Pec.pigment A∘ represent) (pour n u x)‖≤ Fintype.card (Site n)*(4*4^2*momentPrice 4 a*b):=by
 have hh:= glance x u w hx; apply bulk 4 _ h g _ hh; intro i j a; exact (norm_sub_le ..).trans ((add_le_add ((norm_le_pi_norm (pour n u x) _).trans hh) ((norm_le_pi_norm (pour n u x) _).trans hh)).trans (by norm_num))
 exact ((div_le_self Real.pi_pos.le (show (1:ℝ)≤n.val from by exact_mod_cast n.property))).trans Real.pi_le_four
lemma nearCapR(p:Momentum)(F:Tide n p): grove n (hike p)= amber p∧ waveL n (hike p)= zinnia p:=⟨funext fun i=>congrArg Complex.re (F.fresh i).symm,funext fun i=> congrArg Complex.im (F.fresh i).symm⟩
def copper (n:Side)(u:CoreX)(A:Cloud n→ℂ): Heat n := (show (_→ₗ[ℝ]ℝ) ≃ₗ[ℝ](Air n→L[ℝ]ℝ) from LinearMap.toContinuousLinearMap).symm.toLinearMap.comp (fderiv ℝ (fderiv ℝ (Complex.reCLM ∘ A ∘ pour n u)) 0).toLinearMap
lemma copperP (u:CoreX)(f:Cloud n→ℂ)(p:ContDiffAt ℝ (↑(2:ℕ)) f 0)(x:Air n): copper n u f x x= 2*(trim 2 f (pour n u x)).re:=by
 let Z:= Complex.reCLM∘ f; let L:=pour n u
 have he:ContDiffAt ℝ (↑(2:ℕ)) Z 0:= Complex.reCLM.contDiff.contDiffAt.comp 0 p
 have hx : (trim 2 f (pour n u x)).re= trim 2 Z (pour n u x):=(extendJ 2 2 _ _ p le_rfl Complex.reCLM).symm
 rw [hx]; have hp': (fderiv ℝ (fderiv ℝ (Z∘ L)) 0 x x)= Tensor.diagonal (iteratedFDeriv ℝ 2 Z 0) (L x):=by
    rw [show (fderiv ℝ (fderiv ℝ (Z∘ L)) 0 x x)=iteratedFDeriv ℝ 2 (Z ∘ L) 0 (fun _ =>x) from (by rw [iteratedFDeriv_two_apply]), Push.Uniform.iter_lin_at (L:=L) (show ContDiffAt _ _ _ (L 0) from ((map_zero L).symm ▸ he)),map_zero]; rfl
 change (fderiv ℝ (fderiv ℝ (Z ∘ L)) _ x x)=_; rw [hp']; unfold trim cake Tensor.diagonal; simp only [_root_.smul_apply,smul_eq_mul]; unfold L; norm_num; ring
lemma palmC {B L:Side}{ho:Odd L.val}{e:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{P:Grasp Y B e} (M:Male)(x:Air n)(p:P.roundZ≤ n.val)(k:0<e)(v:1≤j)(S:Stamped j L ho Y)(u:CoreX)(U:Dress n)(g:Ample U)(Q:ContDiffAt ℝ ω (spar j M ∘ represent (n:=More n)) 0):palmH (ArcJ u j M U) x = 2*trim 2 (gala M j U ∘ represent) (pour n u x):=by
 unfold palmH; let J:=ArcJ u j M U; let F:=gala M j U ∘ represent; let A:= pour n u x; rw [show (fun t:ℝ=>Aroma.cash (Met J (t • x)))=(fun t:ℝ=>F (t • A)) from ?_]; swap; · funext t; rw [plume]; unfold F; rw [show pour n u (t • x)=t • A from map_smul ..]; exact beamCash ..
 change deriv (deriv fun t:ℝ=> F (t • A)) 0=_; rw [show deriv (deriv (fun t:ℝ=> F (t • A))) 0=_ from (by simp [iteratedDeriv_succ'] :deriv (deriv fun t:ℝ=>F (t • A)) 0=iteratedDeriv 2 (fun t:ℝ=>F (t • A)) 0), Next.Foundations.iteratedDeriv_on_line (k:=2) ((gala_h p k v S M U g Q).of_le le_top) ]; unfold trim cake Tensor.diagonal; unfold A; simp only [_root_.smul_apply,smul_eq_mul]; norm_num; ring
end YM.CF.Cascade
