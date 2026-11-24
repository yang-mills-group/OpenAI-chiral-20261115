import YM.Push.STATIONARY_UNIFORM.Beacons
import YM.CF.Jet.Mask
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Gingham.Ruff
open Jet Set Metric Function Finset Push
open scoped ContDiff Topology
variable {E F Y:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
    [NormedAddCommGroup Y][NormedSpace ℝ Y]


variable {f:E→F}{w:ℝ}{n:ℕ}
def Gallery(n:ℕ)(f:E→F)(w:ℝ):Prop:=∀ x, ‖x‖<1→ Allows n f x w
namespace Gallery
lemma lower (G: Gallery n f w):0≤w:=(G 0 (by simp)).nonneg
lemma sub (G: Gallery n f w)(m:ℕ)(h:m≤n):Gallery m f w:=fun x y=> (G x y).order h
lemma listens (G: Gallery n.succ f w){x:E}(u:‖x‖<1) : DifferentiableAt ℝ f x := 
 (G x u).smooth.differentiableAt (by simp)
lemma thread (G: Gallery n.succ f w):Gallery n (fderiv ℝ f) w:=
 fun x t=> (G x t).slide
lemma change₁ (G: Gallery 1 f w) {x:E}(u:‖x‖<1):
 ‖f x-f 0‖ ≤ w*‖x‖:=by
 simpa using
  (convex_ball (0:E) (1:ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun i h=>G.listens (mem_ball_zero_iff.mp h))
    (fun i h=>(G.thread i (mem_ball_zero_iff.mp h)).value)
    (mem_ball_zero_iff.mpr (show ‖(0:E)‖<1 by simp))
    (mem_ball_zero_iff.mpr u)


lemma change₂ (G: Gallery 2 f w){x:E}(u:‖x‖<1):
 ‖f x-f 0-fderiv ℝ f 0 x‖ ≤ w*‖x‖^2:=by
  have h(i)(z:i∈closedBall (0:E) ‖x‖):‖i‖≤‖x‖:=mem_closedBall_zero_iff.mp z
  let g:= G.sub 1 (by decide)
  rw [pow_two,←mul_assoc]
  convert (convex_closedBall (0:E) ‖x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun i v=>(g.listens ((h i v).trans_lt u)).hasFDerivAt.hasFDerivWithinAt)
    (fun i v=> (G.thread.change₁ ((h i v).trans_lt u)).trans (mul_le_mul_of_nonneg_left (h i v) G.lower))
    (show (0:E)∈closedBall (0:E) ‖x‖ by simp) (mem_closedBall_zero_iff.mpr (show ‖x‖≤‖x‖ from le_rfl))
    using 1 <;> simp

lemma change₂_0 (G:Gallery 2 f w)(z:fderiv ℝ f 0=0){x:E}(u:‖x‖<1):
 ‖f x-f 0‖≤w*‖x‖^2:=by simpa [z] using G.change₂ u

lemma slope₀ (G: Gallery 2 f w)(z:fderiv ℝ f 0=0){x:E}(u:‖x‖<1):
 ‖fderiv ℝ f x‖≤w*‖x‖:=by simpa [z] using G.thread.change₁ u


lemma cubic (G:Gallery 3 f w)(z:fderiv ℝ f 0=0){x:E}(u:‖x‖<1):
 let H:=fderiv ℝ (fderiv ℝ f) 0
 ‖f x - f 0 - (2:ℝ)⁻¹ • (H x x)‖ ≤ w*‖x‖^3:=by
 intro H
 let g(t:ℝ):= f (t • x) - (t^2/2:ℝ) • H x x
 let A(t:ℝ):=fderiv ℝ f (t • x)-H (t • x)
 let D(t:ℝ):=A t x
 have size(t:ℝ)(a:0≤t)(b:t≤1):‖t • x‖≤‖x‖:=by
   rw [norm_smul,Real.norm_of_nonneg a];exact mul_le_of_le_one_left (norm_nonneg x) b
 suffices ‖g 1-g 0‖≤w*‖x‖^3 from by
   rwa [show g 1-g 0=f x - f 0 - (2:ℝ)⁻¹ • (H x x) by simp [g]; abel] at this
 apply norm_image_sub_le_of_norm_deriv_le_segment_01' (f':=D)
 · intro t v
   have i: ‖t • x‖<1:=(size t v.1 v.2).trans_lt u
   have d₁:HasDerivAt (fun t:ℝ=>t • x) x t:=by simpa using (hasDerivAt_id' t).smul_const x
   have d₂:=HasFDerivAt.comp_hasDerivAt t (G.listens i).hasFDerivAt d₁


   have d₃:HasDerivAt (fun t:ℝ => t^2/2) t t:=by
     convert (((hasDerivAt_id t).pow 2).div_const 2) using 1 <;> try rfl
     push_cast; rw [id_eq]; norm_num
   rw [show D t=fderiv ℝ f (t • x) x - t • (H x x) by simp [D,A]]
   exact (d₂.sub (d₃.smul_const (H x x))).hasDerivWithinAt
 intro t v
 have m:=size t v.1 v.2.le
 have h: ‖A t‖≤ w*‖x‖^2:=by
    apply le_trans _ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) m 2) G.lower)
    unfold A H
    simpa [z] using G.thread.change₂ (m.trans_lt u)
 rw [pow_succ,←mul_assoc]
 exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

#print axioms cubic

/-- Billing the deviation of a consultation at small configuration x
   with small directions T. -/
lemma quadratic (p:2≤n)(G:Gallery n f w)(z:fderiv ℝ f 0=0)
   {t:ℝ}(q:t<1){x:E}(u:‖x‖≤ t)
   (T:Y→L[ℝ]E)(k:‖T‖≤ t) :
   Allows n (fun y:Y=>f (x+T y)-f 0) 0 (w*t^2):=by
  have c: ContDiffAt ℝ (↑n) (fun v=>f v-f 0) x:=
    (G x (u.trans_lt q)).smooth.sub contDiffAt_const
  let g(v:E):= f (x+v)-f 0
  have g0: ContDiffAt ℝ (↑n) g (T 0):=by
    rw [map_zero]
    exact (show ContDiffAt ℝ (↑n) (fun v=>f v-f 0) (x+0) by simpa using c).comp _ 
      (f:=fun v=> x+v) (by fun_prop)
  change Allows n (g ∘ T) 0 _
  refine ⟨g0.comp _ T.contDiff.contDiffAt,fun r he=>?_⟩
  by_cases r0:r=0
  · subst r
    rw [norm_iteratedFDeriv_zero, comp_apply,map_zero]
    unfold g
    rw [add_zero]
    exact ((G.sub 2 p).change₂_0 z (u.trans_lt q)).trans 
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) u 2) G.lower)


  rw [Uniform.iter_lin_at (g0.of_le (Nat.cast_le.mpr he))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  have e: ‖iteratedFDeriv ℝ r g (T 0)‖=‖iteratedFDeriv ℝ r f x‖:=by
    change ‖iteratedFDeriv ℝ r (fun i=> (f - fun _=>f 0 :E→F) (x+i)) (T 0)‖=_
    rw [map_zero,iteratedFDeriv_comp_add_left, add_zero, 
      iteratedFDeriv_sub_apply (((G x (u.trans_lt q)).smooth).of_le (Nat.cast_le.mpr he)) contDiffAt_const,
      iteratedFDeriv_const_of_ne r0,Pi.zero_apply,sub_zero]
  simp only [prod_const,card_univ,Fintype.card_fin,e]
  by_cases hi:r=1
  · subst r
    have h:=((G.sub 2 p).slope₀ z (u.trans_lt q)).trans (mul_le_mul_of_nonneg_left u G.lower)
    rw [pow_one,norm_iteratedFDeriv_one,pow_two,←mul_assoc]
    exact mul_le_mul h k (norm_nonneg _) (mul_nonneg G.lower ((norm_nonneg _).trans k))
  have hm:2≤r:=by omega
  exact mul_le_mul ((G x (u.trans_lt q)).norm_le _ he)
    ((pow_le_pow_left₀ (norm_nonneg _) k r).trans
      (pow_le_pow_of_le_one ((norm_nonneg _).trans k) q.le hm)) (by positivity) G.lower

end Gallery

