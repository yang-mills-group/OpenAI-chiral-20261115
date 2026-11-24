import Zephyr.Chern.Bud
-- minimal Mathlib closure?
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Filter Topology Metric
namespace YM.CF.Organdy
variable {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F:V→ℂ}{A B:V→V→ℂ}{r c:ℝ}
abbrev skewer (F:V→ℂ)(A B:V→V→ℂ) (x y:V) (t:ℝ) : ℂ:=
 F (x+t•y) - (F x + t*A x y + t^2*B x y)
-- NB `t^` type coerced ℂ
structure Sugar (r c:ℝ)(F:V→ℂ)(A B:V→V→ℂ):Prop where
 fresh: 0<r
 plus : 0≤c
 flow : ContinuousOn F (ball 0 (r+r))
 lean (y:V) : ‖A 0 y‖ ≤ c*‖y‖
 bend (y:V) : ‖B 0 y‖ ≤ c*‖y‖^2
 coat (x y:V)(t:ℝ) (p:‖x‖<r) (h: |t| * ‖y‖<r):
  ‖skewer F A B x y t‖ ≤ c * (|t| * ‖y‖)^3

namespace Sugar
variable (f:Sugar r c F A B)
abbrev pearl (F:V→ℂ)(x y:V)(t:ℝ): ℂ :=F (x+t•y)+F (x+(-t)•y)-2*F x

include f
lemma dorsal (x y:V)(t:ℝ) (p:‖x‖<r)(h: |t| * ‖y‖<r):
 ‖pearl F x y t - t^2*(2*B x y)‖ ≤
   2*(c * (|t| * ‖y‖)^3):=by
 rw [show pearl F x y t - t^2*(2*B x y)=skewer F A B x y t + skewer F A B x y (-t) from
    (by unfold skewer pearl; push_cast; ring), two_mul]
 exact (norm_add_le ..).trans (add_le_add (f.coat x y t p h)
    (by simpa using f.coat x y (-t) p (by simpa)))
lemma nib (x y:V)(t:ℝ) (p:‖x‖<r)(h: |t| * ‖y‖<r)(v:0<t):
 dist (pearl F x y t / (2*t^2)) (B x y) ≤ c*‖y‖^3*t:=by
 rw [dist_eq_norm_sub,div_sub' (hc:=?c)] -- avoid
 rw [show pearl F x y t - 2*t^2*B x y= pearl F x y t - t^2*(2*B x y) by ring, norm_div,norm_mul,norm_pow,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,abs_of_pos v]
 rw [div_le_iff₀ (by positivity)]
 exact (f.dorsal x y t p h).trans_eq (by rw [abs_of_pos v];ring)
 case c => exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr v.ne'))
lemma halva {α:Type*}{l:Filter α}{x y:V}{sx sy:α→V}
   (zx:Tendsto sx l (𝓝 x))(zy:Tendsto sy l (𝓝 y)) (u:‖x‖<r):
   Tendsto (fun i=> B (sx i) (sy i)) l (𝓝 (B x y)):=by
 apply Metric.tendsto_nhds.mpr; intro ε e
 let h:=‖y‖+1
 have g : ∀ᶠ t:ℝ in 𝓝[>] 0, c*h^3*t < ε/4 ∧ t*h < r ∧ 0<t:=by
    apply Eventually.and
    · exact (continuous_const.mul continuous_id').continuousWithinAt (s:=Set.Ioi _)
           |>.tendsto.eventually (gt_mem_nhds (by change c*h^3*0<ε/4;rw [mul_zero]; linarith))
    exact ((continuous_id'.mul continuous_const).continuousWithinAt.tendsto.eventually
      (gt_mem_nhds (by change 0*h<r;rw [zero_mul]; exact f.fresh))).and self_mem_nhdsWithin
 obtain ⟨t,a,b,d⟩:=g.exists
 let L (x y:V):=pearl F x y t/(2*t^2)
 have bound {x' y':V}(p:‖x'‖<r)(q:‖y'‖<h):
      dist (L x' y') (B x' y') < ε/4:=by
    have n:|t| * ‖y'‖<r:= by rw [abs_of_pos d]; exact (mul_le_mul_of_nonneg_left q.le d.le).trans_lt b
    exact (f.nib x' y' t p n d).trans_lt ((mul_le_mul_of_nonneg_right 
       (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) q.le 3) f.plus) d.le).trans_lt a)
 have U:‖y‖<h:=lt_add_of_pos_right _ one_pos
 have n:|t| * ‖y‖<r:= by rw [abs_of_pos d]; exact (mul_le_mul_of_nonneg_left U.le d.le).trans_lt b
 have G:(∀ {e} {p:α→V}, ‖e‖<r+r → Tendsto p l (𝓝 e) → 
   Tendsto (fun i=> F (p i)) l (𝓝 (F e))) := by
    intro z p h k; exact (f.flow.continuousAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr h))).tendsto.comp k
 have hl:Tendsto (fun i=> L (sx i) (sy i)) l (𝓝 (L x y)):=by
    have u1:‖x+t•y‖<r+r:=(norm_add_le ..).trans_lt (add_lt_add u (by simpa [norm_smul] using n))
    have u2:‖x+(-t)•y‖<r+r:=(norm_add_le ..).trans_lt (add_lt_add u (by simpa [norm_smul] using n))
    exact (((G u1 (zx.add (tendsto_const_nhds.smul zy))).add
      (G u2 (zx.add (tendsto_const_nhds.smul zy)))).sub
      (tendsto_const_nhds.mul (G (u.trans (lt_add_of_pos_right _ f.fresh)) zx))).div_const _
 filter_upwards [zx.norm.eventually (gt_mem_nhds u),zy.norm.eventually (gt_mem_nhds U),
    hl.eventually (ball_mem_nhds _ (by linarith:0<ε/2))] with i p q m
 change dist (L (sx i) (sy i)) (L x y)<ε/2 at m
 exact (dist_triangle4 _ (L (sx i) (sy i)) (L x y) _).trans_lt
    (by rw [dist_comm (B _ _)]; linarith [bound p q,bound u U])

omit f in
lemma bar {g:ℂ} {h:ℝ→ℂ}{k:ℂ}{M:ℝ}
   (p:Tendsto h (𝓝[>] 0) (𝓝 k))
   (u:∀ᶠ t:ℝ in 𝓝[>] 0,‖(t:ℂ)*g+t^2*h t‖ ≤ M*(t:ℝ)^3):
 g=0 ∧ k=0:=by
 let t₀:= show Tendsto (fun t:ℝ=>(t:ℂ)) (𝓝[>] 0) (𝓝 0) from by
   rw [←Complex.ofReal_zero]; exact Complex.continuous_ofReal.continuousWithinAt.tendsto
 have hw:Tendsto (fun t:ℝ=>g+t*h t) (𝓝[>] 0) (𝓝 g):=by simpa using (tendsto_const_nhds (x:=g)).add (t₀.mul p)
 have x:g=0:=by
    refine tendsto_nhds_unique hw (squeeze_zero_norm' (a:=fun t=>M*t^2) ?_ ?_)
    · filter_upwards [u,self_mem_nhdsWithin] with t r z
      change 0<t at z
      rw [show (t:ℂ)*g+(t:ℂ)^2*h t=t*(g+t*h t) by ring,
          norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z] at r
      exact le_of_mul_le_mul_left (r.trans_eq (by ring)) z
    nth_rw 3 [show (0:ℝ)= M*0^2 by ring] -- rw at filter too, bad
    exact (continuous_const.mul (continuous_id'.pow 2)).continuousWithinAt.tendsto
 rw [x] at u

 refine ⟨x,tendsto_nhds_unique p (squeeze_zero_norm' (a:=fun t=>M*t) ?_ ?_)⟩
 · filter_upwards [u,self_mem_nhdsWithin] with t r z
   change 0<t at z
   rw [mul_zero,zero_add,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z] at r
   exact le_of_mul_le_mul_left (r.trans_eq (by ring)) (pow_pos z 2)
 nth_rw 3 [show (0:ℝ)= M*0 by ring]
 exact (continuous_const.mul continuous_id').continuousWithinAt.tendsto

lemma jab (x y:V):
 (A 0 (x+y)+A 0 (x-y)=2*A 0 x) ∧
 (B 0 (x+y)+B 0 (x-y)=2*B 0 x+2*B 0 y):=by
 let g := A 0 (x+y)+A 0 (x-y)-2*A 0 x
 let j := B 0 (x+y)+B 0 (x-y)-2*B 0 x
 let h (t:ℝ) := j - 2*B (t•x) y
 let k := j - 2*B 0 y
 have r0:‖(0:V)‖ < r:=by simpa using f.fresh
 have C:Tendsto (fun t:ℝ=>t•x) (𝓝[>] 0) (𝓝 0):=by 
    rw [←zero_smul ℝ x] -- need no nth: zero types
    exact (continuous_id'.smul continuous_const).continuousWithinAt.tendsto
 have u:Tendsto h (𝓝[>] 0) (𝓝 k):=
   tendsto_const_nhds.sub (tendsto_const_nhds.mul (f.halva C tendsto_const_nhds r0))
 let R (v:V):=c*‖v‖^3
 have b (v:V) :∀ᶠ t:ℝ in 𝓝[>] 0, |t| * ‖v‖ < r:=
     ((continuous_id'.abs.mul continuous_const).continuousWithinAt.tendsto.eventually
       (gt_mem_nhds (by change |(0:ℝ)| * ‖v‖ < r; simpa using f.fresh)))
 suffices g=0∧k=0 by
    obtain ⟨v,w⟩:=this; unfold k j at w
    exact ⟨sub_eq_zero.mp v,sub_eq_zero.mp (by rw [← sub_sub]; exact w)⟩

 apply bar (M:=((R (x+y)+R (x-y)) + (R x + R x)) + 2*R y) u
 filter_upwards [b (x+y),b (x-y),b x,b y,self_mem_nhdsWithin] with t a l v w p
 let e z:=skewer F A B 0 z t
 let d:=pearl F (t•x) y t - t^2 * (2*B (t•x) y)
 have z: (t:ℂ)*g+(t:ℂ)^2*h t=( (-(e (x+y)+e (x-y))+(e x+e x)) + d ):=by
    dsimp only [e,d,h,g,j,pearl,skewer]
    simp only [zero_add, smul_neg,smul_add,neg_smul,sub_eq_add_neg]
    ring
 rw [z]
 apply (norm_add_le ..).trans
 have T0:‖t•x‖<r:=by simpa [norm_smul] using v
 have E:‖-(e (x+y)+e (x-y))+(e x+e x)‖≤_:=
    (norm_add_le ..).trans (add_le_add
      ((norm_neg ..).le.trans ((norm_add_le ..).trans (add_le_add (f.coat _ _ _ r0 a) (f.coat _ _ _ r0 l))))
       ((norm_add_le ..).trans (add_le_add (f.coat _ _ _ r0 v) (f.coat _ _ _ r0 v))))
 exact (add_le_add E (f.dorsal (t•x) y t T0 w)).trans_eq (by unfold R;rw [abs_of_pos (show 0<t from p)];ring)

omit f
def whippet (p:V→ℂ) (h:p 0=0) (g:∀ x y,p (x+y)+p (x-y)=2*p x) : V→+ℂ where
 toFun:=p
 map_zero':=h
 map_add' x y:=by
    have e:=g 0 (x-y)
    have u:=g y x
    rw [add_comm y] at u
    rw [h,zero_add,zero_sub,neg_sub] at e
    linear_combination (g x y + u - e)/2
include f
lemma lean_zero : A 0 0=0:=by simpa using (f.lean 0)
lemma bend_zero : B 0 0=0:=by simpa using (f.bend 0)
lemma lean_paid:
   ∃ L:V→ₗ[ℝ]ℂ,∀ x,A 0 x=L x:=by
    let v := whippet (A 0) f.lean_zero (fun x y=>(f.jab x y).1)
    exact ⟨(v.toRealLinearMap (AddMonoidHomClass.continuous_of_bound v c f.lean)).toLinearMap,fun _=>rfl⟩
def polar (Q:V→ℂ)(x y:V): ℂ := (Q (x+y)-Q (x-y))/4
lemma even (v:V):B 0 (-v)=B 0 v:=by
    have p:=(f.jab 0 v).2
    rw [f.bend_zero,zero_add,zero_sub] at p
    linear_combination p

lemma dual (v:V): ∃ L:V→ₗ[ℝ]ℂ,∀ x,polar (B 0) x v=L x:=by

  have z:polar (B 0) 0 v=0:=by unfold polar; rw [zero_add,zero_sub,f.even,sub_self,zero_div]
  have j:∀ x y:V,polar (B 0) (x+y) v + polar (B 0) (x-y) v=2*polar (B 0) x v:=by
    intro x y
    unfold polar
    rw [show x+y+v=x+v+y by abel,show x+y-v=x-v+y by abel,
        show x-y+v=x+v-y by abel,show x-y-v=x-v-y by abel]
    linear_combination ((f.jab (x+v) y).2 - (f.jab (x-v) y).2)/4
  let L:= whippet (fun x=>polar (B 0) x v) z j
  have h:Continuous (B 0):= continuous_iff_continuousAt.mpr (fun _=>f.halva tendsto_const_nhds tendsto_id (by rw [norm_zero];exact f.fresh))
  have c:Continuous L :=((h.comp (continuous_id.add continuous_const)).sub
    (h.comp (continuous_id.sub continuous_const))).div_const 4 -- coercion issue
  exact ⟨(L.toRealLinearMap c).toLinearMap,fun _=>rfl⟩
lemma bend_paid :
    ∃ Q: V→ₗ[ℝ]V→ₗ[ℝ]ℂ, (∀ x,B 0 x=Q x x)∧∀ x y,Q x y=Q y x:=by
  let L (v:V) :=(f.dual v).choose

  have p(x y): polar (B 0) x y=L y x:=(f.dual y).choose_spec x
  have t(x y): L x y=L y x:=by rw [←p,←p]; unfold polar; rw [add_comm x, ← neg_sub x,f.even]
  let Q: V→ₗ[ℝ]V→ₗ[ℝ]ℂ:=
   { toFun:=L
     map_add':=fun x y=>LinearMap.ext fun u=>show L (x+y) u=L x u+L y u from by rw [t,map_add,t u,t y]
     map_smul':=fun s x=>LinearMap.ext fun u=>show L (s•x) u = s•L x u from by rw [t,map_smul,t u]}
  refine ⟨Q,fun x=>?_,t⟩
  have h:=(f.jab x x).2
  rw [show Q x x=L x x from rfl, ←p, polar]
  rw [sub_self,f.bend_zero] at h ⊢; linear_combination -h/4
end Sugar
end YM.CF.Organdy
