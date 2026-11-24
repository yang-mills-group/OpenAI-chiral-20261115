import YM.CF.Font.Tulip
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Lattice Wilson Laurent RG Precision Tree Finset Exterior Extra Extra.Iteration Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {L f n c:Side}{g: Ratio c f}{A a b:ℝ}
def nick(a s:ℝ): ℝ:= (1+s)*Real.exp (a*s)
lemma nick_pos(a:ℝ){s:ℝ}(h:0≤s):0< nick a s:=by unfold nick; positivity
lemma nick_cheap {s:ℝ}(h:0≤s){a:ℝ}(hp:0≤a):1≤nick a s:=by unfold nick; exact one_le_mul_of_one_le_of_one_le (by linarith) (Real.one_le_exp (mul_nonneg hp h))
lemma nick_add{a s t:ℝ}(h:0≤s)(p:0≤t): nick a (s+t)≤ nick a s*nick a t:=by unfold nick; rw [mul_add,Real.exp_add,show (1+s)*_*((1+t)* Real.exp (a*t))= (1+s)*(1+t)*(Real.exp (a*s)*Real.exp (a*t)) by ring]; exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
lemma nick_inc(h:0≤a){s t:ℝ}(p:0≤s)(e:s≤t): nick a s≤nick a t:=by unfold nick; gcongr; linarith
lemma nick_rate {s:ℝ}(e:a≤b)(p:0≤s):nick a s≤ nick b s:=by unfold nick; gcongr
def taxH (a:ℝ):=momentPrice 1 (a/2)
lemma dentH {x:ℝ}(h:0<a)(e:b≤ a/2)(p:0≤x):nick b x ≤ taxH a*Real.exp (a*x):=by
 apply (nick_rate e p).trans; have he:= spendMoment 1 (half_pos h) p; rw [pow_one] at he; unfold nick; refine (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le).trans_eq ?_; unfold taxH; rw [mul_assoc,← Real.exp_add]; ring_nf
lemma Faro_comp {x y w:Site c}{r:ℝ}(h:0≤a)(p:↑(separation x y)≤r):Faro a x w ≤ Real.exp (a*r)* Faro a y w:=by
 unfold Faro; rw [←Real.exp_add,←mul_add]; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ h
 exact (le_trans (b:=↑(separation x y)+(separation y w:ℝ)) (by exact_mod_cast separation_triangle x y w) (by linarith))
def spanV(g:Ratio c f):ℝ:=g.count.val
lemma period_one : 1≤spanV g:=by unfold spanV; exact_mod_cast g.count.property
lemma span_pos : 0< spanV g:=zero_lt_one.trans_le period_one
lemma hleft(x y:Site f): (separation (g.parent x) (g.parent y):ℝ)≤separation x y/spanV g+1:=by
 have hh:spanV g* ↑(separation (g.parent x) (g.parent y)) ≤ separation x y + spanV g:=by unfold spanV; exact_mod_cast Corona.foreshorten g x y
 rw [show (_:ℝ) /spanV g+1=(separation x y + spanV g)/spanV g by rw [add_div,div_self (show spanV g≠0 from span_pos.ne')]]; apply (le_div_iff₀ span_pos).2; rw [mul_comm]; exact hh
namespace Rails
variable {Λ:Ps f→Ps c→ℝ}(h:0<a)(k:0<A)(P:Rails g A a Λ)
include h P
lemma shift (x:Site c)(v:Ps f){s:ℝ}(p:↑(separation x (g.parent v.1))≤s): ∑ y: Ps c,Faro a x y.1*‖Λ v y‖≤ Real.exp (a*s)*(A/spanV g^2):=by
 apply le_trans _ (mul_le_mul_of_nonneg_left (P.rate v) (Real.exp_pos (a*s)).le); rw [mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (Faro_comp h.le p) (norm_nonneg _)
lemma sprint (x y:Site f)(u:Walk)(p:PlaqAxes)(b:ℝ)(hz:(separation x y:ℝ)+u.length≤b): ∑ z:Ps c, Faro a (g.parent x) z.1 * ‖Λ (stop y u,p) z-Λ (y,p) z‖≤ u.length * (Real.exp (a*(b/spanV g+1))*(A/spanV g^3)):=by
 induction u generalizing y with
 | nil => simp [stop]
 | cons d w H=>
   let t:= y+d.vec; let V:= b/spanV g + 1; let z:=g.parent x; let B:= Real.exp (a*V)*(A/spanV g^3)
   have hu: (separation x t:ℝ) ≤ ↑(separation x y)+1:=by exact_mod_cast (separation_triangle x y t).trans (Nat.add_le_add_left (small y d) _)
   simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hz
   have ht:(separation x t:ℝ)+w.length≤b:=by linarith
   have hk:0≤spanV g:=span_pos.le
   have hx:(separation z (g.parent t):ℝ)≤ V:=by apply (hleft ..).trans; unfold V; gcongr; have hx: 0≤(w.length:ℝ):=Nat.cast_nonneg _; linarith
   have hp:(separation z (g.parent y):ℝ)≤V:=by apply (hleft ..).trans; unfold V; gcongr; have hx: 0≤(w.length:ℝ):=Nat.cast_nonneg _; linarith
   have he(u:Site f)(hl:(separation z (g.parent u):ℝ)≤V): ∑ i : Ps c, Faro a z i.1* ‖Λ (u+step d.dir,p) i-Λ (u,p) i‖ ≤ B:=by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (P.gap (u,p) d.dir) (Real.exp_pos (a*V)).le); rw [mul_sum]; exact sum_le_sum fun i _=> (mul_le_mul_of_nonneg_right (Faro_comp h.le hl) (norm_nonneg _)).trans_eq (mul_assoc ..)
   have hv: ∑ i:Ps c, Faro a z i.1*‖Λ (t,p) i-Λ (y,p) i‖ ≤ B:=by
      by_cases k:d.neg
      · have hx':t+step d.dir=y:=by simp [t,Step.vec,k]
        simp_rw [norm_sub_rev (Λ (t,p) _)]; simpa only [hx'] using he t hx
      simpa [t,Step.vec,k,if_false] using he y hp
   calc
    _ ≤ (∑ i:Ps c, Faro a z i.1* ‖Λ (stop t w,p) i-Λ (t,p) i‖)+∑ i: Ps c,Faro a z i.1*‖Λ (t,p) i-Λ (y,p) i‖ :=by rw [←sum_add_distrib]; exact sum_le_sum fun i _=> (mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) (Real.exp_pos _ |>.le)).trans_eq (mul_add ..)
    _ ≤ _:= (add_le_add (H t ht) hv).trans_eq (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,B, V, z])
end Rails
end YM.CF.Font
