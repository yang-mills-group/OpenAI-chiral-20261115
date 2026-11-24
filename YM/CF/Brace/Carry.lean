import YM.CF.Brace.Shine
/-! Pairing transfer, coarse values lifted on refined gauge sites via exact local routes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory Tulip Peaks Rush
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
def rankS(d: ℕ):ℕ:= 4*d+d*(4*(2*d+1))+1
def billK(d:ℕ)(e p:ℝ):ℝ:= 8*(rankS d:ℝ)^2*e+(4*(2*(d:ℝ)+1))*e+(4*(2*(d:ℝ)+1))*p
lemma warp (w:Walk)(x:Fend N):stop ((ratio G).embed x) (sail G w)=(ratio G).embed (stop x w):=by
 induction w generalizing x with| nil=>rfl| cons a l ih=> rw [show sail G (a::l)=leapK G a++sail G l from rfl,stop_append,stop_s,ih]; rfl
lemma walks (w:Walk)(x:Fend N)(U: Nom N P)(e:ℝ)(h:JointB G U e): Cube.cmp firstF (travel U.1 ((ratio G).embed x) (sail G w)) (travel U.2 x w) ≤ w.length*e := by
 induction w generalizing x with
 | nil=> change Cube.cmp _ 1 1≤_; rw [cmp_id]; simp
 | cons a l ih=>
   rw [show sail G (a::l)=leapK G a++sail G l from rfl,travel_append,stop_s,travel];
   apply (cmp_triangle firstF _ (a.read U.2 x*travel U.1 ((ratio G).embed (x+a.vec)) (sail G l)) _).trans; rw [cmp_right,cmp_left,List.length_cons]; push_cast; rw [add_mul,one_mul,add_comm (↑l.length*e)]
   exact add_le_add (ratio_cmp _ _ _ _ _ h) (ih _) -- tune
lemma uprightL(o:Site P)(l w:Walk)(t:ℕ)(h:stop o l=stop o w)(p:l.length≤t)(hp:w.length≤t)(hw:2*t<P.val): stop (0:Cover) l=stop 0 w:=by
 let A:=stop (0:Cover) l; let B:=stop (0:Cover) w
 have he: wrap P A=wrap P B:=add_left_cancel ((right_to o l).symm.trans (h.trans (right_to o w)))
 have hx(l:Walk)(p:l.length≤t):lift (wrap P (stop (0:Cover) l))=stop 0 l:=by
   rw [lift_eq_iff]; refine ⟨rfl,fun i=>?_⟩; have ht: ((stop (0:Cover) l) i).natAbs≤t:=by simpa using (coord_size 0 l i).trans p; -- tune
   omega
 exact (hx l p).symm.trans ((congrArg lift he).trans (hx w hp))
lemma marchG(U: Nom N P)(e p:ℝ)(h:JointB G U e)(he:0≤ e)(x:Stun N)(hk:Slow U.2 (hook x) p)(hq:0<p)(m:Fend P)(i:Axis)(hr: 2*rankS G.count.val <(More P).val):
 ‖turn (U.1 (m,i)) (hook (ascend G x U.1) (m+step i))-hook (ascend G x U.1) m‖≤ billK G.count.val e p:=by
 let n:=m+step i; let T:=ratio G; let r:=T.parent m; let s:= T.parent n; let w:=march r s 1; let A:Walk:=posDir i::dart G n; let B:=dart G m++ sail G w
 have hg(x:Fend P):stop x (dart G x)=T.embed (T.parent x):=Cube.arrive ..
 have hM:stop m A=stop m B:=by rw [show stop m A=stop n (dart G n) from rfl, hg, show B=_++_ from rfl,stop_append,hg,warp,show stop r w=s from Cube.arrive ..];
 let d:=G.count.val
 have ht:w.length≤4*(2*d+1):=by apply march_len; rw [separation_comm]; exact parentsK T m i
 have ha:A.length≤ rankS d:=by have he:(dart G n).length≤4*d:=dartK ..; unfold A rankS; rw [List.length_cons]; omega
 have hb:B.length≤rankS d:=by unfold B rankS; rw [List.length_append,walk_len]; exact (Nat.add_le_add (dartK ..) (Nat.mul_le_mul_left _ ht)).trans (Nat.le_add_right ..)
 have hl:= uprightL m A B _ hM ha hb hr
 let y:= hook x s; let z:= hook x r; let V:=travel U.1 m (dart G m)
 have hY: turn (U.1 (m,i)) (hook (ascend G x U.1) (m+step i))=turn (travel U.1 m A) y:=by unfold A; rw [travel,Step.pos_read,Step.vec_pos,turn_seq]; rfl
 rw [hY]; change ‖_-turn V z‖≤ _
 have hk1: ‖turn (travel U.1 m A) y-turn (travel U.1 m B) y‖ ≤ 8*(rankS d:ℝ)^2*e:=by
   apply (turn_price ..).trans; rw [show ‖y‖=1 from hookN ..,mul_one]; apply (near_hop he h.fg.1 m A B hl).trans; rw [←add_mul]; refine mul_le_mul_of_nonneg_right ?_ he
   nlinarith [pow_le_pow_left₀ (by positivity) (show (A.length:ℝ)≤rankS d by exact_mod_cast ha) 2, pow_le_pow_left₀ (by positivity) (show (B.length:ℝ)≤rankS d by exact_mod_cast hb) 2]
 apply (norm_sub_le_norm_sub_add_norm_sub _ (turn (travel U.1 m B) y) _).trans
 unfold billK; rw [add_assoc]; apply add_le_add hk1 _; unfold B; rw [travel_append,hg, turn_seq, show travel U.1 m (dart G m)=V from rfl, ←turn_sub,turn_norm];
 apply (norm_sub_le_norm_sub_add_norm_sub _ (turn (travel U.2 r w) y) _).trans; apply add_le_add
 · apply (turn_price ..).trans; rw [show ‖y‖=1 from hookN ..,mul_one]; exact (walks G w r U e h).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) he)
 have he := stroll_h U.2 _ p hk w r; rw [show stop r w=s from Cube.arrive ..] at he; exact he.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) hq.le)
def accordL (x:Nom N P)(v:Stun N): Sew N P:= (x,ascend G v x.1,v)
lemma guild (U:Nom N P)(e p d: ℝ)(h:JointB G U e)(he:0<e)(he': e≤d)(x:Stun N)(hp:Slow U.2 (hook x) p)(hq:0<p)(hv:p≤d)(hr:2*rankS G.count.val<(More P).val)(hk:billK G.count.val e p< d): Gild G (accordL G U x) d:=by
 refine ⟨⟨h.fg.shrink he',h.cg.shrink he', fun i=>(h.follow i).trans he'⟩,fun m i=>(marchG G U e p h he.le x hp hq m i hr).trans_lt hk, fun i t=>(hp i t).trans_le hv,?_⟩
 intro i; change ‖hook (ascend G x _) _-_‖<_; unfold hook; rw [adel]; change ‖(x i).val-(x i).val‖<_; rw [sub_self,norm_zero]; exact he.trans_le he'
omit G
lemma kip (b:ℕ)(d:ℝ)(p:0<d):∃ e:ℝ,0<e∧ e<d∧ billK b e e< d :=by
 have hf:Continuous (fun i=>billK b i i):=by unfold billK; fun_prop
 have he : ∀ᶠ i in 𝓝[>] (0:ℝ), (0:ℝ) < i∧ i<d∧billK b i i<d:=Eventually.and self_mem_nhdsWithin (Eventually.and (nhdsWithin_le_nhds (gt_mem_nhds p)) (hf.continuousAt.continuousWithinAt (gt_mem_nhds (show billK b 0 0< d by simpa [billK])))) -- tune
 exact he.exists
end YM.CF.Brace
