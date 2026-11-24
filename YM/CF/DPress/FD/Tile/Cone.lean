import YM.CF.DPress.FD.Tile.Collar
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Metric Filter SU MeasureTheory Ramp Row Frame
open scoped Topology BigOperators NNReal ENNReal Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {I K:Type*}[Fintype I][Fintype K]{m:ℕ}
namespace Warm
abbrev Skip (F:ArrayF K)(D:Finset K):Prop:= ∀ i∈D,F i=0
variable {U:Finset I} (H:U.Nonempty){x y:Ramp I m}(p:0<m) (s:K)
def prick (F:ArrayF K)(k:K)(a b:ℝ):ArrayF K:=update (b • F) k (a • (1:Key))
lemma prick_y (F:ArrayF K)(h:F s=0) : prick F s 0 1=F:= by rw [prick,one_smul,zero_smul,←h,update_eq_self]
lemma prick_ok (a b:ℝ)(wa:a∈Row.budget)(wb:b∈Row.budget) (t:a=1∨b=1){F:ArrayF K} (h:F∈Frame K) (hx:F s=0) : prick F s a b∈ Frame K:=by
 unfold prick; constructor
 · intro i; by_cases p:i=s; · rw [p,update_self]; exact Row.swell (fund_one ▸Row.plant 1) wa
   rw [update_of_ne p]; exact Row.swell (h.1 i) wb
 rcases t with t|t; · rw [t]; exact ⟨s,1,by simp [fund_one]⟩
 obtain ⟨i,t',g⟩:=h.2; have hi:i≠s:=by intro t; rw [t,hx] at g; exact (ne_of_gt (Row.bloom t'|>.symm ▸ Row.alive)) (by rw [g,norm_zero])
 rw [t,one_smul]; exact ⟨i,t',by rw [update_of_ne hi,g]⟩
private lemma point_cost {F G:ArrayF K}(g:G∈ Frame K)(a b c d:ℝ)(wb:b ≤ 1)(we:0 ≤ b)(K' L:ℝ)(ha:|a-c|≤ K')(hc:|b-d|≤ K')(t:dist F G ≤ L):dist (prick F s a b) (prick G s c d)≤ K'*Row.rad+L:=by
 have ht:0≤L:=dist_nonneg.trans t; have hv:0≤K':= (abs_nonneg _).trans ha; refine (dist_pi_le_iff (add_nonneg (mul_nonneg hv Row.alive.le) ht)).mpr fun i=>?_ ; unfold prick; by_cases h:i=s; · rw [h,update_self,update_self,dist_eq_norm,←sub_smul,norm_smul]; exact (mul_le_mul_of_nonneg_right ha Row.alive.le).trans (le_add_of_nonneg_right ht)
 rw [update_of_ne h,update_of_ne h]; change dist (b • F i) (d • G i) ≤ _; refine (dist_triangle _ (b • G i) _).trans ?_; rw [add_comm (dist _ _),dist_smul₀,Real.norm_of_nonneg we,dist_eq_norm,←sub_smul,norm_smul]; refine add_le_add (mul_le_mul hc (Row.age (g.1 i)) (norm_nonneg _) hv) ?_; exact (mul_le_of_le_one_left dist_nonneg wb).trans ((dist_le_pi_dist ..).trans t)
variable (G:Ramp I m→ArrayF K) {V:Finset K}{a:ℝ}
abbrev cones(x:Ramp I m):=prick (G (Ramp.peg U H x)) s (Ramp.gain U H x) (Ramp.lower U H x)
local notation "coverX"=> (boundary U)
include p H
lemma entry(t:x∈ boundary U)(h:G x s=0): cones H s G x=G x:=by rw [cones,(Ramp.begin_ U H x p t).1,(Ramp.begin_ U H x p t).2,peg_l U H x p t,prick_y s (G x) h]
lemma coat (t:Shape (boundary U) G)(v: ∀ i∈ boundary U,G i s=0)(q:x∈facet U): cones H s G x∈ Frame K := by
 obtain ⟨u,l,r⟩:=Ramp.pay U H x; by_cases hx:2*low U H x≤m; · exact prick_ok s _ _ u l r (t (peg_H U H x p q hx)) (v _ (peg_H U H x p q hx)) -- can't infer p? pass
 obtain ⟨a,b⟩:= Ramp.cut U H x p (lt_of_not_ge hx); unfold cones prick; rw [a,b,zero_smul,one_smul]; refine ⟨fun i=>?_,⟨s,1,by simp [fund_one]⟩⟩; by_cases h:i=s; rw [h,update_self]; exact fund_one ▸ Row.plant 1; rw [update_of_ne h]; exact Row.nil
lemma hem {V:Finset K}(h:∀ i∈ boundary U,Skip (G i) V)(v:s∉ V)(q:x∈ facet U):Skip (cones H s G x) V:=by
 intro i u; have hi:i≠s:=fun k=>v (k ▸ u); unfold cones prick; rw [update_of_ne hi,Pi.smul_apply]; by_cases t:2*low U H x ≤ m; · rw [h _ (peg_H U H x p q t) i u,smul_zero]
 rw [(cut U H x p (lt_of_not_ge t)).2,zero_smul]
private lemma pillar (t:Shape (boundary U) G)(w:2*low U H x > m)(k:2*low U H y≤m)(q:y∈ facet U):dist (cones H s G x) (cones H s G y) ≤ 4*Row.rad * δR x y:=by
 obtain ⟨l,u⟩:= Ramp.cut U H x p w; let g:=G (Ramp.peg U H y); unfold cones prick; rw [l,u,show (0:ℝ) • G (Ramp.peg U H x)=(0:ℝ) • g by rw [zero_smul,zero_smul]]; -- point_cost with second b; orientation need b=0 helps, F=g
 have ht:= gain_cost U H x y; rw [l,u] at ht; refine (point_cost s (F:=g) (show g ∈ Frame K from t (peg_H U H y p q k)) _ _ _ _ zero_le_one le_rfl _ _ ht.1 ht.2 (dist_self g|>.le)).trans_eq ?_; simp only [add_zero]; ring
lemma widen_cost (h:Shape (boundary U) G)(p':Speed (boundary U) G a)(sA:0≤a):Speed (facet U) (cones H s G) (4*rad+4*a):=by
 intro x k y h'; rw [add_mul]; have hx:0≤ 4*a*δR x y:= mul_nonneg (mul_nonneg (by positivity) sA) δp; have hx':= Row.alive; by_cases t:2*low U H x>m <;> by_cases r:2*low U H y>m
 · rw [show cones H s G x= cones H s G y from ?_,dist_self]; exact add_nonneg (mul_nonneg (by positivity) δp) hx
   unfold cones prick; rw [(cut U H x p t).1,(cut U H x p t).2,(cut U H y p r).1,(cut U H y p r).2,zero_smul,zero_smul]
 · exact (pillar H p s G h t (le_of_not_gt r) h').trans (le_add_of_nonneg_right hx)
 · rw [dist_comm]; exact (pillar H p s G h r (le_of_not_gt t) k).trans (by rw [δs]; exact le_add_of_nonneg_right hx) -- tune δs macro rewrite
 let hy:= peg_H U H y p h' (le_of_not_gt r); let hu:=gain_cost U H x y; let pk:= (Ramp.pay U H x).2.1; refine (point_cost s (h hy) _ _ _ _ pk.2 pk.1 (4*δR x y) _ hu.1 hu.2 (le_trans (p' _ (peg_H U H x p k (le_of_not_gt t)) _ hy) (mul_le_mul_of_nonneg_left (thick U H x y) sA))).trans_eq ?_; ring
end Warm
end YM.CF.DPress.FD
