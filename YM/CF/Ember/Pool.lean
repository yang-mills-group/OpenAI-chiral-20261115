import YM.CF.Ember.Lore
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator
variable {ι:Type*}{t:Tax ι}
structure Move (t:Tax ι)(p:ι→ℂ→ Momentum):Prop where
 act: Act t 1 p
 hit : ∀ a:ℝ,0<a→ ∃ b:ℝ,0<b∧∀ i,∀ z:ℂ,‖z‖<b→p i z∈cube a
namespace Move
variable {p:ι→ℂ→Momentum}(P:Move t p){f:ι→Momentum→ℂ}(h:Moderate (fun _:ι=>1) f)
include P h
lemma plunge: Act t 0 fun i z=> f i (p i z):=by
 obtain ⟨a,C,ha,hc,H⟩:=h; obtain ⟨b,hb,B⟩:= P.hit a ha; obtain ⟨c,A,v,w,F⟩:=P.act; refine ⟨min b c,C,lt_min hb v,hc,fun i z hz=>?_⟩; have hp:=B i z (hz.trans_le (min_le_left ..)); obtain ⟨u,e⟩:=F i z (hz.trans_le (min_le_right ..)); exact ⟨((H i).hol _ hp).comp z u, by simpa using (H i).bound _ hp⟩
omit P h in
private lemma flash {a C:ℝ}{f:Momentum→ℂ}{x:Momentum}(hc:0<C)(ha:0<a)(S:SafeCube (2*a) C f)(hf:f 0=0)(hx:x∈cube (2*a)): ‖f x‖≤ C/a*‖x‖:=by
 have he:ball (0:Momentum) a⊆ cube (2*a):=by simpa [two_mul] using ball_inside_cube (η:=2*a) (cube_zero a ha)
 by_cases h:‖x‖<a
 · have hm:Set.MapsTo f (ball 0 a) (closedBall (f 0) C):=by intro x hx; rw [hf]; exact mem_closedBall_zero_iff.mpr (S.bound _ (he hx))
   have h:=Complex.dist_le_div_mul_dist_of_mapsTo_ball (fun z hz=>(S.hol _ (he hz)).differentiableWithinAt) hm (mem_ball_zero_iff.mpr h)
   rwa [hf,dist_zero_right,dist_zero_right] at h
 exact (S.bound _ hx).trans (by rw [div_mul_eq_mul_div,le_div_iff₀ ha]; exact mul_le_mul_of_nonneg_left (le_of_not_gt h) hc.le)
lemma freeze (he:∀ i,f i 0=0): Act t 1 fun i z=> f i (p i z):=by
 obtain ⟨a,C,ha,hc,H⟩:=h; let A:=a/2; have hy:0<A:=by unfold A; positivity
 obtain ⟨b,hb,B⟩:=P.hit a ha; obtain ⟨c,D,hk,hd,K⟩:=P.act
 refine ⟨min b c,C/A*D,lt_min hb hk,by positivity,fun i z hz=>?_⟩; have hp:=B i z (hz.trans_le (min_le_left ..)); obtain ⟨u,w⟩:=K i z (hz.trans_le (min_le_right ..))
 have h:2*A=a:=by unfold A; ring
 exact ⟨((H i).hol _ hp).comp z u,(flash hc hy (by rw [h]; simpa using H i) (he i) (h.symm ▸ hp)).trans (by rw [mul_assoc (C/A) D]; gcongr)⟩
omit P h in
private lemma frozen {a C:ℝ}{f:Momentum→ℂ}{x:Momentum}(hc:0<C)(ha:0<a)(S:SafeCube (2*a) C f)(h:f 0=0)(hv:∀ p:Momentum, HasDerivAt (fun z:ℂ=> f (z • p)) 0 0)(hx:x∈cube (2*a)): ‖f x‖≤ C/a^2*‖x‖^2:=by
 by_cases hw:x=0
 · simp [hw,h]
 let r:= ‖x‖; have he:0<r:=norm_pos_iff.mpr hw
 by_cases v:r<a
 · let A:=a/r; have hp:1<A:= (one_lt_div he).mpr v
   let F(z:ℂ):=f (z • x); let P:=dslope F 0
   have hs:ball (0:Momentum) a⊆cube (2*a):=by simpa [two_mul] using ball_inside_cube (η:=2*a) (cube_zero a ha)
   have ht z (w:z∈ ball (0:ℂ) A): z • x∈cube (2*a):=by apply hs; rw [mem_ball_zero_iff,norm_smul]; exact (lt_div_iff₀ he).mp (mem_ball_zero_iff.mp w)
   have hg:DifferentiableOn ℂ F (ball 0 A):=fun z w=> ((S.hol _ (ht z w)).comp z (show DifferentiableAt ℂ (fun z:ℂ=>z • x) z from by fun_prop)).differentiableWithinAt
   have he0:Set.MapsTo F (ball 0 A) (closedBall (F 0) C):=fun z w=>by rw [show F 0=0 by simp [F,h]]; exact mem_closedBall_zero_iff.mpr (S.bound _ (ht z w))
   have hm:P 0=0:=by rw [show P 0=deriv F 0 from dslope_same ..]; exact (hv x).deriv
   have hn : Set.MapsTo P (ball 0 A) (closedBall (P 0) (C/A)) :=by intro z w; rw [hm]; exact mem_closedBall_zero_iff.mpr (Complex.norm_dslope_le_div_of_mapsTo_ball hg he0 w)
   have hz := Complex.dist_le_div_mul_dist_of_mapsTo_ball ((Complex.differentiableOn_dslope (ball_mem_nhds _ (zero_lt_one.trans hp))).mpr hg) hn (mem_ball_zero_iff.mpr (show ‖(1:ℂ)‖<A by simpa)); change dist (P 1) (P 0)≤ _ at hz
   rw [hm,dist_zero_right,dist_zero_right,norm_one,mul_one] at hz; have hl:P 1=f x:=by unfold P; rw [dslope_of_ne _ one_ne_zero,slope_def_module]; simp [F,h]
   rw [hl] at hz; exact hz.trans_eq (by change C/(a/r)/(a/r)= C/a^2*r^2; field_simp)
 push Not at v; exact (S.bound _ hx).trans (by rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos ha _)]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le v 2) hc.le)
lemma daze (he:∀ i,f i 0=0)(hv:∀ i,∀ x:Momentum,HasDerivAt (fun z:ℂ=> f i (z • x)) 0 0): Act t 2 fun i z=> f i (p i z):=by
 obtain ⟨a,C,ha,hc,H⟩:=h; let A:=a/2; have hy:0<A:=by unfold A; positivity
 obtain ⟨b,hb,B⟩:=P.hit a ha; obtain ⟨c,D,hk,hd,K⟩:=P.act
 refine ⟨min b c,C/A^2*D^2,lt_min hb hk,by positivity,fun i z hz=>?_⟩; have hp:=B i z (hz.trans_le (min_le_left ..)); obtain ⟨u,w⟩:=K i z (hz.trans_le (min_le_right ..))
 have h:2*A=a:=by unfold A; ring
 refine ⟨((H i).hol _ hp).comp z u,(frozen hc hy (by rw [h]; simpa using H i) (he i) (hv i) (h.symm ▸ hp)).trans ?_⟩
 refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) w 2) (by positivity :0≤ C/A^2)).trans_eq ?_; rw [zpow_one,_root_.zpow_ofNat]; ring
end Move
end YM.CF.Ember
