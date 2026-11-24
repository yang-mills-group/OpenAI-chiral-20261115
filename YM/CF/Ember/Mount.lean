import YM.CF.Ember.Can
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{t:Tax ι}
lemma Move.left {x:ι→ Momentum}(H:∀ i,x i∈baseCube){A:ℝ}(ha:0<A)(e:∀ i,‖x i‖≤ A*t.r i) : Move t fun i _=> x i :=by
 refine ⟨⟨1,A,one_pos,ha,fun i z _=>⟨differentiableAt_const _,by simpa using e i⟩⟩,fun a h=>⟨1,one_pos,fun i z _=> mem_cube_real (base_subset_realCube h (H i)) h⟩⟩
lemma Move.add {p q:ι→ℂ→Momentum}(P:Move t p)(h:Act t 1 q)(e:∀ i,q i 0=0):Move t fun i z=> p i z+q i z :=by
 obtain ⟨b,C,hb,hc,B⟩:= h.dam
 refine ⟨P.act.add h,fun a ha=>?_⟩
 obtain ⟨d,hd,D⟩:=P.hit (a/2) (by positivity); let E:=max t.cap 1; have he:0<E:=lt_max_of_lt_right one_pos; have hE i:t.r i≤E:= (t.hold i).trans (le_max_left ..)
 refine ⟨min (a/(2*C*E)) (min b d),lt_min (by positivity) (lt_min hb hd),fun i z hz=>?_⟩
 have hx:= hz.trans_le (min_le_right ..)
 apply ball_inside_cube (D i z (hx.trans_le (min_le_right ..))); rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left]
 have hu:= B i z (mem_ball_zero_iff.mpr (hx.trans_le (min_le_left ..))); rw [e,sub_zero,zpow_one] at hu; refine hu.trans_lt ?_; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE i) hc.le) (norm_nonneg z)).trans_lt (lt_of_lt_of_le (mul_lt_mul_of_pos_left (hz.trans_le (min_le_left ..)) (mul_pos hc he)) (le_of_eq (by field_simp; ring)))
def spark (a:Axis)(z:ℂ): Momentum:= z • (Lattice.step a)
lemma spark_star(a z): star (spark a z)=spark a (star z):=by unfold spark; rw [star_smul]; congr 1; ext1 i; by_cases p:i=a <;> simp [p]
lemma spark_plus(a:Axis)(z:ℂ): spark a (2*z)= spark a z+spark a z:=by rw [two_mul]; unfold spark; rw [add_smul]
@[simp] lemma spark_origin(a:Axis): spark a 0=0:=by rw [spark,zero_smul]
def river (x:Gaia) : Momentum := axes (exileE x)
@[simp] lemma riv_phys (x:Gaia): star (river x)=river x:=tmap_physical _
lemma enter{p:Gaia}(h:p∈boundsEarth): river p∈ baseCube:=by refine ⟨riv_phys p,cradleFront p.ofLp h⟩
lemma boundH(p:Gaia): ‖river p‖≤ ‖p‖ :=by
 rw [pi_norm_le_iff_of_nonneg (norm_nonneg p)]; intro i; change ‖((p i:ℝ):ℂ)‖ ≤‖p‖; rw [Complex.norm_real]; exact (norm_le_pi_norm (exileE p) i).trans (orbit_at _)
lemma principal_in (t:Tax ι)(x:ι→ Gaia)(e:∀ i,t.r i=‖x i‖)(h:∀ i,x i∈boundsEarth): Move t fun i _=> river (x i) := Move.left (fun i=>enter (h i)) one_pos fun i=>by rw [one_mul,e]; exact boundH _
lemma sparkBud(t:Tax ι){c:ι→ℂ→ℂ}(h:Act t 1 c)(a:Axis):Act t 1 fun i z=> spark a (c i z):= h.smul (Act.anchor t (step a))
def raf(t:Tax ι)(i:ι)(z:ℂ):= (t.r i:ℂ)*z
lemma raft(t:Tax ι): Act t 1 (raf t):=by
 refine ⟨1,1,one_pos,one_pos,fun i z h=>⟨by unfold raf; fun_prop,?_⟩⟩; unfold raf; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (t.pos i).le,one_mul,zpow_one]; exact mul_le_of_le_one_right (t.pos i).le h.le
lemma kinder {x:ι→ Gaia}(e:∀ i,t.r i=‖x i‖)(h:∀ i,x i∈boundsEarth)(a:Axis):Move t fun i z=>river (x i)+spark a (2*raf t i z):= Move.add (principal_in t x e h) (sparkBud t (Act.lit (raft ..) 2) a) (fun i=>by simp [raf])

abbrev TestX := Momentum×Momentum
structure SkinH {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E](η C:ℝ)(f:TestX→E):Prop where
 rad:0<η
 pos:0<C
 hol(x:TestX)(p:x.1∈ cube η)(q:x.2∈cube η):DifferentiableAt ℂ f x
 fee(x:TestX)(p:x.1∈cube η)(q:x.2∈cube η): ‖f x‖≤ C
namespace Move
variable {p q:ι→ℂ→Momentum}(P:Move t p)(Q:Move t q){E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]{η C:ℝ}{f:ι→TestX→E}(S:∀ i,SkinH η C (f i))(h:0<η)(k:0<C)
include P Q S h k
lemma bend: Act t 0 fun i z=> f i (p i z,q i z):=by
 obtain ⟨a,ha,A⟩:= P.hit η h; obtain ⟨b,hb,B⟩:= Q.hit η h; obtain ⟨c,Y,w,y,H⟩:= P.act; obtain ⟨d,V,r,x,G⟩:=Q.act
 refine ⟨min (min a b) (min c d),C,lt_min (lt_min ha hb) (lt_min w r),k,fun i z hz=>?_⟩
 have he:= hz.trans_le (min_le_left ..); have hx:= hz.trans_le (min_le_right ..); have ht:= A i z (he.trans_le (min_le_left ..)); have hg:=B i z (he.trans_le (min_le_right ..)); have hh:= H i z (hx.trans_le (min_le_left ..)); have hz:=G i z (hx.trans_le (min_le_right ..)); exact ⟨((S i).hol (p i z,q i z) ht hg).comp z (hh.1.prodMk hz.1),by simpa using (S i).fee (p i z,q i z) ht hg⟩
lemma sand : Act t 1 fun i z=> f i (p i z,q i z)-f i 0:=by
 obtain ⟨a,ha,A⟩:= P.hit η h; obtain ⟨b,hb,B⟩:= Q.hit η h; obtain ⟨c,Y,w,y,H⟩:= P.act; obtain ⟨d,V,r,x,G⟩:=Q.act; let μ:=η/2; have hu:0<μ:=by unfold μ; positivity
 have hk(p : TestX)(h':p∈ ball (0:TestX) μ): p.1∈cube η ∧ p.2∈cube η:=by
    have ht:‖p‖<μ:= mem_ball_zero_iff.mp h'; rw [Prod.norm_def,max_lt_iff] at ht
    have hx:η-μ=μ:=by unfold μ; ring
    have he:=ball_inside_cube (η:=η) (cube_zero μ hu); rw [hx] at he; exact ⟨he (mem_ball_zero_iff.mpr ht.1), he (mem_ball_zero_iff.mpr ht.2)⟩
 have hm:=(hk 0 (mem_ball_self hu)); let D:=2*C/μ
 have hv(i:ι)(p:TestX)(hx:p.1∈cube η)(hy:p.2∈cube η): ‖f i p-f i 0‖≤ D*‖p‖:=by
    have hh(x:TestX)(hx:x.1∈cube η)(hy:x.2∈cube η): ‖f i x-f i 0‖≤2*C:= (norm_sub_le ..).trans ((add_le_add ((S i).fee x hx hy) ((S i).fee _ hm.1 hm.2)).trans_eq (two_mul C |>.symm)) -- fix
    by_cases he: p∈ ball (0:TestX) μ
    · have hD:=Complex.dist_le_div_mul_dist_of_mapsTo_ball (fun z hz=>((S i).hol z (hk _ hz).1 (hk _ hz).2).differentiableWithinAt) (fun x hx=>show f i x∈closedBall (f i 0) (2*C) from mem_closedBall.mpr (by rw [dist_eq_norm]; exact hh _ (hk x hx).1 (hk x hx).2)) he
      rw [dist_eq_norm,dist_zero_right] at hD; exact hD
    apply (hh p hx hy).trans; have ht:= le_of_not_gt (mt mem_ball_zero_iff.mpr he); unfold D; rw [div_mul_eq_mul_div,le_div_iff₀ hu]; gcongr
 refine ⟨min (min a b) (min c d), D*(Y+V),lt_min (lt_min ha hb) (lt_min w r),by unfold D; positivity,fun i z hz=>?_⟩
 have he:= hz.trans_le (min_le_left ..); have hx:= hz.trans_le (min_le_right ..); have ht:= A i z (he.trans_le (min_le_left ..)); have hg:=B i z (he.trans_le (min_le_right ..)); have hh:= H i z (hx.trans_le (min_le_left ..)); have hl:=G i z (hx.trans_le (min_le_right ..))
 refine ⟨(((S i).hol (p i z,q i z) ht hg).comp z (hh.1.prodMk hl.1)).sub_const _,(hv _ _ ht hg).trans ?_⟩; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by unfold D; positivity); rw [Prod.norm_def, add_mul]; exact max_le (hh.2.trans (le_add_of_nonneg_right ((norm_nonneg _).trans hl.2))) (hl.2.trans (le_add_of_nonneg_left ((norm_nonneg _).trans hh.2)))
end Move
end YM.CF.Ember
