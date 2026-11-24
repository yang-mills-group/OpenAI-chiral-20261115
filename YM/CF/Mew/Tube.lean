import YM.CF.Mew.Lace
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Mew
open Function Set Metric Filter Complex MeasureTheory Finset
open scoped Topology ContDiff BigOperators Matrix
variable {I E A J :Type*}[Fintype I][DecidableEq I][MeasurableSpace A][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][Fintype J][DecidableEq J]
variable(f:Key I→ E)(u:River f)(S:Finset I)(v:Key I)(x:Key J→Key I){a:ℝ}(hp:∀ i,River (fun y:Key J=>x y i))(ρ:a<1)(H:∀ y∈hill J,∀ i, ‖x y i‖ ≤ a)
abbrev feed_K (i:I)(v:Key I)(x:ℂ):= ∫ t:ℝ,(homeB t*(homeB t-x)⁻¹) • f (Function.update v i (homeB t)) ∂sky
include u in
lemma ca_uc (i:I)(p:v∈hill I)(x:ℂ)(z:x∈rim): f (Function.update v i x)= feed_K f i v x:=by
 let g(t:ℝ):=(homeB t*(homeB t-x)⁻¹) • f (Function.update v i (homeB t)); let A:=f (update v i x); let G:=∫ t,g t∂sky
 have ht:= (u.circle p i).circleIntegral_sub_inv_smul z; have he(t:ℝ): deriv (circleMap 0 1) t • ((homeB t-x)⁻¹ • f (update v i (homeB t)))=(Complex.I • g t):=by rw [deriv_circleMap,smul_smul]; unfold g; rw [smul_smul]; congr 1; unfold homeB; ring
 change (∫ t in 0..roll,deriv (circleMap 0 1) t • ((homeB t-x)⁻¹ • f (update v i (homeB t))))=(2*Real.pi* Complex.I) • A at ht
 simp_rw [he] at ht; rw [intervalIntegral.integral_smul, intervalIntegral.integral_of_le roll_pos.le,show 2*(Real.pi:ℂ)* Complex.I= Complex.I*(roll:ℝ) from (by unfold roll; push_cast; ring),mul_smul] at ht
 let P:=∫ t in Ioc 0 roll, g t; have h:P=roll • A:=smul_right_injective E Complex.I_ne_zero ht
 change A=G; unfold G sky; rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.mpr roll_pos).le]; change A=roll⁻¹ • P; rw [h,inv_smul_smul₀ roll_pos.ne']
-- jet increments analytic interpolation whenever image kept inside.L measures probability. support partial summation on arbitrary faces.
abbrev starp (v:Key I)(i:I)(z:ℂ)(t:ℝ):= (homeB t-z)⁻¹ • f (Function.update v i (homeB t))
abbrev Jtube (v:Key I)(i:I)(z:ℂ):= ∫ t,starp f v i z t∂sky
lemma tourB {α:Type*}[NormedAddCommGroup α][NormedSpace ℂ α](f:ℝ→α)(p:Continuous f): Integrable f sky:=by let t:=Icc 0 roll; let h: IntegrableOn f t:=p.continuousOn.integrableOn_compact isCompact_Icc; unfold sky; exact (h.mono_set Ioc_subset_Icc_self).smul_measure ENNReal.ofReal_ne_top
include u
lemma pace_u (i:I)(p:v∈hill I)(z:ℂ)(h:z∈rim) : Continuous (starp f v i z):=by
 have hp(t):homeB t - z≠0:=by intro hx; have hx':= (home_q t); rw [sub_eq_zero.mp hx] at hx'; exact (mem_ball_zero_iff.mp h).ne hx'
 exact Continuous.smul (((continuous_circleMap _ _).sub continuous_const).inv₀ hp) (u.shore.comp_continuous ((under_r i v).comp (continuous_circleMap ..)) (fun t=> fill_I p i (homeC _)))
lemma fan_I (V:Key I)(i:I)(p:V∈hill I)(x:ℂ)(z:x∈rim): f (Function.update V i x)=f (Function.update V i 0)+x • (Jtube f V i x):=by
 rw [ca_uc f u _ i p x z,ca_uc f u _ i p 0 (mem_ball_self zero_lt_one)]; unfold feed_K Jtube; rw [←integral_smul, ←integral_add]; swap
 · refine tourB _ ?_; have hv:∀ t:ℝ,homeB t* (homeB t- (0:ℂ))⁻¹=1:=fun t=>by rw [sub_zero, mul_inv_cancel₀]; exact norm_ne_zero_iff.mp (by rw [home_q]; norm_num)
   simp_rw [hv,one_smul]; exact u.shore.comp_continuous ((under_r i V).comp (continuous_circleMap ..)) (fun t=> fill_I p i (homeC _))
 swap; · exact tourB _ (continuous_const.smul (pace_u f u V _ p x z))
 refine integral_congr_ae (ae_of_all _ fun t=>?_); unfold starp; simp_rw [smul_smul,←add_smul]; refine congrArg (fun v:ℂ=>v • f (update V i (homeB t))) ?_; have he:homeB t - x ≠0:=by intro v; exact (mem_ball_zero_iff.mp z).ne ((sub_eq_zero.mp v) ▸ home_q t) -- tune
 have hp:homeB t≠0:=norm_ne_zero_iff.mp (by rw [home_q]; norm_num)
 rw [sub_zero,mul_inv_cancel₀ hp]; field_simp; ring -- tune
variable (vF:v∈hill I)
def line_K(v:Key I)(S:Finset I)(z:Key I):Key I:=fun i=>if i∈S then z i else v i
omit u in
lemma du_r(g:Key I→ℂ)(p:River g)(v:∀ i∈hill I,g i≠0):River fun i=>(g i)⁻¹:=by refine ⟨p.shore.inv₀ v,fun i h j x k=>?_⟩; exact (p.slope i h j x k).inv (v _ (fill_I h j (ball_subset_closedBall k)))
omit u
lemma κscale {g:Key J→ℂ}{f:Key J→E}(h:River g)(p:River f):River (fun x=> g x • f x):=⟨h.shore.smul p.shore,fun i p' j x h'=> (h.slope i p' j x h').smul (p.slope i p' j x h')⟩
include H ρ
lemma line_v(z:Key J)(p:z∈hill J)(q:v∈hill I):line_K v S (x z)∈hill I:=by refine hill_i.mpr fun i=>?_ ; unfold line_K; split; exact (H z p i).trans ρ.le; exact hill_i.mp q i
include u hp
lemma cab(S:Finset I)(i:I)(p:v∈hill I) (G:Key J→ Key I)(h:∀ t∈hill J,G t ∈hill I)(w:∀ t:ℝ,River (fun v=> f (update (G v) i (homeB t)))): River (fun v=> Jtube f (G v) i (x v i)):=by
 obtain ⟨C,hC,W⟩:= u.budget; have he(t:ℝ)(z:Key J)(u:z∈hill J): 0 < 1-a ∧ 1-a ≤ ‖homeB t-x z i‖:=⟨sub_pos.mpr ρ,le_trans (sub_le_sub_left (H z u i) _) (by nth_rw 1 [←home_q t]; exact norm_sub_norm_le ..)⟩
 let b:= (1-a)⁻¹*C; have hx(z)(u:z∈hill J): x z i ∈rim:=mem_ball_zero_iff.mpr ((H z u _).trans_lt ρ)
 refine riverSum sky _ (fun j=> κscale ?_ (w j)) (integrable_const b) (fun i p=> (pace_u f u _ _ (h i p) _ (hx i p)).aestronglyMeasurable) (fun z hz t=>?_)
 · apply du_r (g:=fun z:Key J=>homeB j-x z i); · exact ⟨continuousOn_const.sub (hp i).shore, fun t v k y w=> (differentiableAt_const _).sub ((hp i).slope _ v _ _ w)⟩
   intro z hz; exact norm_pos_iff.mp ((he j z hz).1.trans_le (he j z hz).2)
 change ‖starp f (G z) i _ t‖≤b; unfold starp; rw [norm_smul,norm_inv]; exact mul_le_mul (inv_anti₀ (he t z hz).1 (he t z hz).2) (W _ (fill_I (h z hz) i (homeC _))) (norm_nonneg _) (inv_pos.mpr (he t z hz).1).le
lemma star_K: ∀ S:Finset I,∀ (v:Key I)(p:v∈hill I), River (fun z=> f (line_K v S (x z))):=by
 intro S; induction S using Finset.induction_on with
 |empty=>intro v p; refine (zeroR (f v)).cong fun z p=>?_ ; rw [show line_K v ∅ (x z)=v from funext fun i=>if_neg (Finset.notMem_empty _)]

 |insert i S q ih=>
    intro V p; let L(v):= line_K V S (x v); have h(v: Key J)(z:ℂ)(u:‖z‖≤1): Function.update (L v) i z=line_K (update V i z) S (x v):=by
       funext k; unfold L line_K; by_cases l:k=i; · subst k; simp [q]
       simp only [Function.update_of_ne l]
    have he(z:ℂ)(u:‖z‖≤1):River (fun v=> f (update (L v) i z)):=by simp_rw [h _ z u]; exact ih _ (fill_I p i (mem_closedBall_zero_iff.mpr u))
    let g(v):=Jtube f (L v) i (x v i)
    have hc(z)(q:z∈hill J): line_K V (insert i S) (x z)=update (L z) i (x z i):=by funext k; unfold L line_K; by_cases l:k=i <;> simp [l]
    have hL(z)(u:z∈hill J):L z∈hill I:=line_v S V x ρ H _ u p -- tune order
    let G:=cab f u V x hp ρ H S i p L hL (fun i=>he _ (home_q _).le) -- tune
    refine (dub_V (he 0 (by simp)) (κscale (hp i) G)).cong fun z t=>?_; rw [hc z t]; exact fan_I f u _ i (hL z t) _ (mem_ball_zero_iff.mpr ((H z t i).trans_lt ρ))
lemma port_C :River (f∘x):=by
 have hv:= star_K f u x hp ρ H univ 0 roots -- tune
 refine hv.cong fun v h=>?_ ; change f (x v)= f (line_K 0 Finset.univ (x v)); rw [show line_K 0 Finset.univ (x v)= x v from funext (fun i=>if_pos (Finset.mem_univ i))]
variable (zP:x 0=0)
lemma spring_k(i:I): Jtube f 0 i 0= tipI f [i]:=by simp only [Jtube,starp, sub_zero]; rfl -- includes u
include zP
lemma cane (j:J) : tipI (f∘ x) [j] =∑ i:I, tipI (fun y:Key J=>x y i) [j] • tipI f [i]:=by
 let V(S:Finset I)(w:Key J):= line_K 0 S (x w); let F(S:Finset I)(w:Key J):= f (V S w)
 change tipI _ _ = _; rw [show f ∘ x= F Finset.univ from funext (fun i=> congrArg f (show _= V Finset.univ i from funext fun j=> (if_pos (Finset.mem_univ j): V Finset.univ i j = _).symm))]; suffices ∀ S:Finset I,tipI (F S) [j]= ∑ i∈S,tipI (fun y:Key J=>x y i) [j] • tipI f [i] from this _
 intro S; induction S using Finset.induction_on with
 | empty=> rw [Finset.sum_empty,show F ∅= fun _=>f 0 from funext fun z=>congrArg f (funext fun i=> if_neg (Finset.notMem_empty _))]; change cutI (fun _:Key J=>f 0) j 0=_; rw [←(mitt (zeroR _) roots j).deriv]; exact deriv_const ..
 | insert i S e ih=>
    let R:= V S; let B(t):= Jtube f (R t) i (x t i); let C (t):=x t i
    have he(Y:ℂ)(w): line_K (update (0:Key I) i Y) S (x w)=update (R w) i Y:=by ext k:1; unfold line_K R V line_K; by_cases h:i=k; subst k; rw [if_neg e]; simp; rw [update_of_ne (Ne.symm h),update_of_ne (Ne.symm h)] -- tune
    have hp'(i): x 0 i=0:=by rw [zP]; rfl
    have hl(z)(p:z∈hill J):R z∈hill I:=line_v S 0 x ρ H z p roots
    have ht:River B:=cab f u 0 x hp ρ H S i roots R hl (fun t=>by simp_rw [←he]; exact star_K f u x hp ρ H S _ (fill_I roots _ (homeC _)))
    have hB:B 0=tipI f [i]:=by unfold B; rw [hp' i, show R 0=0 from (by ext i:1; unfold R V; rw [zP]; unfold line_K; split <;>rfl)]; exact spring_k f u x hp ρ H _ -- tune
    let L(w:Key J):= C w • B w; let K:=κscale (hp i) ht; have hv:EqOn (F (insert i S)) (fun z=>L z+F S z) (hill J):=by
       intro z p; have hx:V (insert i S) z=update (R z) i (C z):=by funext k; unfold V R line_K; by_cases t:k=i; subst k; simp; rfl; rw [update_of_ne t]; simp [V,line_K,t]
       let U:=R z; have hp:f (update U i 0)=f (R z):= congrArg f (show update (R z) i 0=R z from funext fun k=> by unfold R V line_K; by_cases h:k=i; subst k; simp [e]; rw [update_of_ne h])
       change f _= _+_; rw [hx, fan_I f u (R z) i (hl z p) _ (mem_ball_zero_iff.mpr ((H z p _).trans_lt ρ)), hp,add_comm] -- tune
    have hμ:tipI L [j]=tipI C [j] • tipI f [i]:=by
       let v:= mitt (hp i) roots j|>.smul (mitt ht roots j); rw [←hB]; refine (mitt (show River L from K) roots j).unique v |>.trans ?_
       rw [centre, hp' i, zero_smul,zero_add]; rfl
    rw [Finset.sum_insert e, ←ih, ←hμ]; exact (lace_C _ hv roots).trans (tip_A (f:=L) K (star_K f u x hp ρ H S _ roots) [j]) -- tune
end YM.CF.Mew
