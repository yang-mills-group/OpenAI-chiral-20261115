import YM.CF.Ember.Mica
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Lat Lattice Metric MeasureTheory Finset Stationary
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator
variable {ι E B V:Type*} [NormedAddCommGroup E][NormedSpace ℂ E][NormedRing B][NormedAlgebra ℂ B][NormedAddCommGroup V][NormedSpace ℂ V]
structure Tax (ι:Type*) where
 r:ι→ℝ
 cap:ℝ
 pos(i):0<r i
 hold(i):r i≤cap
variable {t:Tax ι}
def Act (t:Tax ι)(p:ℤ)(f:ι→ℂ→E):Prop:=∃ a C :ℝ,0<a ∧ 0<C ∧ ∀ i,∀ z:ℂ,‖z‖<a→ DifferentiableAt ℂ (f i) z∧‖f i z‖≤ C*(t.r i)^p
namespace Act
variable {p q:ℤ} {f g:ι→ℂ→E}
lemma transfer (h:Act t p f)(e:∃ a:ℝ,0<a∧∀ i,∀ z∈ball (0:ℂ) a,g i z=f i z):Act t p g:=by
 obtain ⟨a,C,ha,hC,H⟩:=h; obtain ⟨b,hb,B⟩:=e; refine ⟨min a b,C,lt_min ha hb,hC,fun i z hz=>?_⟩
 have hp:= H i z (hz.trans_le (min_le_left ..)); have hx : z∈ball (0:ℂ) b:=mem_ball_zero_iff.mpr (hz.trans_le (min_le_right ..))
 exact ⟨hp.1.congr_of_eventuallyEq ((isOpen_ball.eventually_mem hx).mono (fun x hx=> B _ _ hx)), B _ _ hx ▸ hp.2⟩
lemma loose (h:Act t p f)(e:q≤p):Act t q f:=by
 obtain ⟨a,C,ha,hC,H⟩:=h; let T:=max t.cap 1; have hx:0<T:=lt_max_of_lt_right one_pos
 refine ⟨a,C*T^(p-q),ha,by positivity,fun i z hz=>⟨(H _ _ hz).1,(H _ _ hz).2.trans ?_⟩⟩
 have he:= t.pos i; rw [show (t.r i)^p=(t.r i)^(p-q)*(t.r i)^q by rw [← zpow_add₀ he.ne']; congr 1; omega, mul_assoc C]; gcongr; exact zpow_le_zpow_left₀ (sub_nonneg.mpr e) he.le ((t.hold i).trans (le_max_left ..))
lemma origin(t:Tax ι)(p:ℤ) :Act t p (fun _ _=> (0:E)):=⟨1,1,one_pos,one_pos,fun i z h=>⟨differentiableAt_const _,by have:=t.pos i; simp only [norm_zero]; positivity⟩⟩
lemma anchor(t:Tax ι)(x:E): Act t 0 (fun _ _=>x):=⟨1,‖x‖+1,one_pos,by positivity,fun i z h=>⟨differentiableAt_const _,by simp⟩⟩
lemma core(h:Act t p f):Act t p fun i _=> f i 0:=by obtain ⟨a,C,ha,hC,H⟩:=h; exact ⟨a,C,ha,hC,fun i z hz=>⟨differentiableAt_const _,(H i 0 (by simpa)).2⟩⟩
lemma add(h:Act t p f)(k:Act t p g):Act t p (fun i z=> f i z+g i z):=by
 obtain ⟨a,C,ha,hc,H⟩:=h; obtain ⟨b,D,hb,hd,G⟩:=k; refine ⟨min a b,C+D,lt_min ha hb,add_pos hc hd,fun i z hz=>?_⟩
 obtain ⟨x,y⟩:= H i z (hz.trans_le (min_le_left ..)); obtain ⟨w,e⟩:=G i z (hz.trans_le (min_le_right ..)); exact ⟨x.add w,(norm_add_le ..).trans ((add_le_add y e).trans_eq ((add_mul ..).symm))⟩
lemma neg(h:Act t p f):Act t p (fun i z=>-f i z):=by obtain ⟨a,C,ha,hc,H⟩:=h; exact ⟨a,C,ha,hc,fun i z hz=>⟨(H i z hz).1.neg, by rw [norm_neg]; exact (H i z hz).2⟩⟩
lemma sub(h:Act t p f)(k:Act t p g):Act t p (fun i z=> f i z-g i z):=by simpa only [sub_eq_add_neg] using h.add k.neg
lemma mul{f g:ι→ℂ→ B}(h:Act t p f)(k:Act t q g):Act t (p+q) (fun i z=> f i z*g i z):=by
 obtain ⟨a,C,ha,hc,H⟩:=h; obtain ⟨b,D,hb,hd,G⟩:=k; refine ⟨min a b,C*D,lt_min ha hb,mul_pos hc hd,fun i z hz=>?_⟩
 obtain ⟨x,y⟩:= H i z (hz.trans_le (min_le_left ..)); obtain ⟨w,e⟩:=G i z (hz.trans_le (min_le_right ..)); refine ⟨x.mul w,(norm_mul_le ..).trans ((mul_le_mul y e (norm_nonneg _) ((norm_nonneg _).trans y)).trans_eq ?_)⟩; rw [zpow_add₀ (t.pos i).ne']; ring
lemma smul {s:ι→ℂ→ℂ}(h:Act t p s)(k:Act t q f):Act t (p+q) (fun i z=> s i z • f i z):=by
 obtain ⟨a,C,ha,hc,H⟩:=h; obtain ⟨b,D,hb,hd,G⟩:=k; refine ⟨min a b,C*D,lt_min ha hb,mul_pos hc hd,fun i z hz=>?_⟩
 obtain ⟨x,y⟩:= H i z (hz.trans_le (min_le_left ..)); obtain ⟨w,e⟩:=G i z (hz.trans_le (min_le_right ..)); refine ⟨x.smul w,(norm_smul_le ..).trans ((mul_le_mul y e (norm_nonneg _) ((norm_nonneg _).trans y)).trans_eq ?_)⟩; rw [zpow_add₀ (t.pos i).ne']; ring
lemma sun [StarAddMonoid E][NormedStarGroup E][StarModule ℂ E](h:Act t p f):Act t p (fun i z=> star (f i (star z))):=by obtain ⟨a,C,ha,hc,H⟩:=h; refine ⟨a,C,ha,hc,fun i z hz=>?_⟩; obtain ⟨x,y⟩:=H i (star z) (by simpa); rw [norm_star]; exact ⟨by have ht:= x.star_star; rw [star_star] at ht; exact ht,y⟩ -- tune
lemma minus(h:Act t p f):Act t p (fun i z=> f i (-z)):=by
 obtain ⟨a,C,ha,hc,H⟩:=h; refine ⟨a,C,ha,hc,fun i z hz=>?_⟩; obtain ⟨x,y⟩:= H i (-z) (by simpa); exact ⟨x.comp z (show DifferentiableAt ℂ (fun z:ℂ=>-z) z from by fun_prop),y⟩
lemma via (h:Act t p f)(L:E→L[ℂ] V): Act t p fun i z=> L (f i z):=by
 obtain ⟨a,C,ha,hc,H⟩:=h; refine ⟨a,(‖L‖+1)*C,ha,by positivity,fun i z hz=>?_⟩; obtain ⟨x,y⟩:= H i z hz; refine ⟨L.differentiableAt.comp z x,?_⟩; have he:=t.pos i; rw [mul_assoc]; exact (L.le_opNorm _).trans (by gcongr; linarith)
lemma finiteSum {κ: Type*}(s:Finset κ)(F:κ→ι→ℂ→E)(h:∀ a∈s,Act t p (F a)):Act t p fun i z=> ∑ j∈s,F j i z:=by
 classical
 induction s using Finset.induction_on with
 | empty=>simpa using origin t p (E:=E)
 | @insert a k g ih=> simp_rw [Finset.sum_insert g]; exact (h a (by simp)).add (ih fun i e=> h _ (by simp [e]))
lemma lip [CompleteSpace E](h:Act t p f):Act t p (fun i=> dslope (f i) 0):=by
 obtain ⟨a,C,ha,hc,H⟩:=h; refine ⟨a,2*C/a,ha,by positivity,fun i z hz=>?_⟩
 have ht:=mem_ball_zero_iff.mpr hz
 have he:DifferentiableOn ℂ (f i) (ball 0 a):=fun z h=> (H i z (mem_ball_zero_iff.mp h)).1.differentiableWithinAt
 have hx:Set.MapsTo (f i) (ball (0:ℂ) a) (closedBall (f i 0) (2*C*(t.r i)^p)):=by intro z h; rw [mem_closedBall,dist_eq_norm]; exact (norm_sub_le ..).trans ((add_le_add (H i z (mem_ball_zero_iff.mp h)).2 (H i 0 (by simpa)).2).trans_eq (by ring))
 exact ⟨((Complex.differentiableOn_dslope (ball_mem_nhds _ ha)).mpr he).differentiableAt (isOpen_ball.mem_nhds ht),(Complex.norm_dslope_le_div_of_mapsTo_ball he hx ht).trans_eq (by ring)⟩
lemma dam [CompleteSpace E](h:Act t p f):∃ a C :ℝ,0<a∧0<C ∧ ∀ i,∀ z∈ball (0:ℂ) a,‖f i z-f i 0‖≤ C*(t.r i)^p*‖z‖:=by
 obtain ⟨a,C,ha,hc,H⟩:=h.lip; refine ⟨a,C,ha,hc,fun i z hz=>?_⟩
 by_cases he:z=0; · simp [he]
 have hx:0<‖z‖:= norm_pos_iff.mpr he; have hp:=(H i z (mem_ball_zero_iff.mp hz)).2
 dsimp only at hp; rw [dslope_of_ne _ he,slope_def_module,norm_smul,norm_inv,sub_zero,inv_mul_eq_div,div_le_iff₀ hx] at hp; exact hp
lemma levy [CompleteSpace E](h:Act t p f):∃ a C :ℝ,0<a∧0<C ∧ ∀ i,∀ z∈ball (0:ℂ) a,‖(f i z+f i (-z))-(f i 0+f i 0)‖≤ C*(t.r i)^p*‖z‖^2:=by
 obtain ⟨a,C,ha,hc,H⟩:= h.lip.dam; refine ⟨a,2*C,ha,by positivity,fun i z hz=>?_⟩
 let d:=dslope (f i) 0
 have he (x:ℂ): x • d x=f i x-f i 0:=by
   by_cases h:x=0; · simp [h]
   unfold d; rw [dslope_of_ne _ h,slope_def_module,sub_zero,smul_inv_smul₀ h]
 rw [show _ - _= z • (d z-d 0)+(-z) • (d (-z)-d 0) from ?_]; swap
 · rw [smul_sub,smul_sub,he z,he (-z),neg_smul]; abel
 refine (norm_add_le ..).trans ((add_le_add (norm_smul_le ..) (norm_smul_le ..)).trans ?_); rw [norm_neg]
 have h': ‖d (-z)-d 0‖ ≤ C*(t.r i)^p*‖z‖:=by have hs:= H i (-z) (by simpa using hz); simpa only [norm_neg] using hs
 exact (add_le_add (mul_le_mul_of_nonneg_left (H i z hz) (norm_nonneg _)) (mul_le_mul_of_nonneg_left h' (norm_nonneg _))).trans_eq (by ring)
end Act
end YM.CF.Ember
