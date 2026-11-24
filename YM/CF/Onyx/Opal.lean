import YM.CF.Onyx.Hound
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia cartWeight)
variable {j:ℕ}
lemma up_t (H:1≤j):∃ U:ℝ,0<U∧∀ (M:Male)(x:Bin),Bound Real.pi x→ (‖shell j M.val (tmap x)-(1/4:ℂ)*prodM (tmap x) (tmap x)‖≤ U*‖x‖^3 ∧ ‖lash (skin j M.val (tmap x))-(1/2:ℂ) • lash (tmap x)‖≤ U*‖x‖^2) :=by
 have ht:= go_b (t:=crop) RayH.x (fun _=>rfl) RayH.cap; let T:=RayH.M; obtain ⟨c,K,g,p,X⟩:= ht.quartz (fun i=>(T i).val) (fun i=>(T i).property) j H; obtain ⟨b,d,w,v,Z⟩:= lime ht H T
 refine ⟨K+d,by positivity,fun M x h=>?_⟩; by_cases e:x=0
 · subst x; rw [show tmap (0:Bin)=0 from rfl]; simp [lash,prodM]
 let i:RayH:=⟨M,x,h,norm_pos_iff.mpr e⟩; have hz:= (X i 0 (by simpa)).2; have hx:= (Z i 0 (by simpa)).2; rw [zpow_ofNat] at hz hx; exact ⟨hz.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right v.le) (show 0≤ ‖x‖^3 by positivity)), hx.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left p.le) (sq_nonneg ‖x‖))⟩
lemma zio(Y: Gaia):prodM (river Y) (river Y)= (‖Y‖:ℂ)^2 :=by
 rw [← Complex.ofReal_pow, ← real_inner_self_eq_norm_sq,peerF,Complex.ofReal_sum]; unfold prodM; exact sum_congr rfl fun i _=>(Complex.ofReal_mul ..).symm
lemma lift_r (p:Bin)(R:ℝ): river (R • moor p)=(R:ℂ) • tmap p:= by funext i; change ((R*p i:ℝ):ℂ)=_; rw [Complex.ofReal_mul]; rfl
lemma drought (s:ℕ→Side)(v:∀ i,Offset (s i))(R:ℕ→ℝ)(k:∀ i,Site (s i))(Y:Gaia)(X:Tendsto (fun i=> duel (R i) (v i) (k i)) atTop (𝓝 Y)): Tendsto (fun i=> (R i:ℂ) • tmap (glen (v i) (k i))) atTop (𝓝 (river Y)):=by
 simp_rw [← lift_r]; have ht:Continuous river:=by apply continuous_pi; intro i; change Continuous fun p:Gaia=>(p i:ℂ); fun_prop
 exact ht.continuousAt.tendsto.comp X
variable {s:ℕ→Side}{R:ℕ→ℝ}{v:∀ i,Offset (s i)}{k:∀ i,Site (s i)}{Y:Gaia}
lemma Yard.facing(h:Yard s R)(t:∀ᶠ i in atTop,Y∈pie (R i) (k i))(v:∀ i,Offset (s i)): Tendsto (fun i=> duel (R i) (v i) (k i)) atTop (𝓝 Y):=by
 rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (t.mono fun i e=> (norm_sub_rev ..|>.trans_le (cost (h.pos i) e _))) ?_; have he:=h.water.const_mul 4; simpa only [mul_zero,mul_left_comm] using he
lemma Yard.treat (h:Yard s R)(t:Tendsto (fun i=>duel (R i) (v i) (k i)) atTop (𝓝 Y)): ∃ C:ℝ,0<C∧∀ᶠ i in atTop, (R i)*‖glen (v i) (k i)‖ ≤ C:=by
 refine ⟨‖Y‖+1,by positivity,(t.norm.eventually (gt_mem_nhds (by linarith : ‖Y‖ < ‖Y‖+1))).mono fun i e=>?_⟩; refine le_trans ?_ (le_of_lt e); change _ ≤ ‖duel (R i) _ _‖; unfold duel; rw [norm_smul,Real.norm_of_nonneg (h.pos i).le]; refine mul_le_mul_of_nonneg_left ?_ (h.pos i).le; let p:= glen (v i) (k i); have ht:= boundH (moor p); exact ((height p).symm.le.trans ht)
lemma pure_k(K u r y:ℝ)(p:0<r)(g:0≤y)(q:0<K)(v:r*y≤u)(j:ℕ):r^j*(K*y^(j+1)) ≤ (K*u^(j+1))/r:=by
 rw [le_div_iff₀ p]; exact le_trans (by rw [mul_pow]; ring_nf; rfl : r^j*(K*y^(j+1))*r ≤ K*(r*y)^(j+1)) (by gcongr) -- tune
variable (h:Yard s R)(M:ℕ→Male)(t:Tendsto (fun i=>duel (R i) (v i) (k i)) atTop (𝓝 Y))
include h t
lemma flare (H:1≤j): Tendsto (fun i=>(R i:ℂ)^2*shell j (M i).val (tmap (glen (v i) (k i)))) atTop (𝓝 (fieldV Y:ℂ)):=by
 let K(i):=glen (v i) (k i); let U(i):= (R i:ℂ)^2; let P(i):=tmap (K i); let V(i):=duel (R i) (v i) (k i); obtain ⟨b,g,A⟩:= up_t H; obtain ⟨C,p,W⟩:= h.treat t
 have hh:Tendsto (fun i=>U i*(shell j (M i).val (P i)-(1/4:ℂ)*prodM (P i) (P i))) atTop (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ (h.thinner (b*C^(2+1))); filter_upwards [W] with i hi; rw [norm_mul]; unfold U; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (h.pos i).le]; exact (mul_le_mul_of_nonneg_left (A _ _ (orb _ _ (h.even _))).1 (pow_nonneg (h.pos i).le _)).trans (pure_k b C (R i) _ (h.pos i) (norm_nonneg (K i)) g hi 2)
 let G(p:Gaia):ℂ:= (fieldV p:ℂ); have hg: Continuous G:= by unfold G fieldV; fun_prop
 convert hh.add (hg.continuousAt.tendsto.comp t) using 1
 · ext1 i; change U i*_ = _+G (V i); rw [mul_sub]; unfold G fieldV; push_cast; rw [← zio, show V i= (R i) • moor (K i) from rfl,lift_r]; simp only [prodM,Pi.smul_apply,smul_eq_mul]; simp_rw [show ∀ a:Axis, (R i:ℂ)* tmap (K i) a*((R i:ℂ)*tmap (K i) a)=U i*(P i a*P i a) from fun a=>by unfold U P; ring, ←mul_sum]; change U i*shell j _ (P i)=_; ring
 · rw [zero_add]; -- tune
lemma hook (H:1≤j): Tendsto (fun i=> (R i:ℂ) • lash (skin j (M i).val (tmap (glen (v i) (k i))))) atTop (𝓝 ((1/2:ℂ) • lash (river Y))):=by
 let K(i):=glen (v i) (k i); let F(i):= lash (skin j (M i).val (tmap (K i))); let V(i):= lash (tmap (K i)); obtain ⟨b,g,A⟩:=up_t H; obtain ⟨C,p,W⟩:= h.treat t
 have hh:Tendsto (fun i=> (R i:ℂ) • (F i-(1/2:ℂ) • V i)) atTop (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ (h.thinner (b*C^2)); filter_upwards [W] with i hi; rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (h.pos i).le]; refine (mul_le_mul_of_nonneg_left (A _ _ (orb _ _ (h.even _))).2 (h.pos i).le).trans ?_; have hx:=pure_k b C _ _ (h.pos i) (norm_nonneg (K i)) g hi 1; rw [pow_one] at hx; exact hx
 have ht:= drought s v R k Y t; let y:ℂ:=1/2; have hv : Tendsto (fun i=>y • lash ((R i:ℂ) • tmap (K i))) atTop (𝓝 (y • lash (river Y))):= (lashCL.continuous.continuousAt.tendsto.comp ht).const_smul y
 convert hh.add hv using 1
 · ext1 i; change _=(R i:ℂ) • _+_; rw [smul_sub,lash_s,smul_comm (a:=(lash _)) y (R i:ℂ)]; change _=(R i:ℂ) • F i - (R i:ℂ) • (y • V i)+(R i:ℂ) • (y • V i); rw [sub_add_cancel]
 · rw [zero_add]; -- tune
end YM.CF.Onyx
