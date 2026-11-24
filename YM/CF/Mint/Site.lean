import YM.CF.Mint.Bier
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {x y A B:ℕ→ℝ}
def lum (x:ℕ→ℝ)(i:ℕ):= Real.log (x i)
abbrev tame (x:ℕ→ℝ)(i:ℕ):= temp (x i)
def vast(x:ℕ→ℝ)(i:ℕ):= x i * (tame x i)^2
lemma tc (p:Tendsto x atTop atTop): Tendsto (lum x) atTop atTop:= Real.tendsto_log_atTop.comp p
lemma damp(p:Tendsto x atTop atTop): Aqua (lum x) (tame x):=by
 let F(i):=(radiusB (x i):ℝ); let H:= Work.E01.radiusB_tendsto.comp p; have ht:Tendsto F atTop atTop:=tendsto_natCast_atTop_atTop.comp H; have hx:Aqua F (tame x):=fun n=> (Work.E09.radiusB_temp n).comp p -- tune
 apply hx.through ht; refine ⟨1,one_pos,1,?_⟩; filter_upwards [(tc p).eventually_ge_atTop 1] with i hi; change 1 ≤ lum x i at hi; rw [one_mul,pow_one,Real.norm_of_nonneg (zero_le_one.trans hi)]; exact (show lum x i ≤ (lum x i)^2 by nlinarith).trans (Nat.le_ceil _)
lemma burn(p:Tendsto x atTop atTop) : ∀ᶠ i:ℕ in atTop, vast x i=Real.exp (2*(Real.log (lum x i))^2):=by
 filter_upwards [p.eventually_gt_atTop 0] with i hi; unfold vast tame temp lum; rw [mul_pow, inv_pow, Real.sq_sqrt hi.le, ←mul_assoc, mul_inv_cancel₀ hi.ne',one_mul]; exact (Real.exp_nat_mul _ _).symm -- tune
lemma frost(p:Tendsto x atTop atTop): Aqua (lum x) fun i=> (vast x i)⁻¹:=by
 let L:=lum x; let w:=vast x; intro m
 let G(i):= Real.log (L i); have ht:Tendsto G atTop atTop:= Real.tendsto_log_atTop.comp (tc p); have he:Tendsto (fun i=> Real.exp (-G i)) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)
 refine squeeze_zero' ?_ ?_ he
 · filter_upwards [p.eventually_gt_atTop 0,(tc p).eventually_gt_atTop 0] with i hi e; unfold vast; have ht : 0 < lum x i:=e; positivity
 filter_upwards [(tc p).eventually_gt_atTop 0,ht.eventually_ge_atTop ((m:ℝ)+1),burn p] with i h u z; change L i ^ m * (w i)⁻¹ ≤ Real.exp (-G i); have hg:w i=Real.exp (2*(G i)^2):=z; have hz:0 < L i:=h; nth_rw 1 [← Real.exp_log hz]; change Real.exp (G i) ^ m *_≤_; rw [hg,←Real.exp_neg,← Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith only [u,Nat.cast_nonneg (α:=ℝ) m]
lemma vital(p:Tendsto x atTop atTop) : Tendsto (vast x) atTop atTop:=by
 let L:=Real.log ∘ lum x; have he:Tendsto L atTop atTop:= Real.tendsto_log_atTop.comp (tc p); exact tendsto_atTop_mono' _ ((he.eventually_ge_atTop 1|>.and (burn p)).mono (fun i ⟨h,v⟩=> show Real.exp (L i) ≤ vast x i by rw [v]; apply Real.exp_le_exp.mpr; change L i ≤2*(L i)^2; nlinarith only [show 1 ≤ L i from h])) (Real.tendsto_exp_atTop.comp he)
lemma roughW(p:Tendsto x atTop atTop){Y Z:ℕ→ℝ}{c:ℝ}(g:0<c)(h:Aqua (lum x) fun i=> Y i*(vast x i)⁻¹)(v:∀ᶠ i in atTop,Z i ≥c*vast x i): Aqua (lum x) fun i=> Real.exp (Y i - Z i):=by
 let a:=lum x; let u:=vast x; apply Aqua.clip (G:=fun i=>Real.exp (-1*a i)) (Aqua.exp_neg (tc p) 1 one_pos) (tc p)
 have ht:Tendsto (fun i=> a i*(u i)⁻¹) atTop (𝓝 0):=(Aqua.fed (frost p) (Gray.arg (tc p)) (tc p)).shrinks
 filter_upwards [v,(vital p).eventually_gt_atTop 0, ((ht.add h.shrinks).eventually (ge_mem_nhds (by linarith : 0+0<c)))] with i hi d q; refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ?_⟩; change a i*(u i)⁻¹+Y i*(u i)⁻¹≤c at q; rw [←add_mul, ←div_eq_mul_inv] at q; have hx := (div_le_iff₀ (show 0<u i from d)).1 q; change _≤ -1*a i; change c*u i ≤ _ at hi; linarith
end YM.CF.Mint
