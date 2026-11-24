import YM.CF.Graph.Core
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {x y A B:ℕ→ℝ}
def Gray (x f:ℕ→ℝ):Prop:=∃ C:ℝ,0<C∧∃ v:ℕ,∀ᶠ i in atTop, ‖f i‖ ≤ C*(x i)^v
namespace Gray
variable {F G U:ℕ→ℝ}
lemma coef (h:Tendsto A atTop atTop)(c:ℝ):Gray A fun _=>c:=⟨‖c‖+1,by positivity,0,Eventually.of_forall (fun i=>by simp)⟩
lemma arg(h:Tendsto A atTop atTop): Gray A A:=⟨1,one_pos,1,(h.eventually (eventually_ge_atTop 0)).mono fun i u=>by rw [Real.norm_of_nonneg u]; simp⟩
lemma thin(h:Tendsto A atTop atTop){c:ℝ}(p:Tendsto F atTop (𝓝 c)):Gray A F:=by obtain ⟨d,v,b,H⟩:=coef h (‖c‖+1); exact ⟨d,v,b, H.mp ((p.norm.eventually (ge_mem_nhds (lt_add_one _))).mono fun i q e=>le_trans q ((Real.norm_of_nonneg (by positivity :0≤‖c‖+1 )).symm.trans_le e))⟩ -- tune orientation
lemma neg (p:Gray A F):Gray A fun i=> -F i:=by obtain ⟨c,a,h,q⟩:=p; exact ⟨c,a,h,by simpa using q⟩
lemma add(h:Tendsto A atTop atTop)(p:Gray A F)(v:Gray A G):Gray A fun i=>F i+G i:=by
 obtain ⟨c,g,x,w⟩:=p; obtain ⟨b,hb,y,v⟩:=v; refine ⟨c+b,add_pos g hb,x+y,?_⟩; filter_upwards [w,v,h.eventually (eventually_ge_atTop (1:ℝ))] with i a d e; rw [add_mul]; exact (norm_add_le ..).trans (add_le_add (a.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ e (by omega)) g.le)) (d.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ e (by omega)) hb.le)))
lemma mul(p:Gray A F)(v:Gray A G):Gray A fun i=> F i *G i:=by
 obtain ⟨c,g,x,w⟩:=p; obtain ⟨b,hb,y,v⟩:=v; refine ⟨c*b,mul_pos g hb,x+y,?_⟩; filter_upwards [w,v] with i a d; rw [norm_mul]; exact (mul_le_mul a d (norm_nonneg _) ((norm_nonneg _).trans a)).trans_eq (by rw [pow_add]; ring)
lemma powG(h:Tendsto A atTop atTop)(p:Gray A F)(n:ℕ):Gray A fun i=>F i^n:=by induction n with| zero=>simpa using coef h 1| succ n ih=> simp_rw [pow_succ]; exact ih.mul p
lemma higher(p:Gray A G)(h:∀ᶠ i in atTop, ‖F i‖ ≤ G i):Gray A F:=by obtain ⟨c,u,v,y⟩:=p; exact ⟨c,u,v,(h.and y).mono fun i ⟨h,e⟩=> h.trans ((le_abs_self _).trans e)⟩
lemma up(p:Gray A B)(v:Gray B F): Gray A F:=by
 obtain ⟨c,a,k,u⟩:=p; obtain ⟨d,g,j,h⟩:= v; refine ⟨d*c^j,by positivity,k*j,?_⟩; filter_upwards [u,h] with i hi t; refine t.trans ?_; apply (mul_le_mul_of_nonneg_left (show B i ^ j ≤ (c*A i^k)^j from ?_) g.le).trans_eq ?_
 · exact (le_abs_self _).trans (by rw [abs_pow]; gcongr; exact hi)
 rw [mul_pow,pow_mul,mul_assoc]
end Gray
def Aqua(A F:ℕ→ℝ):Prop:=∀ n:ℕ, Tendsto (fun i=> (A i)^n * F i) atTop (𝓝 0)
namespace Aqua
variable {F G:ℕ→ℝ}
lemma shrinks(p:Aqua A F): Tendsto F atTop (𝓝 0):=by simpa using p 0
lemma pays(p:Aqua A F)(g:Gray A G)(h:Tendsto A atTop atTop):Aqua A fun i=> F i * G i:=by
 obtain ⟨c,a,v,t⟩:=g; intro n; have ht:= p (n+v); refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun i=> norm_nonneg _)) ?_ (show Tendsto (fun i=> ‖(A i)^(n+v)*F i‖ * c) atTop (𝓝 0) from ?_)); swap; · simpa only [norm_zero,zero_mul] using ((ht.norm).mul_const c)
 filter_upwards [t,h.eventually_ge_atTop 0] with i hi q; rw [norm_mul,norm_mul,norm_mul,norm_pow,norm_pow,Real.norm_of_nonneg q]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (norm_nonneg _)) (pow_nonneg q _)).trans_eq; rw [pow_add]; ring
lemma fed(p:Aqua A F)(b:Gray A G)(h:Tendsto A atTop atTop): Aqua A fun i=> G i * F i:=by rw [show (fun i=>G i * F i)=_ from funext fun i=>mul_comm (G i) (F i)]; exact p.pays b h
lemma panel(p:Aqua A F)(h:Aqua A G): Aqua A fun i=>F i+G i:=fun n=>by simp_rw [mul_add]; simpa only [add_zero] using (p n).add (h n)
lemma exp_neg(h:Tendsto A atTop atTop)(c:ℝ)(p:0<c): Aqua A fun i=>Real.exp (-c*A i):=by
 intro n; have he:= ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n:=n)).comp (h.const_mul_atTop p)).const_mul (c^n)⁻¹; change Tendsto (fun i=> (c^n)⁻¹ * ((c*A i)^n * Real.exp (-(c*A i)))) atTop (𝓝 ((c^n)⁻¹*0)) at he; rw [mul_zero] at he; apply he.congr'; apply Eventually.of_forall; intro i; dsimp only; rw [mul_pow, neg_mul]; field_simp
lemma clip(p:Aqua A G)(h:Tendsto A atTop atTop)(v:∀ᶠ i in atTop,0 ≤ F i∧ F i ≤ G i): Aqua A F:=fun n=> squeeze_zero' ( ((h.eventually_ge_atTop 0).and v).mono fun i u=> mul_nonneg (pow_nonneg u.1 n) u.2.1) (((h.eventually_ge_atTop 0).and v).mono fun i u=> mul_le_mul_of_nonneg_left u.2.2 (pow_nonneg u.1 n)) (p n)
lemma rise(p:Aqua A F)(h:Tendsto A atTop atTop)(g:∀ᶠ i in atTop,0≤ F i): Aqua A fun i=> Real.exp (F i)-1:= (p.fed (Gray.coef h 2) h).clip h <| (g.and (p.shrinks.eventually (ge_mem_nhds one_pos))).mono fun i ⟨u,v⟩=>⟨sub_nonneg.mpr (Real.one_le_exp u),Pic.score u v⟩
lemma through(p:Aqua A F)(h:Tendsto A atTop atTop)(g:Gray A B): Aqua B F:=fun n=> (Aqua.fed p (Gray.powG h g n) h).shrinks
lemma changeA(p:Aqua A F)(h:F=ᶠ[atTop] G): Aqua A G:=fun n=>(p n).congr' (h.mono fun i v=>congrArg (A i^n * ·) v)
end Aqua
end YM.CF.Mint
