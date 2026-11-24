import YM.SU5.FiniteGaugeData.Largo.Such
set_option autoImplicit false
set_option maxHeartbeats 370000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir
open scoped Topology BigOperators Pointwise
-- Tannery & rank port. HD: 4 alias exponents from plank, 8 after square. 
section
variable {X:Type*}{f:Filter X} {F:X→Momentum} {u:ℕ} {w:Momentum}{M:X→Side} (p:∀ x, Odd (M x).val)(r:Tendsto (fun i=> (M i).val) f atTop)(P:Tendsto F f (𝓝 w))
abbrev wick (i:Cover):= ∏ k:Axis,gateL (i k)
lemma wickL: Summable wick:=by
 let B:= ∑' i,gateL i; apply summable_of_sum_le (fun i=> Finset.prod_nonneg fun j _=> (gate_pp _).le) (c:= B^4)
 intro s; let V(k:Axis):= s.image (fun x=>x k); have he: s ⊆ Fintype.piFinset V:=fun i t=> Fintype.mem_piFinset.mpr fun k=> mem_image_of_mem _ t
 refine (sum_le_sum_of_subset_of_nonneg he (fun i _ _=> Finset.prod_nonneg (s:=@univ Axis _) fun j _=> (gate_pp _).le)).trans ?_; rw [← Finset.prod_univ_sum (κ:=fun _=>ℤ) V (fun _=>gateL)]; simpa only [prod_const,card_univ,Axis,Fintype.card_fin] using (Finset.prod_le_prod (s:=@univ Axis _) (f:=fun i=> ∑ j∈V i,gateL j) (g:=fun i=>B) (fun i _=>sum_nonneg (fun j _=>(gate_pp j).le)) (fun i _=>gate_summ.sum_le_tsum _ (fun j _=> (gate_pp j).le)))
abbrev content (M:Side)(p:Momentum)(a:Axis)(i:Site M):ℂ:= muff 4 M (aliasAt p i)^2*((M.val:ℂ)⁻¹ * bGraph (aliasAt p i) a)
include p in
lemma midC(a:Axis): ∃ C:ℝ,0<C∧ ∀ i (l:Site (M i)), l≠0 →∀ w:Momentum, w∈baseCube→ ‖content (M i) w a l‖ ≤ C*wick (lift l):=by
 let I:= Σ i:X,{l:Site (M i)//l≠0}; let μ(t:I):=M t.1; let v(t:I):Site (μ t):=t.2.val
 have hp:∀i:I,Odd (μ i).val:=fun i=> p _
 obtain ⟨e,C,t,H,G⟩:= Moderate.mul ((muff_pay 4 μ hp v).pow 2) (spicy μ hp v (fun i=>i.2.property) a)
 refine ⟨C,H,fun i l hl w p=>?_⟩; let t':I:= ⟨i,l,hl⟩; apply (G t'|>.bound _ (mem_cube_real (base_subset_realCube t p) t)).trans; apply mul_le_mul_of_nonneg_left _ H.le; change decay 4 l^2*(grade l)⁻¹≤ wick _
 have he: decay 4 l ≤ decay 2 l:= decay_anti l (show 2≤4 by omega)
 calc decay 4 l^2*(grade l)⁻¹ ≤ decay 4 l:= by
        rw [sq]; refine (mul_le_of_le_one_right (mul_nonneg (decay_pos ..).le (decay_pos ..).le) (inv_le_one_of_one_le₀ (grade_ge _))).trans (mul_le_of_le_one_right (decay_pos ..).le (decay_le_one ..))
      _ ≤ _:= he.trans_eq (by simp [wick,decay,mix,gateL,up, prod_pow])
abbrev risen (n:Side):= (univ:Finset (Site n)).image (Lattice.lift)
def cashN (N:Side)(x:Momentum)(a:Axis)(j:Cover):ℂ:= if j∈ risen N then content N x a (wrap N j) else 0
def melody (p:Momentum) (i:Axis): ℂ := ∑' j:Cover, leer (p+reciprocal j)^8 * (2*((p+reciprocal j) i) / pass (p+reciprocal j))
lemma moments (N:Side)(x:Momentum)(a:Axis) : mixL 4 N x a= ∑' i, cashN N x a i:= by
 rw [tsum_eq_sum (s:=risen N) (by intro i p; unfold cashN; rw [if_neg p]), show risen N=_ from rfl]; unfold risen; rw [sum_image]; swap; · exact lift_inj.injOn
 unfold mixL; simp_rw [Pi.smul_apply,Finset.sum_apply, Pi.smul_apply, smul_eq_mul,mul_sum]; apply sum_congr rfl; intro i h
 unfold cashN; rw [if_pos (show lift i∈ risen N from mem_image_of_mem _ h),wrap_lift]; unfold content; ring
lemma in_place {N:Side}{x:Cover}(h:x∈ risen N): lift (wrap N x)=x:= by obtain ⟨x,p,rfl⟩:=mem_image.mp h; rw [wrap_lift]
-- requirement eventually base. Tannery permits special principal density budget eventually only. 
include r p P
lemma harmony (u:∀ i:Cover,pass (w+reciprocal i)≠0) (a:Axis)(v:∀ᶠ i in f,F i∈baseCube): Tendsto (fun i=> mixL 4 (M i) (F i) a) f (𝓝 (melody w a)):= by
 let g(x:Cover):=leer (w+reciprocal x)^8*(2*((w+reciprocal x) a)/pass (w+reciprocal x)); let Y(i:X):=cashN (M i) (F i) a
 have he(x:Cover):Tendsto (fun i=> Y i x) f (𝓝 (g x)):=by
    let h(i):= F i+reciprocal x; have he:Tendsto h f (𝓝 (w+reciprocal x)):= P.add_const _; let U:= Tendsto.mul ((guideM p r he 4).pow 2) (mileL r he (u x) a); rw [←pow_mul] at U
    refine U.congr' ?_; have H(i:Side): (∀ a:Axis,-(i.val:ℤ)<2*x a ∧ 2*x a ≤ i.val)→ lift (wrap i x)=x:= fun t=> lift_eq_iff.mpr ⟨rfl,t⟩; let D:= (univ:Finset Axis).sup (fun a:Axis=> (x a).natAbs)
    filter_upwards [r.eventually_gt_atTop (2*D)] with i t; let N:= M i; have hx:lift (wrap N x)= x:= H N fun a=> by change _ < N.val at t; have hv: (x a).natAbs ≤ D:=le_sup (f:=fun a:Axis=> (x a).natAbs) (mem_univ _); omega
    have hv:x∈ risen (M i):=mem_image.mpr ⟨(wrap (M i) x),mem_univ _,hx⟩
    unfold Y cashN; rw [if_pos hv]; unfold content; rw [show aliasAt (F i) (wrap (M i) x)= narrow N (F i+reciprocal x) from ?_]; funext a; rw [alias_value,hx]; simp [N,narrow,reciprocal, div_eq_mul_inv,mul_comm]
 let V:= ‖g 0‖+1; let hx:Tendsto (fun i=> ‖Y i 0‖) f (𝓝 ‖g 0‖):= (he _).norm; obtain ⟨C,hp,t⟩:= midC p a; simp_rw [moments]; let W:= Function.update (fun a: Cover=> C*wick a) 0 V
 apply tendsto_tsum_of_dominated_convergence (bound:=W) _ he ?_; swap
 · filter_upwards [v,hx.eventually (ge_mem_nhds (lt_add_one _))] with i v h x; let y:=wrap (M i) x; by_cases g':x=0; · subst x; unfold W; rw [update_self]; exact h
   unfold Y cashN W; rw [update_of_ne g']; split; rename_i l
   · have hy: y ≠ 0:= fun t=>g' (by have hx:lift y=x:= in_place l; rw [← hx,t,lift_origin]); exact (t i y hy (F i) v).trans (le_of_eq (congrArg (fun z=> C*wick z) (in_place l)))
   rw [norm_zero]; exact mul_nonneg hp.le (prod_nonneg (fun _ _=>(gate_pp _).le))
 exact (wickL.mul_left C).update _ _
end
end YM.CF.Window.Largo
