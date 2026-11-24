import YM.CF.BProof.Prox.Chunk

/-! Taking trace to a scalar support price, resetting row index and losing a fixed
fraction of the rate. Polynomial ball growth in micro/block dims. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Prox
open Function Filter Matrix Finset MeasureTheory RG Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix
variable {A X E I: Type*}[Fintype A][Fintype I][MeasurableSpace X][NormedAddCommGroup E][MeasurableSpace E]
variable (B:Base A)(O:Atmos A X)
def Solo (f:X→E)(a p:ℝ): Prop := ∃ (u:Finset A → X→ E)(W:Finset A→ℝ), (∀ T:Finset A, Rent O T (u T) (W T)∧(W T≠0→ T.Nonempty∧ B.C T))∧ f=∑ i,u i∧ Moment.Toll id W a p -- tune parentheses
variable (F:B.Index I)

/-- cost factor on change to trace; exponential t ≤1 may be absorbed later. -/
def trBill (d f:ℕ) (t:ℝ):=((2^d)*f * (t⁻¹^d*d.factorial*Real.exp t))*(1-Real.exp (-t))⁻¹ -- tune cast
variable {B F O}

private lemma seats (B:Base A)(F:B.Index I)(o:A)(k:ℕ) : ((Finset.univ.filter (fun i=> F.port i∈ B.ball o k)).card:ℝ) ≤ ((2:ℝ)^B.dim)*F.roof*(1+(k:ℝ))^B.dim:= by
 apply le_trans ((Nat.cast_le (α:=ℝ)).mpr (F.vent_ball o k)); push_cast; rw [_root_.mul_right_comm (2^_),← mul_pow]; gcongr; linarith

private theorem line_price {W:Page A I I ℝ}(v:∀ i x y,0≤W i x y)(p:∀ i x y,W i x y≠0 → B.C i ∧ F.port x∈i ∧ F.port y∈i){t C:ℝ}(ht:0<t)(hc:0≤C)(k:∀ i,∑ j,∑ R:Finset A,Real.exp (3*t*R.card)*W R i j≤ C): Moment.Toll id (fun R=>∑ i,W R i i) t (C*trBill B.dim F.roof t) := by
 let a:=3*t; let u(x:Finset A):=∑ i,W x i i
 have hu(s:Finset A):0≤u s:= sum_nonneg fun _ _=>v ..
 let H:= (2:ℝ)^B.dim*F.roof*(t⁻¹^B.dim*B.dim.factorial*Real.exp t)
 have hv:0≤H:=by unfold H; positivity
 constructor; exact hu
 intro i; let g(s:Finset A):= Moment.hit id u t i s; rw [show (C*trBill B.dim F.roof t)=(C*H)* (1-Real.exp (-t))⁻¹ by rw [mul_assoc]; rfl]; apply budget_degrees Finset.card (f:=g) (fun i=>by unfold g Moment.hit; split; exact mul_nonneg (Real.exp_pos _).le (hu i); exact le_rfl) (by positivity : 0≤C*H) (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith)); -- tune
 intro n s hs
 let Z:Finset (Finset A):= s.filter (fun T=>i∈T); let J:= univ.filter (fun x=> F.port x∈B.ball i n)
 have he(x:I): ∑ R: Finset A,Real.exp (3*t*R.card)*W R x x ≤ C:= (single_le_sum (f:=fun j=> ∑ R:Finset A,Real.exp (3*t*R.card)*W R x j) (fun j _=> sum_nonneg fun i _=> mul_nonneg (Real.exp_pos _).le (v ..)) (mem_univ x)).trans (k x)
 have hp(T:Finset A)(hT:T∈Z): u T=∑ j∈J,W T j j:=by
    symm; refine sum_subset (subset_univ _) (fun x _ h=>?_); by_contra H; obtain ⟨l,q,-⟩:= p T x x H; have hh:= B.dia l (mem_filter.mp hT).2 q; exact h (mem_filter.mpr ⟨mem_univ _,(B.ball_m ..).2 ((hs T (mem_filter.mp hT).1) ▸ hh)⟩)
 let N:= Real.exp (-(2*t*n)); have hf:0≤N:=(Real.exp_pos _).le; change (∑ i∈s,g i)≤_
 calc
   _ = ∑ j∈J,∑ R∈ Z, N*(Real.exp (3*t*R.card)*W R j j) := by
       rw [sum_comm]; unfold g Moment.hit; simp only [id_eq]; rw [←sum_filter]; apply sum_congr rfl; intro T hT; rw [hp T hT,mul_sum]; refine sum_congr rfl fun j hj=>?_; unfold N; rw [hs T (mem_filter.mp hT).1, ←mul_assoc, ← Real.exp_add,show -(2*t*n)+3*t*n=t*n from by ring]
   _ ≤ ∑ _j∈J, N*C:= by
       apply sum_le_sum; intro j _; rw [← mul_sum]; apply mul_le_mul_of_nonneg_left _ hf; apply le_trans _ (he j); exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> mul_nonneg (Real.exp_pos _).le (v ..))
   _ ≤ ((2:ℝ)^B.dim * F.roof*(1+(n:ℝ))^B.dim)*(N*C):=by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (seats B F i n) (mul_nonneg hf hc)
   _ ≤ (H*Real.exp (t*n))*(N*C):=by unfold H; rw [mul_assoc ((2:ℝ)^_*_) _ (Real.exp (t*n))]; gcongr; exact polynomial_cost ht (by positivity) _
   _ ≤ _:= Eq.le (by unfold N; rw [←Real.exp_nat_mul,show H*Real.exp (t*n)*(Real.exp (-(2*t*n))*C)=C*H*(Real.exp (t*n)*Real.exp (-(2*t*n))) by ring,←Real.exp_add]; ring_nf)
section
variable [BorelSpace E][SecondCountableTopology E]
theorem trace_price {X': Pup X I E}{t C:ℝ}(u:Show O F F X' (3*t) C)(v:0<t)(w:0≤C): Solo B O (fun x=> (X' x).trace) t (C*trBill B.dim F.roof t):=by
 obtain ⟨W,K,t,h,l,p,q⟩:=u.presents
 refine ⟨fun R x=> ∑ i,K R i i x,fun R=>∑ i,W R i i,fun R=>⟨?_,?_⟩,?_,line_price (fun i x y=>(t ..).price) h v w p⟩
 · convert Rent.sum univ (u:=fun i=>K R i i) (fun i _=>t R i i) using 1; ext x; rw [Finset.sum_apply]
 · intro p; by_contra H; apply p; apply sum_eq_zero; intro i _; by_contra u; obtain ⟨v,d,-⟩:=h R i i u; exact H ⟨⟨_,d⟩,v⟩
 ext x; rw [trace]; dsimp only [Matrix.diag_apply]; rw [Finset.sum_apply,sum_comm]; apply sum_congr rfl; intro i hi; exact (congrFun (l i i) x).trans (Finset.sum_apply ..) -- direction tune
end
end YM.CF.BProof.Prox
