import YM.SU5.Aria.Troupe
/-! # Horizon estimates for travelling commitments. May use them to show full continuity on **all-axis-separated** footprints, not just some horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Aria.Casting
open Set Function Filter Metric
open scoped Topology InnerProductSpace NNReal
variable {I T : Type*}{B:Filter T}{F:ℕ→ Mist I}{X:Type*} [NormedRing X][NormedAlgebra ℂ X]
lemma troupe_size {P:I→ ℝ}(f:I→X)(l:List I)(p:∀ i∈ l, ‖f i‖≤ P i): ‖(l.map f).prod‖ ≤ max ‖(1:X)‖ 1*(l.map P).prod:=by -- norm one ≤? general possibly 0. 
 induction l with
 | nil=> simpa using le_max_left ‖(1:X)‖ 1
 | cons i l ih=>
   have hp: 0≤ P i:=(norm_nonneg _).trans (p _ (List.Mem.head ..)); let q:= max ‖(1:X)‖ 1
   simp only [List.map_cons,List.prod_cons]; refine (norm_mul_le ..).trans ((mul_le_mul (p i (List.Mem.head ..)) (ih (fun i v=> p i (List.Mem.tail _ v))) (norm_nonneg _) hp).trans_eq ?_); rw [mul_left_comm (P i) q] -- tune syntax
lemma troupe_cost (P:I→ℝ)(f g:T→ I→ X)(l:List I)(t:∀ i∈l,∀ t,‖f t i‖≤P i ∧ ‖g t i‖≤P i)(e:∀ i∈l,Tendsto (fun t=> dist (f t i) (g t i)) B (𝓝 0)):
    Tendsto (fun t=> dist (l.map (f t)).prod (l.map (g t)).prod) B (𝓝 0):=by
 induction l with
 | nil=> simp; exact tendsto_const_nhds
 | cons i l ih=>
   let u(t:T):=(l.map (f t)).prod; let v(t:T):=(l.map (g t)).prod; let V:= max ‖(1:X)‖ 1*(l.map P).prod
   have hp:Tendsto (fun t=> dist (u t) (v t)) B (𝓝 0):=ih (fun i p=> t i (List.Mem.tail _ p)) (fun i p=>e i (List.Mem.tail _ p))
   have hc:Tendsto (fun t=> P i*dist (u t) (v t)+dist (f t i) (g t i)*V) B (𝓝 0):=by simpa using (hp.const_mul _).add ((e i (List.Mem.head ..)).mul_const V)
   apply squeeze_zero (fun _=> dist_nonneg) _ hc; intro y; let x:=f y i; let a:=g y i
   have he: ‖x‖≤ P i:= (t i (List.Mem.head ..) y).1; have hx:‖v y‖≤ V:=troupe_size (g y) l (fun i p=> (t i (List.Mem.tail _ p) y).2)
   change dist (x * u y) (a*v y) ≤ P i*dist (u y) (v y)+dist x a * V; simp only [dist_eq_norm]; rw [show x*u y-a*v y=x*(u y-v y)+(x-a)*v y from by noncomm_ring]; apply (norm_add_le ..).trans; apply add_le_add ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))) ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _)))
lemma comfort (H:Hilbert) (A:T→ H.Op)(D:T→H.Op)(Ω:H)(t:Tendsto (fun i=>dist (A i) (D i)) B (𝓝 0)):
    Tendsto (fun i=>dist (inner ℂ Ω (A i Ω)) (inner ℂ Ω (D i Ω))) B (𝓝 0):=by
 have hp:Tendsto (fun i=> ‖Ω‖*(dist (A i) (D i)*‖Ω‖)) B (𝓝 0):=by simpa using (t.mul_const ‖Ω‖).const_mul ‖Ω‖
 apply squeeze_zero (fun _=>dist_nonneg) _ hp; intro i; simp_rw [dist_eq_norm,← inner_sub_right]; apply (norm_inner_le_norm ..).trans; exact mul_le_mul_of_nonneg_left ((A i-D i).le_opNorm _) (norm_nonneg _)
lemma jitter_zero {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y](f: I→ Y)(u:ℕ→Y)(M:ℕ→Mist I)(t:∀ v:ℕ→I,(∀ n,(M n).reaches (v n))→Tendsto (fun i=>dist (u i) (f (v i))) atTop (𝓝 0)) : Tendsto (fun i=>dist (u i) ((M i).mean f)) atTop (𝓝 0):=by
 -- choose worst each n where bad
 classical
 apply Metric.tendsto_nhds.mpr; intro ε p; let S (i:ℕ)(x:I):= dist (u i) (f x) ≤ ε/2; have h(i):∃ x,(M i).reaches x ∧ ((M i).holds (S i) ∨ ¬ S i x):=by
    by_cases v:(M i).holds (S i); · obtain ⟨x,t⟩:=(M i).someReach; exact ⟨x,t,Or.inl v⟩
    rw [Mist.holds_at, not_forall] at v; obtain ⟨u₀,v⟩:=v; rw [Classical.not_imp] at v; exact ⟨u₀,v.1,Or.inr v.2⟩
 choose x hx H using h
 filter_upwards [ (t x hx).eventually (gt_mem_nhds (show 0<ε/2 by positivity))] with n a
 have hb: (M n).holds (S n):=(H n).resolve_right (not_not.mpr a.le); rw [Real.dist_0_eq_abs,abs_of_nonneg dist_nonneg,dist_comm]; exact ((M n).ceiling f _ (ε/2) ((M n).promotes (fun i p=>by rw [dist_comm]; exact p) hb)).trans_lt (half_lt_self p)
end YM.CF.Buffered.Afterglow.Tower.Aria.Casting
