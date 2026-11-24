import YM.CF.BPress.Spin.Pledge
/-! Complete pledge from rows passed on per-entry, and from both rows and columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin.Pledge
open Function Finset Filter Fock Branch
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra

variable {I Y D : Type*}[Fintype Y][DecidableEq Y][Fintype I][DecidableEq I] [TopologicalSpace D] {b : Stage Y I D Empty} {P:Pledge} {C : ℝ}
variable {J:Type*}[Fintype J] {A:I→I→J→Seal Y} {c:I→I→J→ℝ} {f:I→I→J→D→ℂ}{g:Raw D I}
section
variable (H:∀ i j k, Expo b (A i j k) i j (c i j k) (f i j k)) (K:∀ i, ∑ j,∑ k,rent P.rate (A i j k)* c i j k ≤ P.price)
include H K
theorem funds (q:∀ j, ∑ i, ∑ k,rent P.rate (A i j k)* c i j k ≤ P.price)(h:∀ x i j,g x i j=∑ k,f i j k x) : P.Costs b g:=by
 let W S i j:= ∑ k∈dest (A i j) S,c i j k
 let F(S: Seal Y)(x:D):Op I:= Matrix.of fun i j=> ∑ k∈dest (A i j) S,f i j k x
 have he S i j : Expo b S i j (W S i j) (fun x=> F S x i j):= Expo.sumK (dest (A i j) S) (c i j) (f i j) (fun k t=>by rw [← show A i j k=S from (mem_filter.mp t).2]; exact H i j _) -- tune
 have hx i j : saleM P.rate W i j= ∑ k,rent P.rate (A i j k)* c i j k:=by rw [lump (A i j) (fun k=>_)]; unfold saleM W; apply sum_congr rfl; intro S _; rw [mul_sum]; exact sum_congr rfl fun i' h=> by rw [(mem_filter.mp h).2]
 refine ⟨F,W,fun S=> ⟨fun i _=> Empty.elim i, he S⟩, ⟨P.bought.le,fun i=>by simp_rw [hx]; exact K i,fun i=>by simp_rw [hx]; exact q i⟩,fun x=>?_⟩ -- simp orientation
 ext i j; rw [Matrix.sum_apply,h]; exact lump (A i j) (fun y=>f i j y x)

omit H K in
def disperse (P:Pledge)(C:ℝ):Pledge:=⟨P.rate/2,max P.price ((∑' i:ℕ, Real.exp (-P.rate/2*i)*(C*((i:ℝ)+1)^4))*P.price), half_pos P.pos,lt_max_of_lt_left P.bought⟩
theorem fundRows (v:Capacity b C)(p:0≤C)(h:∀ x i j,g x i j=∑ k,f i j k x) : (P.disperse C).Costs b g:=by
 let t(n:ℕ):= Real.exp (-P.rate/2*n); let W(n:ℕ):= t n * (C*((n:ℝ)+1)^4)
 let U i j k:= rent (P.rate/2) (A i j k)* c i j k
 refine funds H ?_ ?_ h
 · intro i; apply le_trans ?_ ((K i).trans (le_max_left ..)); apply sum_le_sum; intro j _; exact sum_le_sum fun k _=> mul_le_mul_of_nonneg_right (rent_up (half_le_self P.pos.le) _) (H i j k).positive
 intro j; change ∑ i, ∑ k,U i j k≤ max _ _; refine le_trans ?_ (le_max_right ..)
 have ht (n : ℕ) : (∑ i:I, ∑ k:J with (A i j k).card=n,U i j k) ≤ W n * P.price:=by
   let s:= board b (bay b.F (b.home j) n); let f' i:=∑ k:J with (A i j k).card=n,U i j k
   have he i (u:i∉ s): f' i=0:=by
      apply sum_eq_zero; intro k w; unfold U; rw [show c i j k=0 from ?_,mul_zero]
      by_contra h; obtain ⟨x,y,z⟩:= (H i j k).triggered h; apply u; apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩; rw [←(mem_filter.mp w).2]; exact x.basin z y
   rw [← sum_subset (f:=f') s.subset_univ (fun i _ u=> he i u)]; apply le_trans (sum_le_sum (g:=fun _=>t n*P.price) (fun i _=>?_)) ?_
   · rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (v.place ..) (mul_nonneg (Real.exp_pos _).le P.bought.le)).trans_eq; unfold W; ring
   apply le_trans ?_ (mul_le_mul_of_nonneg_left (K i) (Real.exp_pos _).le); let Y(j k):= rent P.rate (A i j k)* c i j k
   refine le_trans ?_ (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun j:I=> ∑ k,Y j k) (fun l _=> sum_nonneg (fun i' _=> mul_nonneg (rent_pos ..).le (H i l i').positive)) (mem_univ j)) (Real.exp_pos _).le)
   rw [mul_sum]; apply le_trans ?_ (sum_le_sum_of_subset_of_nonneg (s:= univ.filter fun k:J=> (A i j k).card=n) (subset_univ _) (fun k _ _=> mul_nonneg (Real.exp_pos _).le (mul_nonneg (rent_pos ..).le (H i j k).positive)))
   exact (sum_congr rfl fun k hk=> by unfold U; rw [rent,rent,← mul_assoc,←Real.exp_add,(mem_filter.mp hk).2]; ring_nf).le -- tune
 let N : ℕ:=Fintype.card Y+1; have he i k: (A i j k).card ∈ range N:= mem_range.mpr ((card_le_univ _).trans_lt (by unfold N; omega))
 have hy (i:I): (∑ k,U i j k)=∑ n∈range N,∑ k:J with (A i j k).card=n,U i j k:= by simp_rw [sum_filter]; rw [sum_comm]; simp [he]
 simp_rw [hy]; rw [sum_comm]; apply (sum_le_sum fun i (_:i∈range N)=> ht i).trans; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right ((fund_hit P.rate C P.pos p).sum_le_tsum _ fun _ _=> by positivity) P.bought.le
end
end YM.CF.BPress.Spin.Pledge
