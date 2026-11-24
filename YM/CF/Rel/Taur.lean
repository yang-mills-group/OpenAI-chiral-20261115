import YM.CF.Rel.Graced
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Braid
abbrev DialT (n:Side)(m:ℕ):=Fin m→Site n
def cMul(d x:DialT n m):ℂ:= ∏ i,cell (d i) (x i)
lemma cSwap(d x:DialT n m):cMul d x=cMul x d:=prod_congr rfl fun i _=> cell_duality ..
lemma legX (x y : Site n): ‖cell x y‖ = 1:=mode_real _ _ (real_frequency x)
@[simp] lemma cUnit (d x:DialT n m): ‖cMul d x‖=1:=by unfold cMul; simp_rw [norm_prod,legX,prod_const_one] -- tune
lemma cnorm (d x y: DialT n m):cMul d (x+y)=cMul d x*cMul d y:=by unfold cMul; simp_rw [Pi.add_apply,cell_add,Finset.prod_mul_distrib]
lemma cneg (d x : DialT n m): cMul d (-x)=(cMul d x)⁻¹:=by unfold cMul; simp_rw [Pi.neg_apply,cell_inverse, Finset.prod_inv_distrib] -- tune
abbrev Epos(n:Side)(m:ℕ):ℝ:= Fintype.card (DialT n m)
abbrev frameX(n:Side)(m:ℕ):ℂ:= Epos n m
lemma lineE(n:Side)(m:ℕ): frameX n m=((n.val:ℂ)^4)^m:=by simp [frameX,Epos,DialT]
lemma frame_ne(n:Side)(m:ℕ):frameX n m≠0:=by rw [lineE]; exact pow_ne_zero _ (pow_ne_zero _ (side_ne _))
lemma detU (d d':DialT n m): (∑ i,cMul i d*(cMul i d')⁻¹)= if d=d' then frameX n m else 0:=by
 conv_lhs=> rhs; intro i; rw [cSwap i d,cSwap i d']
 calc
    _ = ∏ k:Fin m, (if d k=d' k then ((n.val:ℂ)^4) else 0):= by
       unfold cMul DialT; simp_rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]; rw [← Fintype.prod_sum (fun k:Fin m=> fun i:Site n=> cell (d k) i*(cell (d' k) i)⁻¹)]; simp_rw [Bloch.orthogonal]
    _ = _:=by split
              next h=> rw [h,lineE]; simp
              next h=> obtain ⟨i,hi⟩:= Function.ne_iff.mp h; exact Finset.prod_eq_zero (mem_univ i) (if_neg hi)
-- inversion for coefs
abbrev stencil(m:ℕ):=Shift (Keys m)
def tollX(d:DialT n m):Space m:=fun k=> mon (d k.1) k.2
def coil (n:Side)(x:stencil m):DialT n m:=fun i=> wrap n (fun k=>x (i,k))
lemma cord (d:DialT n m) (x:stencil m): Laurent.mode (tollX d) x= cMul d (coil n x):=by
 unfold mode tollX; rw [Fintype.sum_prod_type,Finset.mul_sum,Complex.exp_sum]; unfold coil cMul; simp_rw [cell_wrap]; rfl
lemma two_size {x y:stencil m}(hx:size x≤ l)(hy:size y≤ l)(h:coil n x=coil n y)(hl:2*l<n.val):x=y:=by
 funext ⟨i,j⟩; obtain ⟨p,hp⟩:= Bloch.cover_of_eq _ _ (congr_fun h i : wrap _ (_:Cover)=_)
 have he:= congr_fun hp j; have ha:= (Braid.nams x (i,j)).trans hx; have hb:= (Braid.nams y (i,j)).trans hy
 change y (i,j)= x (i,j)+n.val • p j at he; by_cases hm:p j=0; · rw [he,hm,nsmul_zero,add_zero]
 exfalso; rw [nsmul_eq_mul] at he
 by_cases h:p j<0
 · have hv := mul_le_mul_of_nonneg_left (show p j ≤ -1 from by omega) (show 0≤ (n.val:ℤ) by positivity); omega
 have hv := le_mul_of_one_le_right (show 0≤ (n.val:ℤ) by positivity) (show 1 ≤ p j from by omega); omega
end YM.CF.Rel
