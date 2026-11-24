import YM.SU5.Relativistic.Schist
import YM.SU5.Fineness.Chalice

/-!
# Compare the sales heights using unbounded order at flat Saber
- May purchase the order as function of all the parameters; the letter (site mode) estimate still available at that same price.
- In distinguishing cost here from the more delicate actual Orbit wind in Rebuke.lean, do NOT require atTop comparison from gram reals at all witnessing schools. Pay via all-entry estimates on S (after one gauge). This lemma exposes that geometric receipt explicitly.
-/
set_option autoImplicit false
set_option maxHeartbeats 530000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]

/- combining entry budgets with glow cost -/
def revE (A:Op I):ℝ:= ∑ i, ∑ j, ‖A i j‖
lemma revE_ge (A:Op I): 0 ≤ revE A:=sum_nonneg fun _ _=> sum_nonneg fun _ _=> norm_nonneg _
lemma revE_cols (A:Op I) : revE A= ∑ i,∑ j, ‖A j i‖:= sum_comm
private lemma trace_offer (X Y:Op I) {R:ℝ}(h:∀ i j:I, ‖X i j‖ ≤ R) : ‖Matrix.trace (X*Y)‖ ≤ R*revE Y:=by
 unfold Matrix.trace; apply (norm_sum_le ..).trans; rw [revE_cols,mul_sum]; apply sum_le_sum; intro i hi
 rw [mul_sum]; refine le_trans (norm_sum_le _ _) (sum_le_sum ?_); intro j hj
 exact (norm_mul (X i j) (Y j i)).trans_le (mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _))

structure ColumnDeal (A:Op I)(z:ℝ) :Prop where
 all (i:I):‖acts A (basisKet i)‖ ≤ z
lemma ColumnDeal.more (A:Op I){E f:ℝ} (p:ColumnDeal A E)(h:E≤f):ColumnDeal A f:=⟨fun i=>(p.all i).trans h⟩
lemma ColumnDeal.charge (A:Op I){z:ℝ}(p:ColumnDeal A z)(x:Ket I) : ‖acts A x‖ ≤ Gall.dialZ x * z := by
 nth_rw 1 [←basis_expand x]; rw [map_sum]; apply (norm_sum_le ..).trans; rw [Gall.dialZ, sum_mul]; apply sum_le_sum; intro i _; rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (p.all i) (norm_nonneg _)
lemma ColumnDeal.scroll {A:Op I}{z:ℝ}(p:ColumnDeal A z)(i j:I) : ‖(star A*A) i j‖ ≤ z^2:=by
 calc
    _ = ‖inner ℂ (acts A (basisKet i)) (acts A (basisKet j))‖:=by
       rw [←basis_act (star A*A),←basis_inner,act_mul,←act_inner,star_star]
    _ ≤ _ := (norm_inner_le_norm ..).trans (by rw [pow_two]; exact mul_le_mul (p.all i) (p.all j) (norm_nonneg _) ((norm_nonneg _).trans (p.all i)))
-- determinant pricing adapted Raspa.sat.
private lemma entrySat (V:Op I) (p:0≤V): ‖V.det‖ ≤ Real.exp ((V-1).trace.re):=by
 obtain ⟨U,d,e⟩:= spectral_exists V (IsSelfAdjoint.of_nonneg p); subst V; rw [←spectral_zero U,spectral_le] at p
 rw [← spectral_one U,spectral_sub,spectral,spectral,det_twist,trace_twist,Matrix.trace_diagonal, Matrix.det_diagonal,norm_prod]; push_cast -- tune
 have he(i:I): ‖(↑(d i):ℂ)‖ ≤ Real.exp (d i-1):=by have hx:= Real.add_one_le_exp (d i-1); rw [Complex.norm_real, Real.norm_of_nonneg (p i)]; linarith
 rw [show ( (∑ i:I, (↑((d-1) i):ℂ):ℂ)).re= (∑ i:I, (d i-1)) from (?_), Real.exp_sum]
 · exact prod_le_prod (fun i _=> norm_nonneg _) (fun i _=>he i)
 rw [←Complex.ofReal_sum,Complex.ofReal_re]; rfl
lemma sea_gain (Q P:Op I)(R:Shaft I)(f:Wave I)(E:ℝ)(p:IsStarProjection P)(q:IsStarProjection Q)(t:Sea P f)(h:ColumnDeal R.sell E) (u:R.sell*Q=Q):
  ‖acts (quant R.sell) f‖ ≤ Real.exp ((E^2+1)*revE (P-Q)/2):=by
 let S:=R.sell; let X:= acts (quant S) f; let W:=star S*S; let Y:= P*W*P+(1-P)
 have hX:‖X‖^2=‖Y.det‖:=by
    have hx: Matrix.det Y=inner ℂ X X:=by
       rw [show Matrix.det Y=skyGlow f W f from (meadow p f t _).symm,skyGlow]; unfold W; rw [quant_mul,quant_star,act_mul]; unfold X; rw [←act_inner,star_star]
    rw [hx,inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg X)]
 let A:= W-1
 have hg: (Y-1).trace= (A*(P-Q)).trace:=by
    have he:star (S*Q)=star Q:= congrArg star u
    rw [star_mul] at he; rw [show star Q=Q from q.isSelfAdjoint] at he
    have ht: Q*W*Q=Q:=by unfold W; rw [←mul_assoc,he,mul_assoc, show S*Q=Q from u,show Q*Q=Q from q.isIdempotentElem.eq]; -- he tune
    have hf(U:Op I)(h:IsStarProjection U):(U*W*U+(1-U)-1).trace=(A*U).trace:=by
      unfold A; rw [sub_mul,one_mul]; rw [show U*W*U+(1-U)-1=U*W*U-U from by abel, Matrix.trace_sub, Matrix.trace_sub]; rw [mul_assoc,Matrix.trace_mul_comm U, mul_assoc W,h.isIdempotentElem.eq]
    unfold Y; rw [hf P p,mul_sub,Matrix.trace_sub,←hf Q q, ht, add_sub_cancel, sub_self, Matrix.trace_zero,sub_zero]
 have hf(i j:I): ‖A i j‖ ≤ E^2+1 := by
    unfold A; rw [Matrix.sub_apply]; apply (norm_sub_le ..).trans; refine add_le_add (h.scroll i j) ?_; simp [Matrix.one_apply]; split <;> norm_num
 let O:ℝ:=(E^2+1)*revE (P-Q)
 have he:(Y-1).trace.re ≤ O:= hg ▸ (Complex.re_le_norm _).trans (trace_offer A _ hf)
 apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (Real.exp_pos _).le; change ‖X‖^2 ≤ Real.exp (O/2)^2; rw [hX]; apply (entrySat Y ?_).trans; swap
 · apply add_nonneg _ p.one_sub.nonneg; exact le_trans (star_mul_self_nonneg (S*P)) (le_of_eq (by rw [star_mul, p.isSelfAdjoint]; unfold W; noncomm_ring)) -- tune
 rw [←Real.exp_nat_mul]; push_cast; exact Real.exp_monotone (he.trans_eq (by ring))

-- Budget on the Dyn
namespace Shaft
variable (T: Shaft I) (u:ℝ)
def glowHom : FC I →+* FC I where
 toFun:= T.glow
 map_mul':=T.glow_mult
 map_add':=T.glow_sum
 map_one':=T.glow_nil
 map_zero':=T.glow_zero
lemma glowExp (B:FC I): T.glow (exp B)=exp (T.glow B):=by
 letI : NormedAlgebra ℚ (FC I) := NormedAlgebra.restrictScalars ℚ ℂ (FC I)
 have hc: Continuous ⇑(T.glowHom):=by change Continuous fun x:FC I=> quant T.sell*x*quant T.buy; fun_prop
 exact map_exp (T.glowHom) hc B

variable (X:ColumnDeal T.sell u)(Y:ColumnDeal (star T.buy) u)
include X Y
lemma tag_glow [Nonempty I] (P:Op I)(v:ℝ)(h:0≤u)(e:0≤v)(p:∀ i:I, Gall.dialZ (acts P (basisKet i)) ≤ v)(i:LeanV I):
 ‖T.glow (Pastry.drawT P i)‖ ≤ (v+1)*u:= by
 unfold Pastry.drawT; split
 · rw [seekF,prong_p, T.glow_up]; let V:= acts (1-P) (basisKet i.2)
   apply ((Flare.cost_pe false _).trans (X.charge _ V)).trans; refine mul_le_mul_of_nonneg_right ?_ h; unfold V; rw [act_sub,act_one]; refine (Graph.pony ..).trans ((add_le_add (show Gall.dialZ _ ≤ 1 from ?_) (p _)).trans_eq (add_comm 1 v))
   simp [Gall.dialZ,apply_ite (fun x:ℂ=> ‖x‖)]
 rw [hideF,prong_t,T.glow_down]; let V:=acts P (basisKet i.2)
 exact (Flare.cost_pe true _).trans ((Y.charge _ V).trans (mul_le_mul_of_nonneg_right ((p _).trans (by linarith)) h))
lemma dg_glow (A:Op I)(h:0≤u): ‖T.glow (dg A)‖ ≤ u^2*revE A:= by
 unfold dg dyad; change ‖(T.glowHom) _‖≤_; rw [map_sum]; apply (norm_sum_le ..).trans; unfold revE; rw [mul_sum]; apply sum_le_sum; intro i _; rw [map_sum,mul_sum]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro j _
 change ‖T.glow (A i j • (put i*takeF j))‖≤_; rw [T.glow_free,T.glow_mult, norm_smul]
 rw [←create_put,←remove_take,T.glow_up,T.glow_down,mul_comm (u^2)]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); refine (norm_mul_le ..).trans ?_; rw [pow_two]; exact mul_le_mul ((Flare.cost_pe false _).trans (X.all i)) ((Flare.cost_pe true _).trans (Y.all j)) (norm_nonneg _) h
end Shaft

end YM.CF.Papyrus.Franc
