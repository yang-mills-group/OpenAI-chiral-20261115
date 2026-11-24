import YM.SU5.Selected.Hill.Rocket
/-! Truncated frame dominates full operator on retained colors. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Hill.Box
open Function Filter Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree Calculus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
variable {G:Gauge}{n:Side}{r:Side}{B B' R:ℕ}
variable {W:PathData G}{C:Clip}{σ X D θ u A:ℝ}
variable {S:Lots n}{I:Type*}[Fintype I][DecidableEq I](f:I→EdgeT n)
-- zero outside injection space
def icing (v:Scene G I): ListT G n:= expand (vouch f G.ColorIndex) v
lemma walks_clear{ x: Site n}{p:Walk}(v:Scene G I)(h:∀ j:I,p.length<separation x (f j).1) : linkSum (Exterior.collect G (tin (icing f v))) x p=0:=by
 rw [tin,badge_out]; induction p generalizing x with
 | nil => rfl
 | cons a m ih=>
    let i:= a.used x
    have hp : colorup (icing f v) i=0 :=by
       ext j; change (icing f v) (i,j)=0; apply Calculus.displaced ..; intro y t; have he:= congrArg (fun (k:Pens G (EdgeT n))=> k.1.1) t; change (f y.1).1=i.1 at he; have hx:= h y.1; rw [he,List.length_cons] at hx; have h0:separation x i.1 ≤ 1:=go_by ..; omega
    rw [linkSum, ih (by
        intro j; have ht:=move_by a x; have hx:=separation_triangle x (x+a.vec) (f j).1; specialize h j; rw [List.length_cons] at h; omega)]; change (if a.neg then _ else colorup (icing f v) i)+0=0; split <;> simp [hp] <;> exact hp
-- pin vanishes even helper omits small side; induced retention contacts
lemma remote (p:∀ j:I,recess r 1 (f j).1)(v:Scene G I)(i:G.ColorIndex): pin ℝ n *ᵥ page (icing f v) i=0:=by
 funext j; rw [pin_apply]; apply sum_eq_zero; intro w _; refine displaced _ _ (fun u h=> ?_); have hp:= congrArg (fun k:Pens G (EdgeT n)=> k.1.1) h; change (f u.1).1=lineK n j w at hp; exact recess_pin j w (r:=r) (hp ▸ p u.1)
lemma quiet_ach (D:B+2*R+4≤ B')(F:∀ j,Light r S B' (f j).1)(b:Plane n)(h:b∉lesson r S B)(x:Scene G I){p:Bool}: drive R (tin (icing f x)) C W (b,p)=0:=by
 have ht(j:I): 2*R+4<separation b.1 (f j).1:=by by_contra! v; apply h; exact mem_filter.mpr ⟨mem_univ _,((F j).small (show 2*R+4+B ≤ _ from by omega)).sees ((separation_comm ..).le.trans v)⟩
 unfold drive; split
 next=>
    unfold curtailed; rw [←tsum_zero (α:=G.Color) (β:=ℕ)]; apply tsum_congr; intro k; unfold trimmed; split; rfl; next v=>
       rw [←slot_v,walks_clear,smul_zero]; intro j; have hv:=(not_lt.mp v); have hh:= slot_t (W.row b.2 k).2; specialize ht j; dsimp only at hv ⊢; omega
 next=>
    rw [faceCurl,←fundamental,walks_clear,smul_zero]; intro j; apply lt_of_le_of_lt ?_ (ht j) -- wrong order
    change 4≤_; omega
variable {H:Bed}(h:W.Bounds C σ X D)(g: Attached H W)(p: Floor H C n u A)
include g p h
lemma wick (v:ListT G n): let E:= Next.Fluctuations.xLin C W (tin v); v ⬝ᵥ (story (pasture (H.metric.acts n)) G.ColorIndex*ᵥ v)= sail E ^2:=by
 intro E; rw [dotted]; simp_rw [profiled,tinsel]; change Bid.gaugeFiscal H (tin v) (tin v)=_; rw [metric_pair H h g _ _ p,Tail.quadratic,Fintype.sum_prod_type (f:=fun i:Twin n=> ‖E i‖^2)]; apply sum_congr rfl; intro i _; unfold E; rw [Fintype.sum_bool]; simp only [Next.Fluctuations.xLin,Bool.false_eq_true,↓reduceIte,norm_smul,real_inner_self_eq_norm_sq, Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt C.quadratic_pos.le]; rw [add_comm]
-- room for approximating cutoff. relative directly
lemma applause_prec (x:Scene G I)(p':0≤θ)(q:θ≤1)(t:B+2*R+4 ≤ B')(z:∀ i:I,Light r S B' (f i).1)(v: Tail.rate_ell σ X R /C.direct ≤ θ^2): (1-θ)^2*(x ⬝ᵥ cred f G H*ᵥ x) ≤ x ⬝ᵥ ((flare R (lesson r S B) h).submatrix (vouch f G.ColorIndex) (vouch f G.ColorIndex))*ᵥ x:=by
 let a:= icing f x; let f':=tin a; let L:= Next.Fluctuations.xLin C W f'; let K:= prize R (lesson r S B) C W a; have hp0:cred f G H=(story (canopy n H) G.ColorIndex).submatrix (vouch f _) (vouch f _):=rfl
 rw [hp0, Calculus.expansion, Calculus.expansion]; change (1-θ)^2*(a ⬝ᵥ ((story (canopy n H) G.ColorIndex)*ᵥ a))≤ a ⬝ᵥ ((flare R (lesson r S B) h)*ᵥ a); have he:a ⬝ᵥ ((story (canopy n H) G.ColorIndex)*ᵥ a)=sail L^2:=by
    rw [← wick (H:=H) h g p a,dotted,dotted]; simp_rw [profiled]; apply sum_congr rfl; intro i _; rw [canopy, Matrix.add_mulVec,← mulVec_mulVec,show pin ℝ n *ᵥ _=0 from remote f (r:=r) (fun i=> ((z i).small (B:=B') (R:=1) (by omega)).1) x i, Matrix.mulVec_zero,add_zero] -- tune
 rw [he,flash_ok,applause]; change (1-θ)^2*(sail L)^2≤ (sail K)^2
 let U:= drive R f' C W
 have hK:K=U:= by funext i; unfold K prize; split; rfl; next u=> exact (quiet_ach f (C:=C) t z i.1 u x).symm
 let Y:= fun b:Plane n=> faceCurl b f'; let Q:= tail_r W R Y; let M(i:Twin n):=if i.2 then Q i.1 else 0
 have h0:0<C.direct:= C.quadratic_pos; have hz:= show 0≤θ^2 from sq_nonneg _; have hA:L=U+M:=by funext i; unfold L U M Next.Fluctuations.xLin drive; rw [Pi.add_apply]; split; apply curtailed_bill h; rw [add_zero]
 let f₀:= ∑ i:Plane n, ‖Y i‖^2; have hT: C.direct*f₀ ≤ (sail L)^2:=by rw [Tail.quadratic,Fintype.sum_prod_type]; unfold f₀; rw [mul_sum]; apply sum_le_sum; intro i _; rw [Fintype.sum_bool]; change _≤ _ + ‖Real.sqrt C.direct • Y i‖^2; rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt h0.le]; exact le_add_of_nonneg_left (sq_nonneg _)
 have hM:sail M ≤ θ*sail L:=by
    apply (sq_le_sq₀ (sail_nn _) (mul_nonneg p' (sail_nn L))).mp; rw [mul_pow]; apply le_trans (b:=θ^2*(C.direct*f₀)) _ (mul_le_mul_of_nonneg_left hT hz); rw [Tail.quadratic,Fintype.sum_prod_type]; simp only [Fintype.sum_bool,M, Bool.false_eq_true,↓reduceIte,norm_zero,ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,zero_pow,add_zero]; rw [← _root_.mul_assoc]; exact (labor W h R Y).trans (mul_le_mul_of_nonneg_right ((div_le_iff₀ h0).mp v) (sum_nonneg fun _ _=>sq_nonneg _))
 rw [← mul_pow,hK]; apply pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr q) (sail_nn _)); linarith only [show sail L ≤ _ from hA ▸ join U M, hM]
lemma comparison (F:f.Injective)(p':0≤θ)(q:θ ≤1)(t:B+2*R+4 ≤ B')(z:∀ i:I,Light r S B' (f i).1)(v: Tail.rate_ell σ X R /C.direct ≤ θ^2): (1-θ)^2 • cred f G H ≤ (flare R (lesson r S B) h).submatrix (vouch f G.ColorIndex) (vouch f G.ColorIndex):=by
 let f':=vouch f G.ColorIndex; let Q:= (flare R (lesson r S B) h).submatrix f' f'; let U:=cred f G H
 have hp: Q.PosSemidef:= (squared _).submatrix _; have hU: U.IsHermitian:= by apply isHermitian_iff_isSymm.mpr; apply Calculus.symmetry; rw [transpose_submatrix,canopy,transpose_add,pasture_symm _ p.symmetric.1,transpose_mul,transpose_transpose] -- maybe goal after rw not rfl
 apply Matrix.le_iff.mpr; apply PosSemidef.of_dotProduct_mulVec_nonneg (hp.isHermitian.sub (hU.smul (show IsSelfAdjoint ((1-θ)^2) from star_trivial _))); intro x; rw [star_trivial,sub_mulVec,smul_mulVec,dotProduct_sub,dotProduct_smul]; exact sub_nonneg.mpr (applause_prec f h g p x p' q t z v)
end YM.Hill.Box
#print axioms YM.Hill.Box.comparison
