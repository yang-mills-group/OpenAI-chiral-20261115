import YM.SU5.Selected.Hill.Levy
/-! Upper price across all sufficiently cold x. Price scalable per flake. This is pure gauge only. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Post
open Function Filter Metric Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree Calculus Next.Rank.Axial Chene.Perks
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
open Next.SectorChange Luge SectorTools.PhysicalGaussianSwitch
open CF CF.BPress CF.Graph Box AnalyticBridge.Annulus1AD
variable {G:Gauge}{n:Side}{r:Side}{S:Lots n}{B' B R m:ℕ}
variable {P:BudgetPoint}{W:PathData G}{C:Clip}{σ X D θ ε τ b:ℝ}
variable (Z:ChartRatio G)(p:LocalRatio Z) (A:ℝ)
abbrev load(x:ℝ): ℕ:=16*melt x
private lemma relief(K:ℝ)(e:0<ε): ∀ᶠ x:ℝ in atTop,Λ₁ (side x) (load x)*(K*lscale x) ≤ ε:=by
 have hr:Tendsto (fun x=>1536*K*(lscale x)⁻¹) atTop (𝓝 0):=by simpa only [Function.comp_apply,mul_zero] using (tendsto_inv_atTop_zero.comp lscale_late).const_mul (1536*K)
 filter_upwards [hr.eventually (ge_mem_nhds e)] with x v; apply le_trans _ v; unfold Λ₁ load; push_cast; apply Eq.le; -- change powers
 rw [molten,stance_ x]; field_simp [(silver x).ne']; ring
include p
lemma saving (ε y:ℝ)(e:0<ε)(h:0<σ)(L:Next.Rank.Spindle.Rules G)(o:0<θ)(v: nearF G θ τ ≤ ε/4)(K:ℝ→ℝ)(rK:PL K) : ∀ᶠ x:ℝ in atTop,∀ (b:ℝ), b∈Set.Icc (x/2) (2*x) → ∀ (n:Side), (side x).val ≤n.val →∀ κ:ℝ,κ ≤ K x→∀ S:Lots n,
 fee₄ Z (side x) S (load x) (fee₂ S C L b X D θ (screen x) σ (temp x) κ (melt x)) τ θ b A ≤ 3*ε*bulk n+y*S.card:=by
 let k:=nearF G θ τ; obtain ⟨H,z,r⟩:= highB Z p A; let F(x:ℝ):=H*lscale x; let U(x:ℝ):=4*(lscale x^3)^4; let P(x:ℝ):= K x+U x*F x+(-y);
 have hP:PL P:= (rK.add (((PL.const _).mul ((PL.scale.pow _).pow _)).mul ((PL.const _).mul PL.scale))).add (PL.const _)
 filter_upwards [fee_window C L X D o h ε e,r,rain C P hP,relief H e] with x hf ht hr hh b u n t κ q S
 let D':=Λ₁ (side x) (load x); let N:=bulk n; let O:= Fintype.card (outside (side x) S (load x)); let B:=Board (side x) S (load x); have hz:0≤F x:=mul_nonneg z (silver x).le; have hu: (B.card:ℝ) ≤4*N:=by
    let f:= (columbia (side x) n).Free; let X:(↑B:Type)→ EdgeT n:=distil (side x) S (load x); rw [show 4*N=(quantity n:ℝ) from (bulk_edge n).symm]; exact_mod_cast (show B.card ≤ quantity n from (Fintype.card_coe _).ge.trans (Fintype.card_le_of_injective X (distil_inj (side x) S (load x)))) -- eq orientation
 have hg : (O:ℝ) ≤ D'*N+ U x * S.card:= by have hv:= tickets_ (B':=load x) t S; rw [stance_ x] at hv; exact hv
 have h₀:(O:ℝ)*glazeB Z b A ≤ ε*N+ (S.card * (U x * F x)) := calc
    _ ≤ (D'*N+U x*S.card)*F x := (mul_le_mul_of_nonneg_left (ht b u) (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right hg hz)
    _ ≤ _:=by linarith only [mul_le_mul_of_nonneg_right (show D'* F x ≤ ε from hh) (Nat.cast_nonneg (Fintype.card (Site n)) (α:=ℝ))] -- defeq
 have hS: (B.card:ℝ)*k ≤ ε*N:=by calc
    _ ≤ _ := mul_le_mul_of_nonneg_left v (Nat.cast_nonneg _)
    _ ≤ (4*N)*(ε/4) := mul_le_mul_of_nonneg_right hu (by positivity)
    _ = _ := by ring
 let u':=(daily C (temp x)); have hV:κ-b*u'+ U x* F x ≤ y :=by have h:=hr b u; change K x+U x*F x+(-y) ≤ b*u' at h; linarith
 change _+(B.card*k)+(O:ℝ)*_ ≤ _; unfold fee₂
 linarith only [hf b u n,h₀,hS,mul_le_mul_of_nonneg_right hV (Nat.cast_nonneg S.card (α:=ℝ))]
omit p
lemma volume_f(n:Side): (Fintype.card (Plane n):ℝ)= bulk n * Fintype.card PlaqAxes:=by unfold Plane Face; rw [Fintype.card_prod,Nat.cast_mul]
lemma revenue (ε:ℝ)(h:0<ε): ∃ y:ℝ,∀ (m:ℝ)(n:Side),∑ S:Lots n,Real.exp (m + y*S.card) ≤ Real.exp (m+ε*bulk n):=by
 have hh:Tendsto (fun x=> Real.exp x*(Fintype.card PlaqAxes:ℝ)) atBot (𝓝 0):=by simpa only [zero_mul] using Real.tendsto_exp_atBot.mul_const (Fintype.card PlaqAxes:ℝ)
 obtain ⟨y,p⟩:= (hh.eventually (ge_mem_nhds h)).exists; refine ⟨y,fun m n=>?_⟩; rw [Real.exp_add m]; -- which occurrence? tune
 let E:= Real.exp y; let Q:=Fintype.card (Plane n); have he:∑ S:Lots n,Real.exp (m+y*S.card)=Real.exp m*(E+1)^Q:=by
    simp_rw [Real.exp_add,mul_comm y,Real.exp_nat_mul,←mul_sum]; rw [show (E+1)^Q=∑ S:Lots n,E^S.card from ?_]
    exact (by simpa only [prod_const,card_univ,mul_one, prod_const_one,one_pow] using Fintype.prod_add (fun (_:Plane n)=>E) (fun _=>1)) -- direction
 rw [he]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; calc
 _ ≤ Real.exp E ^ Q := pow_le_pow_left₀ (by unfold E; positivity) (Real.add_one_le_exp _) _
 _ = _:= (Real.exp_nat_mul ..).symm -- calc next rhs inferred via p
 _ ≤ Real.exp (ε*bulk n) :=by unfold Q; rw [volume_f]; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_left p (Nat.cast_nonneg (Fintype.card (Site n)) (α:=ℝ))]
include p
-- independent age of T, uniform observation purchase in all forests at scale x. threshold enough. maybe extend upper to δ+x but ok.
theorem gel (u ε:ℝ)(a:0<u)(h:0<ε)(s:0<σ)(K:ℝ→ℝ)(r:PL K) : ∀ᶠ x:ℝ in atTop, (∀ (n:Side), 1<n.val→ (side x).val≤ n.val→∀ (b:ℝ), b∈Set.Icc (x/2) (2*x)→ ∀ (H:Bed) (W:PathData G)(P:BudgetPoint), Floor H C n u A→ Attached H W → W.Bounds C σ X D→ P.threshold=temp x →∀ κ:ℝ,κ ≤ K x → (∫ U:Config G n, service W C P b κ U∂prior G n) ≤ Real.exp (schedule Z n H b+ ε * bulk n)):=by
 let ε':= ε/4; have he:0<ε':= by unfold ε'; positivity
 obtain ⟨θ,τ,v,t,hx,w⟩:= windows_x (G:=G) (ε'/4) (by positivity); obtain ⟨y,f⟩:= revenue ε' he
 let L:= Classical.choice (Next.Rank.Spindle.charts G)
 filter_upwards [eventually_gt_atTop (0:ℝ), vilify C, embers C L Z s p X hx v,saving (σ:=σ) (D:=D) (X:=X) (C:=C) Z p A ε' y he s L v w K r] with x g hz ⟨m,n,k,q⟩ r₀ N₀ q' P₀ b v' H W P h₀ Q R u' κ D0
 let S:=melt x; let A:=8*S; let T:=load x; have hp :0<b:=lt_of_lt_of_le (half_pos g) v'.1; have hk:7≤A:=by unfold A S melt; omega
 apply le_trans (peak (r:=side x) Z L p R κ hp (B:=A) (B':=T) (R:=S) (θ:=θ) (by unfold T A load S melt; omega) (m:=S) (by unfold A S melt; omega) (by unfold A S melt; omega) hk (by rw [stance_,u']) m n v t (by rw [u']; exact hz) k a q' Q h₀ q); -- e inferred via m
 let V:= schedule Z N₀ H b+3*ε'*bulk N₀
 apply le_trans (sum_le_sum (g:=fun S:Lots N₀ => Real.exp (V+y*S.card)) fun i _=>?_); · apply le_trans (f V N₀); exact le_of_eq (by unfold V ε'; congr 1; ring)
 apply Real.exp_monotone; unfold V; rw [u']; linarith only [r₀ b v' N₀ P₀ κ D0 i]
end YM.Hill.Post
#print axioms YM.Hill.Post.gel
