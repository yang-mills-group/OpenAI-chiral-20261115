import YM.Hilbert.Kolmogorov
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import YM.OS.Core
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Vacancy
open Set Function Filter Metric Finset ContinuousLinearMap
open scoped Topology NNReal InnerProductSpace BigOperators
/-!
# Coarse group ergodic facts: shifted discrete averaging

Tools for trying joint-invariant selection by placement rather than Lorentz
rotation. Only Hilbert technology, isolated from implementation and topology
of phase-candidate spectrum. **No continuity of spatial shifts used**. NNReal
times via consumers.
-/
-- uniform finite averages, can reorder across indices. use nonempty parameter to avoid avg of empty; later N+1.
namespace Average
variable {A B:Type*}[Fintype A][Fintype B]{U Y:Type*}[NormedAddCommGroup U][NormedSpace ℂ U][NormedAddCommGroup Y][NormedSpace ℂ Y]
noncomputable def center(f:A→U):U:= ((Fintype.card A:ℂ)⁻¹) • ∑ i:A,f i
lemma eq_of(f g:A→U)(p:∀i,f i=g i):center f=center g:=congrArg _ (funext p)
lemma plus(f g:A→U):center (fun x=>f x+g x)=center f+center g:=by unfold center; rw [Finset.sum_add_distrib,smul_add]
lemma minus(f g:A→U):center (fun x=>f x-g x)=center f-center g:=by unfold center; rw [Finset.sum_sub_distrib,smul_sub]
lemma constant[Nonempty A](q:U):center (fun _:A=>q)=q:=by
 unfold center; simp_rw [Finset.sum_const,Finset.card_univ]
 rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul]; rw [inv_mul_cancel₀ (by simp),one_smul]
lemma norm_worth{f:A→U}[Nonempty A]{c:ℝ}(h:∀i,‖f i‖≤c):‖center f‖≤ c:=by
 unfold center; have hp:0 < ((Fintype.card A:ℕ):ℝ):=by exact_mod_cast Fintype.card_pos
 have he: ‖∑ i:A,f i‖≤ ∑ i:A,c:=(norm_sum_le ..).trans (Finset.sum_le_sum (fun i t=> h _))
 rw [norm_smul,norm_inv, Complex.norm_natCast]; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at he
 refine le_trans (mul_le_mul_of_nonneg_left he (by positivity)) ?_; rw [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]
lemma norm_dist{f g:A→U}[Nonempty A]{c:ℝ}(h:∀i,dist (f i) (g i)≤c):dist (center f) (center g) ≤ c:=by rw [dist_eq_norm,←minus]; apply norm_worth; simpa [dist_eq_norm] using h
lemma natural (f:A→U)(L:U→L[ℂ]Y): center (fun i:A=>L (f i))=L (center f):=by unfold center; simp
lemma trade(L:A≃B)(f:B→U):center (fun i=>f (L i))=center f:=by unfold center; rw [Fintype.card_congr L,Equiv.sum_comp]
lemma domino(f:A×B→U): center f=center (fun i:A=>center (fun j:B=> f (i,j))):=by
 unfold center; rw [Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]; rw [← Finset.smul_sum, smul_smul,mul_inv_rev,mul_comm]
lemma fubini(f:A→B→U):center (fun i=>center (f i))=center (fun j=>center (fun i=>f i j)):=by
 calc
    _=center (fun (i:A×B)=>f i.1 i.2) := (domino (fun i:A×B=>f i.1 i.2)).symm
    _=_ := by rw [← trade (Equiv.prodComm B A),domino]; rfl
end Average

-- Players can represent here; instead use I -> copy of abstract orbit
structure Rolls (H:Hilbert) where
 wind:ℤ→ H.Op
 small(i:ℤ): ‖wind i‖ ≤1
 along(i j:ℤ):(wind i).comp (wind j)=wind (i+j)
 nil:wind 0=ContinuousLinearMap.id ℂ _
namespace Rolls
variable {H:Hilbert}(P:Rolls H)
open Average
lemma paved(i j:ℤ)(x:H):P.wind i (P.wind j x)=P.wind (i+j) x:=by rw [← ContinuousLinearMap.comp_apply,P.along]
lemma inverse(i:ℤ)(x:H):P.wind i (P.wind (-i) x)=x:=by rw [P.paved,add_neg_cancel,P.nil]; rfl
lemma solid(i:ℤ)(x:H): ‖P.wind i x‖=‖x‖:=by
 have hp (i:ℤ)(x:H):‖P.wind i x‖≤‖x‖:= ((P.wind i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (P.small _))
 refine le_antisymm (hp i x) ?_; have h:=hp (-i) (P.wind i x); rwa [P.paved,neg_add_cancel,P.nil] at h
lemma dist_eq (i:ℤ)(x y:H):dist (P.wind i x) (P.wind i y)=dist x y:=by rw [dist_eq_norm,←map_sub,solid,dist_eq_norm]
private abbrev locus := ((P.wind 1).eqLocus (1:H.Op))
noncomputable def calm : H.Op:= (locus P).starProjection
lemma calmB(i:ℕ)(x:H):(⇑(P.wind 1))^[i] x=P.wind (i:ℤ) x:=by induction i with
 | zero=>rw [Nat.cast_zero,P.nil]; rfl
 | succ i h=>rw [Function.iterate_succ_apply',h,P.paved,Nat.cast_add_one,add_comm]
private lemma eqshap {x:H}: x∈locus P ↔ P.wind 1 x=x:= Iff.rfl
lemma calm_hit{i:H}:P.wind 1 (P.calm i)=P.calm i:=P.eqshap.mp ((locus P).starProjection_apply_mem _)
lemma calm_mem (i:H):P.calm i=i↔∀x:ℤ,P.wind x i=i:=by
 rw [calm,Submodule.starProjection_eq_self_iff,P.eqshap]; constructor
 · intro hx
   have h(n:ℕ):P.wind (n:ℤ) i=i:=by induction n with
     | zero=>rw [Nat.cast_zero,P.nil]; rfl
     | succ n v=> rw [Nat.cast_add_one,←P.along,ContinuousLinearMap.comp_apply,hx,v]
   intro x; cases x with
   | ofNat n=>exact h n
   | negSucc n=>
       let k:= (n+1:ℕ); change P.wind (-(k:ℤ)) i=i
       have he:=P.inverse (-(k:ℤ)) i; rw [neg_neg,h] at he; exact he
 exact fun f=>f 1
lemma projected (j:ℤ)(x:H): P.wind j (P.calm x)=P.calm x:=((P.calm_mem _).mp (by unfold calm; rw [Submodule.starProjection_eq_self_iff]; apply Submodule.starProjection_apply_mem)) _
-- use Finset.range directly compare with univ. 
lemma one_lane (x:H) : Tendsto (fun i:ℕ=>center (fun j:Fin (i+1)=> P.wind j x)) atTop (𝓝 (P.calm x)):=by
 have h: Tendsto (fun i:ℕ=> birkhoffAverage ℂ (P.wind 1) _root_.id (i+1) x) atTop (𝓝 (((P.wind 1).eqLocus (1:H.Op)).orthogonalProjectionOnto x : H)):=
    ((P.wind 1).tendsto_birkhoffAverage_orthogonalProjection (P.small _) x).comp (tendsto_add_atTop_nat 1)
 apply h.congr; intro n
 unfold birkhoffAverage birkhoffSum Average.center
 rw [Fintype.card_fin,Fin.sum_univ_eq_sum_range (fun i:ℕ=>P.wind i x)]; simp [calmB]
lemma shifted (p:ℕ→ℤ)(x:H) : Tendsto (fun i:ℕ=>center (fun j:Fin (i+1)=> P.wind (p i+j) x)) atTop (𝓝 (P.calm x)):=by
 rw [tendsto_iff_dist_tendsto_zero]
 have hx:= (tendsto_iff_dist_tendsto_zero.mp (P.one_lane x))
 apply hx.congr; intro n
 have hf(i:Fin (n+1)): P.wind (p n + ↑↑i) x=P.wind (p n) (P.wind (i:ℤ) x):= (P.paved ..).symm
 rw [Average.eq_of _ _ hf,natural]
 nth_rw 2 [← P.projected (p n) x]
 rw [P.dist_eq]
-- covers any centers (velocities needn't bounded), with inputs varying convergently
lemma steers (p:ℕ→ℤ){x:ℕ→H}{y:H}(h:Tendsto x atTop (𝓝 y)):
 Tendsto (fun i=>center (fun j:Fin (i+1)=> P.wind (p i+j) (x i))) atTop (𝓝 (P.calm y)):=by
 apply Metric.tendsto_nhds.mpr; intro ε e
 filter_upwards [Metric.tendsto_nhds.mp (P.shifted p y) (ε/2) (by positivity), Metric.tendsto_nhds.mp h (ε/2) (by positivity)] with i a v
 let W t:=center (fun j:Fin (i+1)=>P.wind (p i+j) t)
 apply lt_of_le_of_lt (dist_triangle _ (W y) _)
 have he: dist (W (x i)) (W y) ≤dist (x i) y:=Average.norm_dist fun j=> (P.dist_eq ..).le; change dist (W y) _ < ε/2 at a; change dist (W (x i)) (W y)+dist (W y) _< ε; linarith

lemma calm_commutes {L:H.Op}(h: ∀ i, L.comp (P.wind i)=(P.wind i).comp L): L.comp P.calm=P.calm.comp L:=by
 ext1 x
 have ht:= P.one_lane x
 have hp:= P.one_lane (L x)
 have hr: Tendsto (fun i:ℕ=>center (fun j:Fin (i+1)=>P.wind j (L x))) atTop (𝓝 (L (P.calm x))):=by
   simp only [← ContinuousLinearMap.comp_apply (P.wind _) L,←h, ContinuousLinearMap.comp_apply]
   simp only [natural]
   exact L.continuous.continuousAt.tendsto.comp ht
 exact tendsto_nhds_unique hr hp
end Rolls
end YM.CF.Buffered.Afterglow.Tower.Vacancy
