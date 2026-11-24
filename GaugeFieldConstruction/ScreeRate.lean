import GaugeFieldConstruction.Trapeze
import YM.CF.Kea.Cool
import YM.CF.Flare.Coda
import GaugeFieldConstruction.WingGate
/-! # P3 similarity on exact momenta. Never set momentum 0 in cost receive phase. -/
set_option autoImplicit false
set_option maxHeartbeats 30000
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Fock.Flux
open Function Filter Metric NormedSpace Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {j:ℕ} {r C:ℝ}
variable {N:Side}
private lemma snowflake (r:ℝ)(x:Site N)(h:amplitude x ≤ r): (fun i:Axis=> chert (x i))∈Lattice.box ⌈r/(pinch N)⌉₊:=by
 let c:=pinch N; let K:=⌈r/c⌉₊; have hp:0<c:=pinch_pos N; have h':c≤ r:= (amplitude_pin _).trans h
 have hx(i:Axis) : (-(K:ℤ)) ≤ chert (x i) ∧ chert (x i) ≤ (K:ℤ):=by
    let p:=Lat.principal (x i); let v:=chert (x i)
    have ht: |p|≤r:= (norm_le_pi_norm (pm x) i).trans h
    have hg: p=(2*(v:ℝ)+1)*c:=ch_price (x i); have hQ:r≤K*c:= (div_le_iff₀ hp).1 (Nat.le_ceil _); obtain ⟨hl,hr⟩:=abs_le.mp ht
    have hK: (1:ℝ) ≤ K:= (one_le_div hp|>.mpr h').trans (Nat.le_ceil _)
    change -(K:ℤ) ≤ v∧v≤ (K:ℤ); have hu : -(K:ℝ) ≤ v ∧ (v:ℝ)≤ K:=by
       constructor
       · apply le_of_mul_le_mul_right _ hp; linarith only [hl,hg,mul_le_mul_of_nonneg_right hK hp.le,hQ]
       apply le_of_mul_le_mul_right _ hp; nlinarith only [hr,hg,mul_le_mul_of_nonneg_right hK hp.le,hQ,hp]
    exact ⟨by exact_mod_cast hu.1,by exact_mod_cast hu.2⟩
 exact box_test.mpr ⟨fun i=> (hx i).1,fun i=> (hx i).2⟩
abbrev leafLens (N:Side)(r:ℝ): Finset (Site N):= univ.filter (fun i=>amplitude i ≤ r)
lemma lens_black (p:r<pinch N) : leafLens N r=∅:= by apply Finset.eq_empty_iff_forall_notMem.mpr; intro i h; exact not_le.mpr p ((amplitude_pin i).trans (mem_filter.mp h).2)
lemma lens_bounds (N:Side)(r:ℝ)(p:0≤r) : ((leafLens N r).card:ℝ) ≤ (5*(r/pinch N))^4:=by
 let f(x:Site N):= fun i: Axis=> chert (x i); let c:=pinch N; let y:= r/c
 by_cases g:r<c
 · rw [lens_black g,card_empty,Nat.cast_zero]; positivity
 have hy:1≤ y:= (one_le_div (pinch_pos N)).mpr (le_of_not_gt g)
 let K:= ⌈y⌉₊; let A:= Lattice.box K
 have ht:Injective f:= by
    intro x z h; funext i; apply prin_inj; rw [ch_price,ch_price,show chert (x i)=chert (z i) from congrFun h i]
 have he:(leafLens N r).card ≤ (K+K+1)^4:=by
    have hp:(leafLens N r).image f⊆ A:=by rintro t p; obtain ⟨x,h,rfl⟩:=mem_image.mp p; exact snowflake r x (mem_filter.mp h).2
    rw [←card_image_of_injective _ ht]; exact (card_le_card hp).trans_eq (by first|exact Corona.box_size _|simp [A])
 have hh: (K:ℝ) ≤ 2*y:=by have hg':(K:ℝ)≤y+1:=(Nat.ceil_lt_add_one (zero_le_one.trans hy)).le; linarith
 refine (Nat.cast_le.mpr he).trans ?_; push_cast; gcongr; change _ ≤ 5*y; linarith only [hh,hy]

def facet_sum (N:Side)(r:ℝ)(f:Site N → ℝ):= (pinch N)^4 * ∑ i∈ leafLens N r, (f i)^2
lemma facet_stop (N:Side)(r:ℝ)(p:0≤r)(t:0≤ C)(f:Site N→ℝ)(g:∀ i, |f i|≤ C/amplitude i) : facet_sum N r f ≤ 5000*C^2*r^2:=by
 let c:=pinch N; have hp:0<c:=pinch_pos _; obtain ⟨n,hn⟩:=exists_nat_gt (r/c)
 suffices hz:∀ (m:ℕ)(r:ℝ),0≤r → r < 2^m * c → facet_sum N r f ≤ 5000*C^2*r^2 by
    apply hz n r p; apply lt_of_lt_of_le ((div_lt_iff₀ hp).1 hn); have hx: n < 2^n:= Nat.lt_two_pow_self; apply mul_le_mul_of_nonneg_right (by exact_mod_cast hx.le) hp.le
 intro m; induction m with
 | zero =>
    intro r hr p; rw [pow_zero,one_mul] at p; unfold facet_sum; rw [lens_black p]; simp; positivity -- tune
 | succ m ih =>
    intro r hr h
    by_cases e:r < c
    · unfold facet_sum; rw [lens_black e]; simp; positivity
    let y:=r/2; have hv:0<r:= hp.trans_le (le_of_not_gt e); have hy:0 < y:=half_pos hv; have hw:y < 2^m * c:=by unfold y; rw [pow_succ'] at h; linarith only [h]
    let s:=leafLens N r; let a:=leafLens N y
    have he:a⊆ s:= fun i p=> mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp p).2).trans (half_le_self hr)⟩
    have hk: (∑ i∈ s\a,(f i)^2) ≤ (s.card:ℝ)* (C/y)^2:=by
       have ht: (s\a).card ≤ s.card:= card_le_card sdiff_subset
       apply le_trans (sum_le_sum (g:=fun _=> (C/y)^2) ?_) ?_
       · intro i h; have hp: y<amplitude i:=lt_of_not_ge (fun p=> (mem_sdiff.mp h).2 (mem_filter.mpr ⟨mem_univ _,p⟩)); rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ((g i).trans (div_le_div_of_nonneg_left t hy hp.le)) 2
       · rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) (sq_nonneg _)
    have hu:= ih y hy.le hw; have hb: c^4* ((s.card:ℝ)*(C/y)^2) ≤ (5^4*4)*C^2*r^2:=by
       apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (lens_bounds N r hr) (sq_nonneg _)) (pow_nonneg hp.le 4)).trans (le_of_eq ?_); change c^4*((5* (r/c))^4 *(_/y)^2)=_; unfold y; field
    unfold facet_sum; change c^4*(∑ i∈s,_ )≤_; rw [←sum_sdiff he,mul_add]; apply (add_le_add ((mul_le_mul_of_nonneg_left hk (pow_nonneg hp.le 4)).trans hb) hu).trans; unfold y; nlinarith only [show 0 ≤ C^2*r^2 by positivity]
lemma momentum_duty (N:Side)(r:ℝ)(p:0≤r)(t:0≤ C)(f:Site N→ℝ)(g:∀ i, |f i|≤ C/amplitude i) : (∑ i∈ leafLens N r, (f i)^2)/(N.val:ℝ)^4 ≤ 5000*C^2*r^2:=by
 have he:= facet_stop N r p t f g; apply le_trans _ he; let F:=∑ i∈ leafLens N r,(f i)^2; have hp: 1/(N.val:ℝ) ≤ pinch N:= div_le_div_of_nonneg_right (by linarith [Real.pi_gt_three]: 1≤Real.pi) (Nat.cast_nonneg _); change F/_ ≤ (pinch N)^4*F; have hh: (1:ℝ)/(N.val:ℝ)^4=(1/(N.val:ℝ))^4:=by rw [div_pow,one_pow]
 rw [show F/(N.val:ℝ)^4= (1/(N.val:ℝ)^4)*F by ring,hh]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) (sum_nonneg fun _ _=> sq_nonneg _)

-- Exact Fourier projectors on *one-particle* HY costs.
abbrev trims_lo (N:Side)(r:ℝ)(x:Stag N):Op SpinIdx:= if x.1∈ leafLens N r then 1 else 0
abbrev lowCut (N: Side)(r:ℝ): Op (Single N):= Dofu N (trims_lo N r)
theorem low_project (N:Side)(r:ℝ): IsStarProjection (lowCut N r):=by
 let H:=trims_lo N r; have he:H*H=H:=funext fun i=>by change H i* H i=H i; unfold H trims_lo; split_ifs <;> simp
 have hh:star H=H:=funext fun i=>by change star (H i)=H i; unfold H trims_lo; split_ifs <;> simp
 exact ⟨by unfold lowCut IsIdempotentElem; rw [←map_mul, he],by unfold lowCut IsSelfAdjoint; rw [← Dofu_s, hh]⟩
lemma low_pi (N:Side)(h:Even N.val): lowCut N Real.pi=1:=by rw [lowCut,show trims_lo N Real.pi=1 from funext fun i=> if_pos (show i.1∈ leafLens N Real.pi from mem_filter.mpr ⟨mem_univ _,amplitude_top h i.1⟩),map_one]
lemma band_moves (N:Side)(r:ℝ)(T:Stag N→Op SpinIdx): Commute (lowCut N r) (Dofu N T):= by
 unfold Commute SemiconjBy lowCut; rw [←map_mul,←map_mul]; refine congrArg _ (funext (fun i:Stag N=>?_)); change trims_lo N r i*T i=T i*trims_lo N r i; unfold trims_lo; split_ifs <;> simp
def ScaleFunds (C:ℝ)(A:Stag N→Op SpinIdx):Prop:=0 ≤ C ∧ ∀ i, ‖A i‖ ≤ C/amplitude i.1
theorem ScaleFunds.miss (N:Side)(r:ℝ)(p:0 ≤ r)(T: Stag N→Op SpinIdx)(u:ScaleFunds C T) (i:Single N): ‖acts (lowCut N r * Dofu N T) (basisKet i)‖ ≤ 100*C*r:=by
 rw [lowCut,←map_mul]
 apply (sq_le_sq₀ (norm_nonneg _) (by have hp:=u.1; positivity)).1
 refine (Gall.wave ( (trims_lo N r)* T) i).trans ?_
 let L:= leafLens N r; let f(x:Site N):= ‖T (x,i.2)‖
 have he : (∑ j:Site N,‖(trims_lo N r * T) (j,i.2)‖^2)=∑ j∈L,f j^2:=by
    rw [← sum_subset (subset_univ L)]; apply sum_congr rfl; intro i p; rw [Pi.mul_apply]; change ‖_ * _‖^2=_; rw [trims_lo, if_pos (show _ from p),one_mul]
    intro j _ h; rw [Pi.mul_apply,trims_lo, if_neg h, zero_mul,norm_zero]; norm_num
 rw [he]; refine (momentum_duty N r p u.1 f (fun i=>by unfold f; rw [abs_of_nonneg (norm_nonneg _)]; exact u.2 _)).trans ?_; nlinarith only [show 0 ≤ C^2*r^2 by positivity]
theorem ScaleFunds.highPrice (N:Side)(r:ℝ)(p:0 < r)(T: Stag N→Op SpinIdx)(u:ScaleFunds C T) : ‖(1-lowCut N r)* Dofu N T‖ ≤ C/r:=by
 let H:= trims_lo N r; rw [lowCut, ← show Dofu N (1:Stag N→Op SpinIdx)=1 from map_one _,←map_sub,←map_mul]; apply markQ _ (div_nonneg u.1 p.le) ; intro i; change ‖(1-H i)* _‖ ≤ _; unfold H trims_lo; split
 next k=> rw [sub_self,zero_mul,norm_zero]; exact div_nonneg u.1 p.le
 next k=> rw [sub_zero,one_mul]; apply (u.2 i).trans; exact div_le_div_of_nonneg_left u.1 p (le_of_not_ge (fun h=> k (mem_filter.mpr ⟨mem_univ _,h⟩)))
end YM.CF.Fock.Flux
end
