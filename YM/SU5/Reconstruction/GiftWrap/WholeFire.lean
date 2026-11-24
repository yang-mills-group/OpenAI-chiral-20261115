import YM.SU5.Reconstruction.GiftWrap.Revolt
import YM.SU5.Reconstruction.UVPrice.Void
import YM.SU5.Reconstruction.Vermont.Playlist
import Mathlib.Analysis.Complex.Liouville
/-! # Gram-sector reasoning yields irreducible WORLD algebra if bought global capacity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Bouy
open Function Set Filter MeasureTheory Metric OS.Semigroup Boundary Picket Ravin BridgeClub Anvil Roy ConePrice Sail Ship Waltz Lens ContinuousLinearMap
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder
-- complex gluing
private lemma cement {F G:ℂ→ℂ} (hF:Continuous F)(hG:Continuous G) (X:AnalyticOnNhd ℂ F inside) (Y:AnalyticOnNhd ℂ G inside) (Z:∃ M:ℝ,∀ z:ℂ,‖F z‖≤M∧‖G z‖≤M)(a:∀ t:ℝ,F (sideways t)=G (sideways (-t))) (t:ℝ): F (sideways t)=F 0:= by
 let q(z:ℂ):= if 0 ≤ z.re then F z else G (-z); let A:= Complex.re ⁻¹' Ici 0; let B:= Complex.re ⁻¹' Iic 0
 have up(x)(h:0≤ (x:ℂ).re): q x=F x:= if_pos h
 have sl(u:ℝ): -(sideways u)= sideways (-u):= by simp [sideways]
 have down(x)(h:(x:ℂ).re ≤0): q x=G (-x):=by
    unfold q; split_ifs with k; swap; rfl
    have e:x= sideways (-x.im):= Complex.ext (by simp only [side]; linarith) (by simp [sideways]); exact ((congrArg F e).trans (a (-x.im))).trans (congrArg G (by rw [← sl, ← e]))
 have hg: Continuous (fun z:ℂ=> G (-z)):= hG.comp continuous_neg; have tq:B∪A=univ:= eq_univ_of_forall fun i => le_total i.re 0
 have he: Continuous q:= continuousOn_univ.mp (((hg.continuousOn.congr (fun z (t:z∈B)=> down z t)).union_of_isClosed (hF.continuousOn.congr (fun z (t:z∈A)=> up z t)) (isClosed_Iic.preimage Complex.continuous_re) (isClosed_Ici.preimage Complex.continuous_re)).mono (le_of_eq tq.symm)) -- arg order
 obtain ⟨M,m⟩:=Z
 have hp:Differentiable ℂ q:= differentiableOn_univ.mp (seam_cement (t:=0) (fun z _ v=>?_) he.continuousOn isOpen_univ)
 · have c : Bornology.IsBounded (Set.range q):= Metric.isBounded_iff_subset_closedBall (0:ℂ)|>.mpr ⟨M,by
     rintro _ ⟨x,rfl⟩; rw [mem_closedBall_zero_iff]; unfold q; split
     · exact (m x).1
     exact (m (-x)).2⟩
   rw [← up 0 (by simp),← up (sideways t) (by rw [side])]; exact hp.apply_eq_apply_of_bounded c _ _
 rcases lt_or_gt_of_ne v with r|r
 · apply ((Y (-z) (show -z∈inside from (by unfold inside; change 0<(-z).re; simpa))).differentiableAt.comp z (f:=fun z:ℂ=> -z) differentiableAt_id.neg).congr_of_eventuallyEq
   filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds r] with z k; exact down z (show z.re < 0 from k).le
 apply (X z r).differentiableAt.congr_of_eventuallyEq; filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds r] with z k; exact up z (show 0<z.re from k).le
variable {H:Hilbert} {a:Axis} (S:OS.Semigroup H a)
variable (Ω:H)(N:Net H)
local notation "P"=>parish N Ω
local notation "U"=> trans S
local notation "V"=> parcelUp S
variable (L:owns_it N Ω)(u:∀ x:E4,Picket.trans S x Ω=Ω)(h:∀ x:E4,∀ A∈N, parcelUp S x A∈N)
include L h u
lemma stationary (A:H.Op)(q:A∈ N.commutant)(t:E4) : (∀ i:Axis,i≠a→ t i=0) → U t (A Ω)=A Ω:=by
 let y:= t a; intro e
 have ht:t=y •basis a:=by ext i; unfold y; by_cases h:i=a <;> simp[*]
 apply ext_inner_left ℂ; intro x; let B:=(innerSL ℂ ((U t) (A Ω))) - (innerSL ℂ (A Ω))
 suffices hy:B x=0 by
    rw[← inner_conj_symm,show inner ℂ x (A Ω)=starRingEnd ℂ (inner ℂ (A Ω) x) from (inner_conj_symm ..).symm,sub_eq_zero.mp (show inner ℂ _ x - inner ℂ (A Ω) x=0 from hy)]  -- symmetry
 refine (show x∈ LinearMap.ker B.toLinearMap from ?_)
 apply Submodule.topologicalClosure_minimal _ ?_ (isClosed_eq B.continuous continuous_const) (L x); refine Submodule.span_le.mpr ?_; rintro _ ⟨g,eω,rfl⟩
 suffices hg:inner ℂ (g Ω) (U t (A Ω))=inner ℂ (g Ω) (A Ω) by exact sub_eq_zero.mpr (show inner ℂ (U t (A Ω)) (g Ω)=_ from (inner_conj_symm ..).symm.trans ((congrArg _ hg).trans (inner_conj_symm ..))) -- tune
 let F(p q:H)(z:ℂ):= inner ℂ p (phase S z q); let cost(p q:H):= ‖p‖*‖q‖
 have Fv(p q:H):Continuous (F p q):=continuous_const.inner (phase_cont S _ _ continuous_const continuous_id)
 have Fu(p q:H):AnalyticOnNhd ℂ (F p q) inside:= fun z v=> (((innerSL ℂ p).comp (ContinuousLinearMap.apply ℂ H.space q)).analyticAt _).comp (phase_ana S z v)
 have Fe(p q:H)(z:ℂ): ‖F p q z‖≤ cost p q:= (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((phase S z).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (phase_price ..))) (norm_nonneg _))
 let F':= F (g Ω) (A Ω); let G:= F (star A Ω) (star g Ω)
 have hp:= cement (Fv (g Ω) (A Ω)) (Fv (star A Ω) (star g Ω)) (Fu _ _) (Fu _ _) ⟨max (cost (g Ω) (A Ω)) (cost (star A Ω) (star g Ω)),fun x=>⟨(Fe ..).trans (le_max_left ..),(Fe ..).trans (le_max_right ..)⟩⟩ ?_ y; swap
 · intro t; unfold F; rw [width_imaginary,width_imaginary,←trans_time,←trans_time]; rw [neg_smul]; let v:= t • basis a; let g':= V (-v) g
   have hf(x:H.Op): g' Ω= U (-v) (g Ω):= by simp only [g',parcelUp,mul_apply_eq_comp,u]
   have he: star g' Ω=U (-v) (star g Ω):=by unfold g'; rw[parcel_star]; simp only[parcelUp,mul_apply_eq_comp,u]
   rw [← he]; change inner ℂ (g Ω) (U v (A Ω))= _
   have hk: Commute (star g') A:= (VonNeumannAlgebra.mem_commutant_iff).1 q _ (star_mem (h (-v) g eω))
   rw [← ContinuousLinearMap.adjoint_inner_left (U v),show (U v).adjoint=U (-v) from Picket.trans_star .., ← hf 1, show star A=ContinuousLinearMap.adjoint A from rfl,ContinuousLinearMap.adjoint_inner_left A]; exact (ContinuousLinearMap.adjoint_inner_right g' Ω (A Ω)).symm.trans (congrArg _ (DFunLike.congr_fun hk.eq Ω))
 change F' _=F' _ at hp; unfold F' F at hp; rw [ht,trans_time]; rw [width_imaginary, show (phase S 0)=(1:H.Op) from (by rw [show (0:ℂ)=((0:ℝ):ℂ) from Complex.ofReal_zero.symm,width_real, Real.toNNReal_zero,S.eZero]; rfl)] at hp; exact hp
lemma warmth (q:Hearth S Ω) (A:H.Op)(p:A∈N.commutant) : A= (inner ℂ Ω (A Ω)) • (1:H.Op):= by
 apply sub_eq_zero.mp
 refine sees_ℓ Ω N _ ?_ ?_ L -- tune args
 · exact sub_mem p (by exact ((N.commutant).toStarSubalgebra).smul_mem (one_mem _) _)
 change A Ω - (inner ℂ Ω _) • Ω=0
 apply sub_eq_zero.mpr; have hV: cue S (A Ω)=A Ω:= by rw [cue_ground]; refine S.ground.starProjection_eq_self_iff.mpr (Boundary.offiero S _ ?_); exact fun t=> stationary S Ω N L u h _ p (t • basis a) (by intro i k; simp[k])
 exact hV.symm.trans (q _)
lemma alreadyGlobal (q:Hearth S Ω)(A:H.Op): A∈N:= by
 rw [← VonNeumannAlgebra.commutant_commutant N]; refine VonNeumannAlgebra.mem_commutant_iff.mpr (fun x h0=> ?_); have ht:= warmth S Ω N L u h q x h0; rw [ht]; exact Commute.smul_left (Commute.one_left A) _
end YM.Quartz.Bouy
