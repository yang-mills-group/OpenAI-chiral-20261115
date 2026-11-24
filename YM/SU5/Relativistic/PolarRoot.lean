import YM.SU5.Relativistic.PureProduct

/-! # Stabilize at most a phase per footprint/scale, NO individual sequence
  for different test arguments. Handles degenerate (zero lift) branch too. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Fock Reflect Function Filter MeasureTheory NormedSpace Finset Metric Set
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

section uniform
variable {A:Type*}{Z:Type*}[NormedAddCommGroup Z]
-- no bounds away from tail assumed; tending uniformly. handy weak ≤ estimates
abbrev Jars (P:ℕ→A→Z) (Y:A→Z) : Prop := ∀ e:ℝ,0<e→∀ᶠ i in atTop,∀ x, ‖P i x - Y x‖≤ e
abbrev SeenAll (P:ℕ→A→Z): Prop :=∃ Y,Jars P Y
abbrev Latches (P:ℕ→A→Z): Prop:=∀ e:ℝ,0<e→∀ᶠ i:ℕ in atTop,∀ m≥i,∀ n≥i,∀ x, ‖P m x-P n x‖≤e
variable {P:ℕ→A→Z} {Y:A→Z}
lemma jarsMono (h:Jars P Y) {u:ℕ→ℕ}(p:Tendsto u atTop atTop):Jars (P ∘ u) Y:=fun _ z=>p.eventually (h _ z)
lemma capAll (h:Jars P Y) : Latches P:=by
 intro e p; obtain ⟨n,h⟩:= eventually_atTop.1 (h _ (half_pos p)); filter_upwards [eventually_ge_atTop n] with i s j t k g a
 exact (norm_sub_le_norm_sub_add_norm_sub _ (Y a) _).trans (by rw [norm_sub_rev (Y a)]; linarith [h _ (s.trans t) a,h _ (s.trans g) a])
lemma capPoints (h:Latches P)(a:A) : CauchySeq (fun n=> P n a):= by
 refine Metric.cauchySeq_iff.mpr fun e v=>?_
 obtain ⟨n,h⟩:= (h _ (half_pos v)).exists; exact ⟨n,fun j p k g=> by rw [dist_eq_norm]; exact (h j p k g a).trans_lt (half_lt_self v)⟩
lemma seenOfComplete [CompleteSpace Z](h:Latches P):SeenAll P:=by
 choose Y p using fun a=> cauchySeq_tendsto_of_complete (capPoints h a)
 refine ⟨Y,fun e v=> ?_⟩; filter_upwards [h _ v] with n t a; apply le_of_tendsto ((p a|>.const_sub (P n a)).norm); filter_upwards [eventually_ge_atTop n] with i hi
 exact t _ le_rfl _ hi a
lemma sights (h:Jars P Y)(a:A) : Tendsto (fun n=>P n a) atTop (𝓝 (Y a)):=by
 refine Metric.tendsto_nhds.mpr fun e v=>?_
 filter_upwards [h _ (half_pos v)] with i t; rw [dist_eq_norm]; exact (t a).trans_lt (half_lt_self v)
end uniform

variable {I A : Type*} [Fintype I] [LinearOrder I]
local notation "W" => FC I
-- R = push, Q = anti-linear mirror gives twist (norm-preserving) at sewn inputs.
variable {S T : Finset I}{R Q:ℕ→A→ FC I}
  (k:Disjoint S T)(q:∀ i a,Sector S true (Q i a))(p:∀ i a,Sector T true (R i a))(w:∀ i a,‖Q i a‖=‖R i a‖)
variable {D:A×A→FC I} (h:Jars (fun i a=> Q i a.1*R i a.2) D)(v:∃ K:ℝ,∀ a, ‖D a‖≤K)
include k q p w h v
lemma sponsor : ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop,∀ a,‖R i a‖≤C:=by
 obtain ⟨K,t⟩:=v; obtain ⟨c,a,e⟩:= leverage k true true; refine ⟨max 1 (Real.sqrt (max 1 ((1+K)/c))),lt_max_of_lt_left zero_lt_one,?_⟩; filter_upwards [h _ zero_lt_one] with i u z
 have hx:= e _ _ (q i z) (p i z); have he:= u (z,z); rw [w] at hx
 have hp:= calc
    ‖Q i z * R i z‖ ≤ ‖Q i z * R i z-D (z,z)‖ + ‖D (z,z)‖:= norm_le_norm_sub_add ..
    _ ≤ 1+K:= add_le_add he (t _)
 apply le_max_of_le_right; have hX: ‖R i z‖^2≤(1+K)/c:= (le_div_iff₀ a).mpr (by nlinarith only [hx,hp])
 let V := max 1 ((1+K)/c); have hv:0 ≤ V:=le_trans zero_le_one (le_max_left ..); nlinarith only [hX.trans (show (1+K)/c≤ V from le_max_right ..),Real.sq_sqrt hv,Real.sqrt_nonneg V]
lemma flock : ∃ u:ℕ→ℕ,StrictMono u ∧ SeenAll (R ∘ u):=by
 obtain ⟨c,a,e⟩:= leverage k true true; by_cases z:∀ i,D i=0
 · refine ⟨id, strictMono_id, 0, fun g t=>?_⟩
   filter_upwards [h (c*g^2) (by positivity)] with i u x
   have he:= u (x,x); rw [z,sub_zero] at he
   have hp:= e _ _ (q i x) (p i x); rw [w] at hp
   have hx:= hp.trans he; change ‖R i x-0‖≤ _; rw [sub_zero]
   apply le_of_pow_le_pow_left₀ (by decide : 2≠0) t.le
   exact le_of_mul_le_mul_left (by nlinarith only [hx] : c*‖R i x‖^2≤c*g^2) a
 push Not at z; obtain ⟨⟨x,y⟩,hz⟩:=z
 obtain ⟨K,Kl,KK⟩:= sponsor k q p w h v
 obtain ⟨Y,_,u,l,t⟩:= (isCompact_closedBall (0:W) K).tendsto_subseq' (x:=fun i:ℕ=> Q i x) ((show ∀ᶠ i:ℕ in atTop,Q i x∈ closedBall (0:W) K from KK.mono fun i h=>mem_closedBall.mpr (by rw [dist_zero_right,w]; exact h x)).frequently)
 have hKK:= l.tendsto_atTop.eventually KK; have hv:Tendsto (fun i=>Q (u i) x) atTop (𝓝 Y):=t -- fix
 let cD:= ‖D (x,y)‖; have hX:0<cD:= norm_pos_iff.mpr hz
 let sigma_ := cD/2/K; have hPos:0<sigma_:= by positivity
 have Hu:= jarsMono h l.tendsto_atTop
 have H : ∀ᶠ i in atTop, sigma_ ≤ ‖Q (u i) x‖ := by
    filter_upwards [Hu _ (half_pos hX),hKK] with i p h
    specialize p (x,y)
    let v:= D (x,y); let A:= Q (u i) x; let B:=R (u i) y
    have he: cD≤ cD/2 + ‖A‖*K:=by
       refine (norm_le_norm_sub_add v (A*B)).trans (add_le_add ?_ ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (h y) (norm_nonneg _))))
       rw [norm_sub_rev]; exact p
    exact (div_le_iff₀ Kl).mpr (by linarith only [he])
 refine ⟨u,l, seenOfComplete ?_⟩
 intro g t; let d:=g*c*sigma_/4; have hd:0<d:=by positivity
 obtain ⟨m,ht⟩:= eventually_atTop.1 ((((hv|> Metric.tendsto_nhds.mp) _ (show 0<d/K from div_pos hd Kl)).and H).and hKK)
 filter_upwards [eventually_ge_atTop m, capAll Hu _ hd] with n r z i ti j tj a'
 let A:=Q (u i) x; let B:=Q (u j) x; let F:= R (u i) a'; let L:=R (u j) a'
 have he:= e A (F-L) (q (u i) x) (sector_sub (p ..) (p ..)); have hi:= ht i (r.trans ti); have hj:=ht j (r.trans tj); have hx: c*sigma_*‖F-L‖≤ ‖A*(F-L)‖:=le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi.1.2 a.le) (norm_nonneg _)) he
 have hy: ‖A*(F-L)‖≤d+2*d:= by
    rw [mul_sub]; apply (norm_sub_le_norm_sub_add_norm_sub (A*F) (B*L) (A*L)).trans (add_le_add (z i ti j tj (x,a')) ?_)
    rw [← _root_.sub_mul]; refine (norm_mul_le ..).trans ?_; apply le_trans (mul_le_mul_of_nonneg_left (hj.2 a') (norm_nonneg _)); rw [←dist_eq_norm]
    exact (mul_le_mul_of_nonneg_right (dist_triangle B Y A) Kl.le).trans (by have hv:dist B Y<d/K:=hj.1.1; have hx:dist A Y<d/K:=hi.1.1; rw [dist_comm Y]; nlinarith [(lt_div_iff₀ Kl).1 hv,(lt_div_iff₀ Kl).1 hx])
 change ‖F-L‖≤_
 exact le_of_mul_le_mul_left ((hx.trans hy).trans (show d+2*d ≤ (c*sigma_)*g by unfold d at hd ⊢; nlinarith only [hd])) (show 0<c*sigma_ from by positivity)
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.flock
