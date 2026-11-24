import YM.SU5.Celeste.Entreat
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
lemma pillar_ (F:P.Ensemble j): (∫ x, ‖P.chi j x F‖^2 ∂ (P.pillars j))= ‖F.val (P.groundZero j)‖^2:=by
  have hv(k):star (P.chi j k F)*P.chi j k F=↑(‖P.chi j k F‖^2:ℝ):=by rw [Complex.sq_norm,←Complex.mul_conj (P.chi j k F),mul_comm]; rfl
  have h:=P.recovery j (star F*F); simp_rw [map_mul,map_star,hv,integral_complex_ofReal] at h; rw [show inner ℂ φ ((star F*F).val φ)=inner ℂ (F.val φ) (F.val φ) from ContinuousLinearMap.adjoint_inner_right F.val φ (F.val φ),inner_self_eq_norm_sq_to_K] at h; apply Complex.ofReal_injective; push_cast; exact h
variable {F:Weaver}{V:Finset Cover}
def tuneK(t:Lamour.Bridge.Celeste.Voice F V): P.Test:= P.art (Ξ F) (aux_test ((t.1.narrow _).widen))
abbrev songK(t:Lamour.Bridge.Celeste.Voice F V)(Z:Tower.region j 0 (Journey.reserve P.par P.width) V)(s:ℕ): P.Vox j s:= P.positiveVox j s V (P.tuneK t) ((Tapestry.locates ..).2 ((t.1.narrow _).widen)) Z -- reserve reducible
lemma traction_load (t:Lamour.Bridge.Celeste.Voice F V)(k:ℕ): P.tuneK (t.tract j (Heat.gaugeShift Q k))=P.halfShift j k (P.tuneK t):=rfl
lemma half_here(s k:ℕ)(t:Lamour.Bridge.Celeste.Voice F V)(x:P.Spectrum0 j): P.singleState j s x (P.tuneK t)=P.singleState j s x (P.tuneK (t.tract j (Heat.gaugeShift (Q) k))):=by rw [P.traction_load j t k,P.single_state,P.single_state,P.halfReads]
lemma credit_delivers (t:Lamour.Bridge.Celeste.Voice F V)(s k:ℕ)(u:Tower.region j 0 ℓ (onFlight (Q) V j k)): (∫ x, ‖P.singleState j s x (P.tuneK t)‖^2 ∂ (P.pillars j)) ≤ ‖P.E s (household (P.calibration) (father P.par.block j F k))‖:= by
  let z:= P.songK j (t.tract j (Heat.gaugeShift Q k)) u s; simp_rw [P.half_here j s k t] -- recursion simp !
  simp_rw [P.single_state,P.pillar_]; rw [at_label];
  let E:=P.piece j s z; change ‖(P.compressed j s (P.voxTest j s z)) φ‖^2≤ ‖P.E s (mirror W j 0 z.val * z.val)‖
  rw [←P.seed_pairing,inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _),P.seed]; exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_orthogonalProjectionOnto_apply_le ..) 2
section
variable {ι:Type}[Fintype ι]{z e B:ℝ}
  (X:Ladle 4 P.par.block (reserve P.par P.width) z ι)
-- budget after choosing history. require upper on μ². accept all enough voters in precisely this topology.
lemma anyPath (z : P.Spectrum0 j)(a : Axis)(s:ℕ)(f:P.Test): P.singleState j s z f=P.singleState a s (P.otherSpectrum j a z) f:= (P.single_agrees ..).symm -- dot shadow
lemma rentGlue {z:Type} [MeasurableSpace z][TopologicalSpace z][BorelSpace z] [CompactSpace z]{μ':Measure z}[IsProbabilityMeasure μ'] (F:ι→ z→ℝ) (C:z→Prop)(h:∀ᵐ x∂μ',C x)(x:0<e)(p:∀ i, Continuous (F i))(h0:∀ i x,0≤F i x)(h':∀ i,(∫ x,F i x ∂μ')≤B)(b:(Fintype.card ι:ℝ)*B < e^2): ∃ x:z,C x∧∀ i,F i x<e^2:=by
 let D(x:z) := ∑ i,F i x; have hm(i):Integrable (F i) μ':= (p i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have hu:Integrable D μ':= integrable_finsetSum _ (fun i _=> hm i)
 have hp: (∫ x,D x ∂μ')<e^2:= by unfold D; rw [integral_finsetSum _ (fun i _=>hm i)]; apply lt_of_le_of_lt (sum_le_sum (fun i _=>h' i)) _; rw [sum_const,nsmul_eq_mul,card_univ]; exact b
 obtain ⟨x,p,q⟩:∃ x:z,C x ∧ D x<e^2:=by
    by_contra! E; have he: (∫ _x:z, (e^2:ℝ) ∂μ')≤ (∫ x,D x ∂μ'):= integral_mono_ae (integrable_const _) hu (h.mono fun x p=> E x p); rw [integral_const,probReal_univ,one_smul] at he; exact not_le.mpr hp he
 exact ⟨x,p,fun i=>lt_of_le_of_lt (show F i x ≤ D x from single_le_sum (fun i _=> h0 i x) (mem_univ i)) q⟩
lemma seasonPick {k:ℕ}(v:Papal.Lecture P.run P.large X k B) (e:ℝ)(f:0<e)(b:(Fintype.card ι:ℝ)*B < e^2): ∀ᶠ s in atTop,∀ i:ℕ,i=s →(∀ d:ι, ‖P.E s (P.tuneK (X.price d)).val‖≤ B) ∧
   ∃ x:P.Spectrum0 3, P.Sanctuary R 3 x ∧ ∀ (d:ι) (j:Axis), ‖P.singleState j s (P.otherSpectrum 3 j x) (P.tuneK (X.price d))‖< e:=by
 filter_upwards [v.price P.law] with s h;
 let S:=P.Spectrum0 3; let t:=P.pillars 3; let G (i:ι)(x:S):= ‖P.singleState 3 s x (P.tuneK (X.price i))‖^2
 have h' (i:ι): (∫ x,G i x ∂(P.pillars 3))≤ B:= (P.credit_delivers 3 (X.price i) s k (v.book _)).trans (h (i,true))
 intro _ _; refine ⟨fun i=> h (i,false),?_⟩
 obtain ⟨x,p,q⟩:= rentGlue (μ':=P.pillars 3) G (P.lodestar 3) (P.many_stars 3 R) f (fun i=>((P.chi_joint 3 (P.reading 3 s (P.tuneK (X.price i)))).norm).pow 2) (fun i x=> sq_nonneg _) h' b
 refine ⟨x,P.homes_weather R 3 (P.all_phases 3 x p), fun i j=>?_⟩; rw [P.single_agrees]; exact (pow_lt_pow_iff_left₀ (norm_nonneg _) f.le (by decide : 2 ≠ 0)).mp (q i)
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.seasonPick
