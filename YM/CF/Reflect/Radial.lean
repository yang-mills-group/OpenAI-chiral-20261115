import YM.CF.Reflect.Pad

/-! Finite transfer integrand with twist-corrected allocated action. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {A D d e β : ℝ} {W : Scroll m B c}
abbrev Glass (m B : Side) := FC (Xmind m B)
abbrev Test (m B : Side) := Pack m B→Glass m B
noncomputable def amplitude {c : Phase.Part m B} (W : Scroll m B c) (l : Foot m B) (β t a : ℝ) (f : Test m B) (x : Pack m B) :=
    ((net m B β x):ℂ)*Complex.exp (-(a:ℂ)*cabin W x)*inner ℂ (linearB (CSide m B)) (acts (f x*quant (n:=Xmind m B) (grow (wiel m B l x.1) t)) (pairWave (n:=Xmind m B) (pair m B x.1 x.2)))
def ratioR {c : Phase.Part m B} (W : Scroll m B c) (e β τ k : ℝ) (l : Foot m B) (f : Test m B) := (TallyR m B e β).indicator (amplitude W l β τ k f)
def rawE {c : Phase.Part m B} (W : Scroll m B c) (e β τ k : ℝ) (l : Foot m B) (f : Test m B) := ∫ x,ratioR W e β τ k l f x ∂wheel m B
section rays
variable (g : ScaleK A D W) (k : Budget B e d)
include g k
lemma program_lim (S : FaceTerm m B) {x : Pack m B} (f : x∈payer m B e) : ‖programK W S x‖ ≤ (tariffR m)⁻¹*W.mint S.2 := by
  unfold programK twistF; rw [norm_smul, flips_norm]; have he := (inv_pos.mpr (paid_t m)).le; rw [Real.norm_of_nonneg he]; exact mul_le_mul_of_nonneg_left ((gainS g k _).norm _ (dominated _ _ f)) he
lemma port_lim (i) : ∃ c≥(0:ℝ), ∀ x∈payer m B e, ‖inPort W i x‖≤c := by
  let f (S:FaceTerm m B) := ‖bonus (faceT S) i‖*((tariffR m)⁻¹*W.mint S.2)
  have he S : 0≤f S := mul_nonneg (norm_nonneg _) (mul_nonneg (inv_pos.mpr (paid_t m)).le (gainS g k _).pos)
  refine ⟨∑ S,f S,sum_nonneg (fun S _=>he S),fun x h=>?_⟩; unfold inPort; apply (norm_sum_le ..).trans; exact sum_le_sum fun S _=> by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (program_lim g k S h) (norm_nonneg _)
lemma cabin_lim : ∃ c≥(0:ℝ), ∀ x∈payer m B e, ‖cabin W x‖≤c := by
  obtain ⟨v,p,L⟩ := port_lim g k 0; exact ⟨v+v,by positivity,fun x h=>by rw [portPair 0]; apply (norm_add_le ..).trans; rw [norm_star]; exact add_le_add (L x h) (L _ (dominated _ _ h))⟩
lemma innateC (i : Axis) : ContinuousOn (inPort W i) (payer m B e) := continuousOn_finsetSum _ fun j _=> (continuousOn_const (c:=bonus (faceT j) i)).smul (programC g k j)
omit g k in
lemma actualC (c : Phase.Part m B) (t : ℝ) : Continuous (fun v:Pack m B=>quant (n:=Xmind m B) (grow (wiel m B c v.1) t)) := by
  letI : NormedAlgebra ℚ (Op (Xmind m B)) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact quant_cont.comp (NormedSpace.exp_continuous.comp ((continuous_const (y:=t)).smul ((wiel_cont _).comp continuous_fst))) -- tune
omit g k in
lemma circular {U T : Type*} [TopologicalSpace U] [NormedAddCommGroup T] {s : Set U} {f:U→T} (h : Continuous f) (p : IsCompact s) : ∃ C:ℝ, 0≤C ∧ ∀ i∈s,‖f i‖≤C := by
  obtain ⟨k,hk⟩ := (p.image h.norm).bddAbove; exact ⟨max k 0,le_max_right ..,fun i w=> (hk ⟨_,w,rfl⟩).trans (le_max_left ..)⟩
omit g k in
lemma roofC {U T : Type*} [TopologicalSpace U] [CompactSpace U] [NormedAddCommGroup T] {f:U→T} (h : Continuous f) : ∃ C:ℝ, 0≤ C∧∀ i,‖f i‖≤C := by obtain ⟨c,p,h⟩ := circular h isCompact_univ; exact ⟨c,p,fun i=>h i (Set.mem_univ i)⟩
lemma amplitude_size {f : Test m B} (h : Continuous f) (β t a : ℝ) (l:Foot m B) :
    ∃ c:ℝ,0≤c∧ ContinuousOn (amplitude W l β t a f) (payer m B e) ∧ ∀ x∈payer m B e, ‖amplitude W l β t a f x‖≤c := by
  let p := payer m B e; let N := CSide m B; let M := Xmind m B; let s:= linearB N
  let F := fun x:Pack m B => f x*quant (n:=M) (grow (wiel m B l x.1) t)
  let P := fun x: Pack m B=>pairWave (n:=M) (pair m B x.1 x.2)
  let X := cabin W; let L x : ℂ := ↑(net m B β x)
  let E (Y : ℂ) := Complex.exp (-(a:ℂ)*Y)
  have he : Continuous L := Complex.continuous_ofReal.comp (net_cont m B β)
  have hf : Continuous F := h.mul (actualC ..)
  have hp : ContinuousOn P p := (pairWave_cont (n:=M)).comp_continuousOn (pair_cont k.1)
  have ht : ContinuousOn X p := cabin_cont g k
  have hx : Continuous E := Complex.continuous_exp.comp (continuous_const.mul continuous_id)
  obtain ⟨v,pV,hV⟩ := cabin_lim g k
  obtain ⟨c,pA,hA⟩ := roofC hf; obtain ⟨m₁,p₁,h₁⟩ := roofC he
  obtain ⟨w,p₂,h₂⟩ := circular hx (isCompact_closedBall 0 v)
  obtain ⟨v₁,p₃,h₃⟩ := circular (pairWave_cont (n:=M)) (isCompact_closedBall (0:Op M) 1)
  refine ⟨(m₁*w)*(‖s‖ * (c*v₁)),by positivity, ?_,?_⟩
  · change ContinuousOn (fun x=>L x*E (X x)*inner ℂ s (acts (F x) (P x))) _
    exact (he.continuousOn.mul (hx.comp_continuousOn ht)).mul (continuousOn_const.inner ((acts_cont.comp hf).continuousOn.clm_apply hp))
  intro x l; let Y := pair m B x.1 x.2; have hz : ‖Y‖=1 := CStarRing.norm_of_mem_unitary (kappa (0:Phase.Part m B) k.1 l.1 l.2).1
  have hL : ‖P x‖≤v₁ := h₃ Y (by simpa using hz.le)
  have hy : ‖acts (F x) (P x)‖ ≤ c*v₁ := (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul (show ‖acts (F x)‖≤c by rw [acts, Matrix.l2_opNorm_toEuclideanCLM]; exact hA _) hL (norm_nonneg _) pA)
  change ‖L x*E (X x)*inner ℂ s (acts (F x) (P x))‖≤ _; rw [norm_mul,norm_mul];
  exact mul_le_mul (mul_le_mul (h₁ _) (h₂ (X x) (by simpa using hV _ l)) (norm_nonneg _) p₁) ((norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))) (norm_nonneg _) (mul_nonneg p₁ p₂)
omit g k in
lemma gift_integrate {T U:Type*} [MeasurableSpace U] [TopologicalSpace U] [SecondCountableTopology U] [BorelSpace U] [NormedAddCommGroup T] [SecondCountableTopology T] {μ:Measure U} [IsFiniteMeasure μ] {S:Set U} (s:Set U) (p : s⊆S) (hs : MeasurableSet s) {c: ℝ} (k: 0≤c) {F:U→T} (h : ContinuousOn F S) (t : ∀ i∈S,‖F i‖≤c) : Integrable (s.indicator F) μ := by
  apply IntegrableOn.integrable_indicator _ hs
  refine Integrable.of_bound ((h.mono p).aestronglyMeasurable hs) c ?_; filter_upwards [ae_restrict_mem hs] with x hx; exact t _ (p hx)
lemma sojourn {f: Test m B} (h : Continuous f) (β t a : ℝ) (l:Foot m B) : Integrable (ratioR W e β t a l f) (wheel m B) := by
  obtain ⟨K,m',H,G⟩ := amplitude_size g k h β t a l
  exact gift_integrate _ (fun i g=> tallyP g) (tally_meas ..) m' H G
end rays
end YM.CF.RP
