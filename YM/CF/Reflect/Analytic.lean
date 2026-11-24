import YM.CF.Reflect.Reuse
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Baire.Lemmas

/-! Finite denominator analytic controls. No claim of uniform bounds except nonvanishing. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
attribute [local instance] opCStarAlgebra
section basic
variable {n : Type*} [LinearOrder n] [Fintype n] {U : Type*} [MeasurableSpace U] [TopologicalSpace U] [SecondCountableTopology U] [BorelSpace U] (p : Wave n) (q : U→Wave n) (s : U→ℝ) {μ : Measure U} [IsFiniteMeasure μ]
def normI (p : Wave n) (q : U→Wave n) (s : U → ℝ) (μ : Measure U) [IsFiniteMeasure μ] (A : CBox U n) (x : U) : ℂ := (s x:ℝ) • inner ℂ p (acts (A x) (q x))
lemma normC (h : Continuous q) (g : Continuous s) (A:CBox U n) : Continuous (normI p q s μ A) := by
  unfold normI; exact g.smul (continuous_const.inner ((acts_cont.comp A.continuous).clm_apply h))
lemma val_rate (h : Continuous q) (g : Continuous s) (K : ℝ) (hp : ∀ x,‖q x‖≤K) (L : ℝ) (t : ∀ x, ‖s x‖≤L) (pk : 0≤K) (pv : 0 ≤ L) : ∃ f : CBox U n →L[ℝ] ℂ, ∀ A,f A=∫ x, (s x:ℂ)*inner ℂ p (acts (A x) (q x)) ∂μ := by
  let o : CBox U n→ U→ℂ := normI p q s μ
  let M := L*‖p‖*K; have he : 0≤M := by unfold M; positivity
  have hx (A:CBox U n) (x) : ‖o A x‖ ≤ M*‖A‖ := by
    calc
      _ = ‖s x‖*‖inner ℂ p (acts (A x) (q x))‖ := norm_smul ..
      _ ≤ _ := (mul_le_mul (t x) ((norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm ..) (norm_nonneg _))) (norm_nonneg _) pv)
      _ ≤ L*(‖p‖*(‖A‖*K)) := by rw [acts, Matrix.l2_opNorm_toEuclideanCLM]; gcongr; exact A.norm_coe_le_norm _; exact hp x -- tune
      _ = _ := by unfold M; ring
  have hi (A) : Integrable (o A) μ := roof (normC p q s h g A) (hx A)
  let F : CBox U n →ₗ[ℝ] ℂ :=
    { toFun := fun A=> ∫ x,o A x ∂μ
      map_add' := fun x y=> by
        rw [← integral_add (hi x) (hi y)]; apply integral_congr_ae; apply Eventually.of_forall; intro w; unfold o normI; simp only [BoundedContinuousFunction.add_apply,act_add,inner_add_right,smul_add]
      map_smul' := fun c f=> by
        rw [RingHom.id_apply,←integral_smul]; apply integral_congr_ae; apply Eventually.of_forall; intro w; dsimp only; unfold o normI; change _ • inner ℂ p (acts (c • f w) _) = _
        rw [←show (c:ℂ) • f w=c • f w by ext i j; simp [Complex.real_smul],act_smul,inner_smul_right]; simp [Complex.real_smul]; ring }
  let K' := M*μ.real Set.univ
  have hb (x:CBox U n) : ‖F x‖≤K'*‖x‖ := by
    change ‖∫ a,o x a ∂μ‖≤_
    unfold K'; rw [mul_right_comm]; exact norm_integral_le_of_norm_le_const (Eventually.of_forall (hx x))
  refine ⟨F.mkContinuous K' hb, fun A=>?_⟩
  change ∫ x,normI _ _ _ μ A x ∂μ=_; simp only [normI,Complex.real_smul,smul_eq_mul]
lemma expC (c : ℂ) : exp (c • (1:FC n))=Complex.exp c • (1:FC n) := by rw [←Algebra.algebraMap_eq_smul_one,←algebraMap_exp_comm, Algebra.algebraMap_eq_smul_one,Complex.exp_eq_exp_ℂ]
end basic
abbrev emptyF (m B : Side) : Test m B := fun _=>1
variable {m B : Side} {c : Phase.Part m B} {A D d e β : ℝ} (β) {W : Scroll m B c} (H : ScaleK A D W) (g : Budget B e d)
include H g
lemma carrier_form (l : Foot m B) : let X := TallyR m B e β; let N := CSide m B; ∃ (F:CBox X (Model N) →L[ℝ] ℂ) (P Q : CBox X (Model N)), ∀ t a:ℝ,
    rawE W e β t a l (emptyF m B)=F (exp (a • P)*exp (t • Q)) := by
  intro X N; let Z := wheel m B; let μ := Z.comap ((↑):X→ Pack m B);
  have hc := tally_meas m B e β; let I := Model N
  let F (x:X) : FC I := (-cabin W x.val) • (1:FC I); let p (x:X) := net m B β x.val
  let q (x:X) := pairWave (n:=I) (pair m B x.val.1 x.val.2)
  have hf : Continuous F := by
    exact (((cabin_cont H g).comp_continuous (continuous_subtype_val) (fun x:X=> tallyP x.property)).neg).smul (continuous_const (y:=(1:FC I)))
  have hp : Continuous p := (net_cont m B β).comp continuous_subtype_val
  have hq : Continuous q := (pairWave_cont (n:=I)).comp ((pair_cont g.1).comp_continuous (continuous_subtype_val (p:=fun x=>x∈X)) (fun i=> tallyP i.property))
  obtain ⟨u,h,hX⟩ := cabin_lim H g
  have ht (x:X) : ‖F x‖≤u := by unfold F; rw [norm_smul,norm_neg,norm_one,mul_one]; exact hX _ (tallyP x.property)
  obtain ⟨w,V,K⟩ := roofC (net_cont m B β)
  obtain ⟨s,T,L⟩ := circular (pairWave_cont (n:=I)) (isCompact_closedBall (0:Op I) 1)
  have hv (x:X) : ‖q x‖≤ s := by
    have hm := tallyP (show x.val∈TallyR m B e β from x.property)
    apply L; apply Metric.mem_closedBall.mpr; rw [dist_zero_right]; exact (CStarRing.norm_of_mem_unitary (kappa c g.1 hm.1 hm.2).1).le
  obtain ⟨j,H⟩ := val_rate (linearB N) q p (μ:=μ) hq hp s hv w (fun i=>K i.val) T V
  let P : CBox X I := BoundedContinuousFunction.ofNormedAddCommGroup F hf u ht
  let Q : CBox X I := voiced ((↑):X→ Pack m B) continuous_subtype_val (fun x: Pack m B=>dg (n:=I) (wiel m B l x.1)) ((dg_cont (n:=I)).comp ((wiel_cont l).comp continuous_fst))
  refine ⟨j,P,Q,?_⟩; intro t a
  rw [rawE,H]; unfold ratioR; rw [integral_indicator hc,← integral_subtype_comap hc];
  apply integral_congr_ae; apply Eventually.of_forall; intro x
  let K := cabin W x.val; let L := wiel m B l x.val.1; let R : Op I := grow L t
  have he : exp (t • Q) x=quant (n:=I) R := by rw [eval_exp]; exact (ferment (n:=I) (show IsSelfAdjoint L from self_wiel ..) t).symm
  have ht : exp (a • P) x=Complex.exp (-(a:ℂ)*K) • (1:FC I) := by
    rw [eval_exp]; change exp (a • ((-K) • (1:FC I)))=_
    rw [←smul_assoc,show a • (-K)= -(a:ℂ)*K by simp [Complex.real_smul],expC]
  unfold amplitude; dsimp only; rw [BoundedContinuousFunction.mul_apply,he,ht]; rw [Algebra.smul_mul_assoc, one_mul,act_smul,inner_smul_right, mul_assoc]
lemma analytic_f (l : Foot m B) : (∀ t, AnalyticOnNhd ℝ (fun a=> rawE W e β t a l (emptyF m B)) Set.univ) ∧ ∀ a, AnalyticOnNhd ℝ (fun t=>rawE W e β t a l (emptyF m B)) Set.univ := by
  obtain ⟨F,P,Q,hT⟩ := carrier_form β H g l
  simp_rw [hT]
  constructor <;> intro t x _
  · apply (F.analyticAt _).comp; apply AnalyticAt.mul _ analyticAt_const; exact (exp_analytic _).comp ((analyticAt_id (𝕜:=ℝ)).smul analyticAt_const) -- tune
  apply (F.analyticAt _).comp; apply AnalyticAt.mul analyticAt_const; exact (exp_analytic _).comp ((analyticAt_id (𝕜:=ℝ)).smul analyticAt_const)
end YM.CF.RP
