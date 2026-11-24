import YM.SU5.Selected.Vanguard
import YM.Ground.Spectrum
/-!
# Norm form of barycenter convergence theorem used to port selection from `Cluster`
for the joint ground projection. Joint mean of `verdict` for each k then nested projections.
General Hilbert-Blueprint over B's character spectrum; phase parameter Z can be transported
consistently. One and the same index/measure/characters. Not smoothing over boundaries nor
assuming concentration at Ω. Ports also RV projection variance lemma.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selection
namespace Localization.Canton
open Companies Pruner
open Function Filter Set Analysis OS.Ground MeasureTheory
open scoped Matrix MatrixOrder Topology InnerProductSpace ComplexOrder Classical

variable {X Y : Hilbert} {P : Submodule ℂ (X→L[ℂ] Y)} {B : StarSubalgebra ℂ X.Op}
variable (Ω : X) (Z : Panes ↑B) (hZ : Z.Shines X B.subtype Ω)
variable (L : ∀ i, Blueprint X Y P B (Z.character i).toAlgHom.toLinearMap)
    (U : ∀ i, (L i).Room)
local notation "Γ" i:max => L i
local notation "ℋ" i:max => (U i).H
local notation "η" i:max => (Γ i).bloom (U i)

/-- infrastructure estimate for arbitrary operator legs, not presupposing B is the whole C*-closure
outside the ground. -/
def weight (p q : P) (s : ∀ x y : P,x.val.adjoint.comp y.val∈ B) : B := ⟨_,s p q⟩
include hZ
lemma initial (p : P) : Continuous (fun i => ‖(η i) p‖^2) ∧ (∫ i, ‖(η i) p‖^2 ∂Z.μ)=‖p.val Ω‖^2 := by
  haveI := hZ.normalized
  haveI : Nonempty Z.X := nonempty_of_isProbabilityMeasure Z.μ
  let b := weight p p ((L (Classical.arbitrary _)).owns)
  -- infer Nonempty? need supporting measure
  have hw i : ‖(η i) p‖^2 = (Z.character i b).re :=
    ((Γ i).norm_bloom_sq (U i) p).trans (congrArg (fun w : B=>(Z.character i w).re) (Subtype.ext rfl))
  simp_rw [hw]
  refine ⟨Complex.continuous_re.comp (hZ.weak _),?_⟩
  change (∫i:Z.X, RCLike.re (Z.character i b) ∂Z.μ)=_
  rw [integral_re ((hZ.weak _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), hZ.ground]
  change (inner ℂ Ω (p.val.adjoint (p.val Ω))).re=_; rw [ContinuousLinearMap.adjoint_inner_right, ← inner_self_eq_norm_sq (𝕜:=ℂ)]; rfl

variable (F : ℕ → preserves P) (h : ∀ i, ‖(F i).val‖ ≤ 1)
abbrev main (n : ℕ) := (F n).val
abbrev route (i : Z.X) (n : ℕ) := (L i).plays (U i) (F n)
omit hZ
include h
local notation "R" i:max => route Z L U F i
local notation "M" => main F
lemma route_size (i : Z.X) (n : ℕ) : ‖(R i) n‖ ≤ 1:= ((L i).implement_size (U i) (F n)).trans (h _)
-- pointwise approximation. apply initial to `applyM`.
local notation "Q" n:max m:max => mix (blend F n) m
local notation "F_j" i:max n:max m:max => mix (blend (R i) n) m
local notation "F_0" n:max m:max => mix (blend M n) m
include hZ
omit h in
lemma cost (n m : ℕ) (p : P) : Continuous (fun i => ‖(F_j i n m) ((η i) p)‖^2) ∧
    (∫ i, ‖(F_j i n m) ((η i) p)‖^2 ∂Z.μ)=‖(F_0 n m) (p.val Ω)‖^2 := by
  have hp i : F_j i n m = (L i).plays (U i) (Q n m) :=
    Eq.symm ((mix_map ((L i).plays (U i)).toAlgHom (blend F n) m).trans (congrArg (fun x=>mix x m) (blend_map ((L i).plays (U i)).toAlgHom _ _)))
  have hF : F_0 n m=(Q n m).val := Eq.symm ((mix_map (preserves P).subtype.toAlgHom (blend F n) m).trans (congrArg (fun x=> mix x m) (blend_map (preserves P).subtype.toAlgHom _ _)))
  have hx i : (F_j i n m) ((η i) p)= (η i) (applyM P (Q n m) p) := (congrArg (fun x:(ℋ i).Op=> x _) (hp i)).trans ((L i).implement_law (U i) _ p)
  simp only [hx,hF]; exact initial Ω Z hZ L U (applyM P (Q n m) p)

-- DCT package induction for both limits
omit h hZ
private lemma commute_limit {K : Type} [MeasurableSpace K] {μ : Measure K} (f : ℕ→K→ℝ)
    (p : K→ℝ) (e : K→ℝ) (hp : ∀ i, Tendsto (fun n=> f n i) atTop (𝓝 (p i)))
    (u : ∀ n, Integrable (f n) μ) (v : Integrable e μ) (g : ∀ n i, ‖f n i‖≤e i)
    (x : ℝ) (w : Tendsto (fun n => ∫ i, f n i ∂μ) atTop (𝓝 x)) : Integrable p μ ∧ (∫i,p i ∂μ)=x :=
  have hs : ∀ i,∀ᵐ k ∂μ, ‖f i k‖≤e k := fun i => Eventually.of_forall (g i)
  ⟨⟨aestronglyMeasurable_of_tendsto_ae _ (fun i=>(u i).1) (Eventually.of_forall hp),
    hasFiniteIntegral_of_dominated_convergence v.2 hs (Eventually.of_forall hp)⟩,
   tendsto_nhds_unique (tendsto_integral_of_dominated_convergence e (fun i=>(u i).1) v hs (Eventually.of_forall hp)) w⟩
local notation "Tₙ" i:max n:max => fixedAt (ℋ i) (R i) n
local notation "σ" i:max => stationary (ℋ i) (R i)
local notation "T₀" n:max => fixedAt Y M n
include F h hZ L U
lemma approaching (p : P) (n : ℕ) : Integrable (fun i=> ‖(Tₙ i n).starProjection ((η i) p)‖^2) Z.μ ∧
    (∫ i, ‖(Tₙ i n).starProjection ((η i) p)‖^2 ∂Z.μ)=‖(T₀ n).starProjection (p.val Ω)‖^2 := by
  haveI := hZ.normalized
  refine commute_limit (fun m i => ‖(F_j i n m) ((η i) p)‖^2) _ (fun i=>‖(η i) p‖^2)
    (fun i=> (mean_summit _ _ (route_size Z L U F h i) n _).norm.pow _) (fun m=>(cost Ω Z hZ L U F n m p).1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ((initial Ω Z hZ L U p).1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ?_ _ ?_
  · intro m i; rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (mean_cost (ℋ i) _ (blend_small _ _ (route_size Z L U F h i) _) _ _) _
  exact ((mean_summit Y M h n _).norm.pow _).congr (fun i=> (cost Ω Z hZ L U F n i p).2.symm)

lemma balance (p : P) : Integrable (fun i => ‖(σ i).starProjection ((η i) p)‖^2) Z.μ ∧
    (∫ i, ‖(σ i).starProjection ((η i) p)‖^2 ∂Z.μ)=‖(stationary Y M).starProjection (p.val Ω)‖^2 := by
  haveI := hZ.normalized
  refine commute_limit (fun n i=> ‖(Tₙ i n).starProjection ((η i) p)‖^2) _ (fun i=>‖(η i) p‖^2)
    (fun i=> (finish _ _ (route_size Z L U F h i) _).norm.pow _) (fun m=>(approaching Ω Z hZ L U F h p m).1) ((initial Ω Z hZ L U p).1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ?_ _ ?_
  · intro m i; rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) ((Tₙ i m).norm_starProjection_apply_le _) _
  exact ((finish Y M h _).norm.pow _).congr (fun n=> (approaching Ω Z hZ L U F h p n).2.symm)
end Localization.Canton
end YM.CF.Buffered.Afterglow.Tower.Selection
