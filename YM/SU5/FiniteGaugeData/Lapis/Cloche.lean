import YM.SU5.FiniteGaugeData.Lapis.Eclipse
/-! # Punch: budgeted Wick-Gaussian moments in BP16 honor coordinates at all finite preparations.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal
namespace Punch
open Drachma Next.SectorChange.Gaussian Galope.Rally
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J](A: sp I)(B:sp J)(h:A.PosDef)(u:B.PosDef){r:ℝ}
-- coordinatize draw. use Euclidean for phase/spectral frame. Note `Fintype.card` appears even in daylight chart dollar.
abbrev Vault (I:Type):= EuclideanSpace ℝ I
lemma root_unit (A:sp I)(h:A.PosDef): IsUnit (CFC.sqrt (A⁻¹)).det:=by
 apply IsUnit.mk0 _; intro p; have he:= congrArg (det) (CFC.sqrt_mul_sqrt_self A⁻¹ h.inv.posSemidef.nonneg); rw [det_mul,p,zero_mul] at he; exact (h.inv.det_pos.ne) he -- tune
def bridgeB (A:sp I)(h:A.PosDef): Vault I ≃ₗ[ℝ] coin I:= (WithLp.linearEquiv 2 ℝ (coin I)).trans (Matrix.toLinearEquiv' (CFC.sqrt (A⁻¹)) ((Matrix.isUnit_iff_isUnit_det _).mpr (root_unit A h)).invertible) -- tune
local notation "σ" i:max => stdGaussian (Vault i)
local notation "Square" => CFC.sqrt
local notation "Y" => coin I
lemma board (x:Vault I): bridgeB A h x = CFC.sqrt (A⁻¹) *ᵥ x.ofLp := by rfl -- tune
lemma chalk(x:Vault I) : dotProduct (bridgeB A h x) (A*ᵥ (bridgeB A h x))= ‖x‖^2:=by
 let M:= CFC.sqrt (A⁻¹); let v:coin I:=x.ofLp
 let W:= dotProduct v v; have he: W=‖x‖^2:=by rw [EuclideanSpace.real_norm_sq_eq]; unfold W dotProduct; simp_rw [sq]; rfl -- tune
 rw [← he]; unfold W; rw [board]; rw [mulVec_mulVec, show A*CFC.sqrt A⁻¹ = M⁻¹ from ?_]; swap
 · suffices he:A*M=M⁻¹ from he
   have hh:M*M=A⁻¹:= CFC.sqrt_mul_sqrt_self _ h.inv.posSemidef.nonneg
   calc
       A*M = A*M*(M*M⁻¹) :=by rw [M.mul_nonsing_inv (root_unit A h),mul_one]
       _ = M⁻¹ := by rw [← Matrix.mul_assoc, Matrix.mul_assoc A M,hh,A.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit),one_mul] -- tune assoc
 have hs:Mᵀ=M:= Matrix.isHermitian_iff_isSymm.mp (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A⁻¹)).isHermitian
 change dotProduct (M *ᵥ v) (M⁻¹ *ᵥ v)=_
 rw [dotProduct_mulVec,←vecMul_transpose M,vecMul_vecMul,hs,M.mul_nonsing_inv (root_unit A h),vecMul_one]
lemma grant : MeasurePreserving (bridgeB A h) (stdGaussian (Vault I)) (cloud (A⁻¹)):=by
 let V:= bridgeB A h; let H:= V.toContinuousLinearEquiv; apply MeasurePreserving.mk H.continuous.measurable
 rw [cloud, multivariateGaussian]; simp only [zero_add]; rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl -- tune
-- $holdK$-normalized directional integral. at cost P vs tilt proof.
lemma stage (f:Y→ℝ) (t:Y)(q:0<r)(e: let H:= bridgeB (r•A) (h.smul q); Integrable (f∘H) (stdGaussian (Vault I))) : let H:= bridgeB (r•A) (h.smul q); Integrable (fun x:Y=> f (x+t)* doll A (x+t) r) ∧ (∫ x:Y,f (x+t)* doll A (x+t) r)= holdK A r *(∫ x,f (H x) ∂ stdGaussian (Vault I)) :=by
 intro H; let L:=H.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv; let g(x:Y):= f x * doll A x r; set S:=r•A; have hS:S.PosDef:= h.smul q; set K:= cloud S⁻¹; have hv:MeasurePreserving L (σ I) K:= grant S hS; have he:=under_cloud hS.inv g; let h₀(x:Y):= Real.exp ((force S⁻¹ x)/2); have hh:(fun x=>h₀ x • g x)=f:=by
    funext x; have hU:force S⁻¹ x=r*dotProduct x (A*ᵥ x):=by unfold force; rw [nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)]; unfold S; rw [smul_mulVec,dotProduct_smul]; rfl
    unfold h₀ g doll; rw [hU,smul_eq_mul,mul_left_comm,← Real.exp_add,show r*dotProduct _ _/2+ _=0 from ?_,Real.exp_zero,mul_one] -- placeholders
    ring
 have hy : Integrable f K:=(hv.integrable_comp_emb L.measurableEmbedding).1 e -- wrong ∘
 change (Integrable g ↔ Integrable (fun x=> h₀ x • g x) K) ∧ (_:ℝ)=holdK A r* (∫ x,h₀ x • g x∂K) at he; rw [hh] at he
 let hμ : MeasurePreserving (MeasurableEquiv.addRight t) volume (volume:Measure Y) := measurePreserving_add_right volume t; exact ⟨hμ.integrable_comp_of_integrable (he.1.mpr hy),(hμ.integral_comp' g).trans (he.2.trans (congrArg (_ * ·) (hv.integral_comp' f).symm))⟩
-- active space inclusion selecting unscaled bill $A$. Useful embedding with $B=r·active$.
def warp (f: coin J →ₗ[ℝ] Y):= (bridgeB A h).symm.toLinearMap.comp (f.comp (bridgeB B u).toLinearMap) -- simplify
variable (g:coin J→ₗ[ℝ] coin I)(p:∀ y:coin J,dotProduct (g y) (A*ᵥ g y)=dotProduct y (B*ᵥ y))
def venue : Vault J →ₗᵢ[ℝ] Vault I where
 toLinearMap:= warp A B h u g
 norm_map' x:= by
    let V:= bridgeB A h; let v:=g (bridgeB B u x); refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_; change ‖V.symm v‖^2=_; exact ((chalk A h (V.symm v)).symm.trans ((congrArg (fun w:coin I=> dotProduct w (A*ᵥ w)) (V.apply_symm_apply _)).trans ((p _).trans (chalk B u _))))
lemma valued(x:Vault J): bridgeB A h (venue A B h u g p x)=g (bridgeB B u x):= (bridgeB A h).apply_symm_apply _
end Punch
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Punch.valued
#print axioms YM.SU5.FiniteGaugeData.Lapis.Punch.stage
