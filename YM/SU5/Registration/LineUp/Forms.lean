import YM.SU5.Registration.Ink.WavePort
import YM.Fields.Star
import YM.Work.A13
import YM.Work.A16
import YM.Extraction.Ties
/-!
 # Criteria from proper rotations on the verified M10 charges

 No invariance claims in this file. Prices on the stars & actual SharpMark stencil
 moments specified later. Uses only the proper rotations (orientation as YM.Mink).
 Does not yet work with a COST. General epaulet module; **finite fares**
 condition on moving the labels instead of trying to turn epaulets topological.
 Using YM pinned `Ortho Field, A13 A16 C07-`, etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Boundary Mink Analysis Function Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
/-- continuity purchase in a pocket. Bill is algebraic module, no continuum-topology claim. -/
def GearContinuity {X : Type*} [TopologicalSpace X] (f:X→V) (x:X) : Prop := ∃ (k:ℕ) (g:Fin k→V) (c:Fin k→ X→ℂ), (∀ j, ContinuousAt (c j) x) ∧ (∀ᶠ u in 𝓝 x, f u=∑ i, c i u • g i)
/-- cost of differentiating labels, enough to carry a boost and use it to turn Wightman tables at cap. -/
def GearDeriv (f:ℝ→V) (e:V) : Prop := ∃ (k:ℕ) (g:Fin k→V) (c:Fin k→ℝ→ℂ) (c':Fin k→ℂ),
  (∀ i, HasDerivAt (c i) (c' i) 0) ∧ (∀ᶠ t in 𝓝 0,f t=∑ i,c i t • g i) ∧ e=∑ i, c' i • g i
lemma GearDeriv.gear {f:ℝ→V}{e} (h:GearDeriv f e) : GearContinuity f 0:= by
 obtain ⟨k,g,c,c',p,h,rfl⟩:=h; exact ⟨k,g,c,fun i=>(p i).continuousAt,h⟩
lemma GearDeriv.back {f:ℝ→V}{e} (h:GearDeriv f e) : GearDeriv (fun t=> f (-t)) (-e):=by
 obtain ⟨k,g,c,c',p,h,rfl⟩:=h; refine ⟨k,g,fun i t=> c i (-t), fun i=> -c' i,fun i=>?_,?_ ,?_⟩
 · simpa [Function.comp_def] using! (p i).scomp_of_eq (0:ℝ) (hasDerivAt_id' (0 : ℝ)).neg (by simp)
 · exact (show Tendsto (fun t:ℝ=>-t) (𝓝 0) (𝓝 0) by simpa using continuous_neg.tendsto (0:ℝ)).eventually h
 simp [Finset.sum_neg_distrib]
structure Courts (V:Type*) [AddCommGroup V][Module ℂ V] where
  eu (s : Ortho) : V →ₗ[ℂ] V -- ask only on proper. convenience unused other.
  eu1 (i:V): eu 1 i=i
  euMul (s t :Ortho)(hs:Lorentz.properTurn s)(ht:Lorentz.properTurn t)(i:V): eu (s*t) i=eu s (eu t i)
  planeDuty (a:SpaceAxis): V →ₗ[ℂ] V
  euD (a:SpaceAxis)(v:V): GearDeriv (fun t=> eu (Ortho.oneParameter (Ortho.plane timeAxis a.castSucc) t) v) (planeDuty a v)
  mi (s:Lorentz): V→ₗ[ℂ] V
  mi1 (i:V): mi 1 i=i
  miMul (s t:Lorentz)(i:V) : mi (s*t) i= mi s (mi t i)
  miD (a:SpaceAxis)(v:V) : GearDeriv (fun t=> mi ((Ray.fromAxis a).boost t) v) ((-Complex.I) • planeDuty a v)
  miC (v:V)(s:Lorentz) : GearContinuity (fun s=> mi s v) s
  both (r:Ortho) (hr:Lorentz.spatialTurn r) : mi (.room r hr)= eu r

namespace Courts
open Ortho
local notation "J" Ω:max r:max=> oneParameter Ω r
abbrev pdet (r : Ortho) := LinearMap.det r.motion.toLinearEquiv.toLinearMap
lemma pdet_mul (r s : Ortho) : pdet (r*s) = pdet r * pdet s:=by
 have h:(motion (r*s)).toLinearEquiv.toLinearMap= (motion r).toLinearEquiv.toLinearMap.comp (motion s).toLinearEquiv.toLinearMap:= LinearMap.ext fun i=> Ortho.move_mul r s i
 unfold pdet; rw [h, LinearMap.det_comp]
lemma proper_one : Lorentz.properTurn 1:=by
 unfold Lorentz.properTurn; rw [show (motion 1).toLinearEquiv.toLinearMap=(LinearMap.id:E4→ₗ[ℝ]E4) from LinearMap.ext fun i=> Ortho.move_one i, LinearMap.det_id]
lemma proper_mul {r s: Ortho}(p:Lorentz.properTurn r)(q:Lorentz.properTurn s): Lorentz.properTurn (r*s):=by
 change pdet (r*s)=_; rw [pdet_mul, show pdet r=1 from p,show pdet s=1 from q,one_mul]
lemma proper_inv {r: Ortho}(p:Lorentz.properTurn r): Lorentz.properTurn r⁻¹:= by
 have k:=pdet_mul r⁻¹ r; rw [inv_mul_cancel,show pdet 1=1 from proper_one, show pdet r=1 from p,mul_one] at k; exact k.symm
lemma pdet_range (r : Ortho) : (pdet r)^2=1:=by
 -- a = b, b= map … ; transfer
 let b := EuclideanSpace.basisFun Axis ℝ; let c:= b.map r.motion; have hd:(b.toBasis.det c)^2=1:= sq_eq_one_iff.mpr (b.det_to_matrix_orthonormalBasis_real c)
 let M:=r.motion.toLinearEquiv.toLinearMap
 have he:b.toBasis.det c=b.toBasis.det (M ∘ b.toBasis):=rfl
 rw [he,b.toBasis.det_comp, b.toBasis.det_self,mul_one] at hd; exact hd
lemma parameter_add (Ω:Ortho.Skew)(x y:ℝ): J Ω (x+y)=J Ω x * J Ω y:=by
 apply Subtype.ext; letI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
 change NormedSpace.exp ((x+y) • Ω.val)= NormedSpace.exp (x • Ω.val) * NormedSpace.exp (y • Ω.val)
 rw [add_smul]; exact NormedSpace.exp_add_of_commute (((Commute.refl Ω.val).smul_left x).smul_right y)
lemma proper_param (Ω:Ortho.Skew)(x:ℝ): Lorentz.properTurn (J Ω x):=by
 let t:=x/2; calc
  _= pdet (J Ω t * J Ω t):=by rw [← parameter_add,show t+t=x by unfold t; ring]
  _=1:=by rw [pdet_mul,← sq,pdet_range]
variable (R:Courts V)
export Work.A13 (oneParameter_zero)
lemma eu_back (U:Ortho) (h:Lorentz.properTurn U) (v:V) : R.eu U⁻¹ (R.eu U v)=v := by rw [← R.euMul _ _ (proper_inv h) h, inv_mul_cancel,R.eu1]
lemma eu_won (U:Ortho) (h:Lorentz.properTurn U) (v:V) : R.eu U (R.eu U⁻¹ v)=v := by rw [← R.euMul _ _ h (proper_inv h), mul_inv_cancel,R.eu1]
lemma kick_eu (a:SpaceAxis)(v:V) : R.eu (J (Ortho.plane timeAxis a.castSucc) 0) v=v:=by rw [oneParameter_zero, R.eu1]
end Courts
end YM.SatinWFixed
open YM.SatinWFixed
#print axioms Courts.proper_param
