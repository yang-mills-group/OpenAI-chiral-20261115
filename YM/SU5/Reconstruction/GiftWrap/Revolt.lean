import YM.SU5.Reconstruction.Quartz.Marginalia
/-! # When all operators continue to orbit closure -/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Bouy
open Function Set Filter MeasureTheory Metric OS.Semigroup Picket Ravin BridgeClub Anvil ConePrice Sail Ship Waltz ContinuousLinearMap
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert} {a:Axis} (S:OS.Semigroup H a) (N:Submodule ℂ H) (q:IsClosed (N:Set H))
variable (Ω:H)(Z:Set H.Op)(h:∀ A∈Z,star A∈Z)(e:∀ A∈Z, MapsTo A N N)
include q h e
lemma clause (A:H.Op)(p:A∈ Auditorium Z) : MapsTo A N N:= by
 letI := q.completeSpace_coe; let P:= N.starProjection; let U:= N.orthogonal
 have H' (B:H.Op)(p:B∈ Z): MapsTo B (Nᗮ) (Nᗮ):= by
    intro x hx; intro y hy; rw [← ContinuousLinearMap.adjoint_inner_left B]; exact (show x∈Nᗮ from hx) _ (e (star B) (h B p) hy) -- orientation
 have v:P∈ Set.centralizer Z:= by
    intro y hy; ext1 x; change y (P x)= P (y x); symm; apply Submodule.eq_starProjection_of_mem_orthogonal (e y hy (?_: P x ∈ N)); · rw [←map_sub]; exact H' y hy (Submodule.sub_starProjection_mem_orthogonal x)
    unfold P; simp
 intro i t; apply Submodule.starProjection_eq_self_iff.mp; change P (A i)= _; rw [show P (A i)=A (P i) from DFunLike.congr_fun ((show A∈ Set.centralizer (Set.centralizer Z) from (lobby Z h) ▸ p) _ v) i, show P i=i from Submodule.starProjection_eq_self_iff.mpr t]
omit q h e
variable (M:Net H)
local notation "X" => parish M Ω
lemma hub : Ω∈ X:= transport_home M Ω 1 (one_mem _)
lemma loyal (A:H.Op)(v:A∈ M) : MapsTo A (parish M Ω) (parish M Ω):= by
 let B:= (X).comap A.toLinearMap; suffices t : X ≤ B from fun i p=> t p
 apply Submodule.topologicalClosure_minimal _ _ ((Submodule.isClosed_topologicalClosure _).preimage A.continuous); apply Submodule.span_le.mpr; rintro _ ⟨k,v',rfl⟩; change _∈ B; exact transport_home M Ω (A*k) (mul_mem v v') -- expr v h
include q
lemma extension (u:owns_it M Ω) (v:Ω∈ N)(k:∀ A∈ M,MapsTo A N N)(x:H) : x∈ N:= by
 apply Submodule.topologicalClosure_minimal _ _ q (u x); apply Submodule.span_le.mpr; rintro _ ⟨A,e0,rfl⟩; exact k A e0 v
omit q
lemma sees_ℓ (A:H.Op) (p:A∈M.commutant) (e:A Ω=0) (u:owns_it M Ω) : A=0:= by
 let P₀:= LinearMap.ker A.toLinearMap
 ext1 x; change A x=0; refine (show x∈ P₀ from ?_)
 exact Submodule.topologicalClosure_minimal (Submodule.span ℂ _) (Submodule.span_le.mpr (by
    rintro _ ⟨i,v,rfl⟩; change A (i Ω)=0; rw [show A (i Ω)=i (A Ω) from DFunLike.congr_fun ((VonNeumannAlgebra.mem_commutant_iff.mp p i v).symm) _, e,map_zero])) (isClosed_eq A.continuous continuous_const) (u x) -- tune
variable (hL:∀ x:E4,trans S x Ω=Ω)(hT:∀ x:E4,∀ A∈M,parcelUp S x A∈M)
include hL hT
lemma globalWalk (x:E4)(y:H)(e:y∈X) : trans S x y∈ X:= by
 let P₁:= (X).comap (trans S x).toLinearMap; suffices t:X ≤ P₁ from t e; apply Submodule.topologicalClosure_minimal _ _ (show IsClosed (P₁:Set H) from (Submodule.isClosed_topologicalClosure _).preimage (trans S x).continuous); apply Submodule.span_le.mpr; rintro _ ⟨k,v,rfl⟩; change trans S x (k Ω) ∈ X; rw [show trans S x (k Ω)= parcelUp S x k Ω from (by simp only[parcelUp,mul_apply_eq_comp,hL])]; exact transport_home M Ω _ (hT x k v)
end YM.Quartz.Bouy
