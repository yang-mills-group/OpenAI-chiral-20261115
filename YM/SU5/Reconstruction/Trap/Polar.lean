import YM.SU5.Reconstruction.Trap.Joy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.StarOrder
/-!
# Polar decomposition for communication through trap.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K H D S:Hilbert} (U:K→L[ℂ]H)
noncomputable def peel : K.Op := CFC.sqrt (U.adjoint.comp U)
lemma positive_peel : 0 ≤ peel U:= CFC.sqrt_nonneg _
lemma peel_sq : peel U * peel U = U.adjoint.comp U:= CFC.sqrt_mul_sqrt_self _ ((ContinuousLinearMap.nonneg_iff_isPositive _).2 U.isPositive_adjoint_comp_self)
lemma rootComm {A B:K.Op}(p:Commute A B): Commute (CFC.sqrt A) B:= by rw [CFC.sqrt_eq_cfc]; exact p.cfc_nnreal _
local notation "P" => peel U
lemma peel_funds (x:K):‖peel U x‖=‖U x‖:= by
  have h: IsSelfAdjoint P:= IsSelfAdjoint.of_nonneg (positive_peel ..); have e: inner ℂ (P x ) (P x)=inner ℂ (U x ) (U x):= by
    nth_rw 1 [show P x = (peel U).adjoint x from DFunLike.congr_fun (show peel U = (peel U).adjoint from h.symm) x]
    rw [ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.comp_apply, show (peel U).comp P = _ from peel_sq U, ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
  rw [@norm_eq_sqrt_re_inner ℂ,@norm_eq_sqrt_re_inner ℂ,e]
lemma peel_inj (p:Injective U) : Injective (peel U):=by
 intro x y h; apply p; apply sub_eq_zero.mp; apply norm_eq_zero.mp; rw [← map_sub, ← peel_funds, map_sub,h,sub_self,norm_zero]
lemma polar_dense {A:K.Op}(p:IsSelfAdjoint A ) (h:Injective A): DenseRange A:=by
  let S:= LinearMap.range A.toLinearMap; rw [DenseRange, dense_iff_closure_eq]; change (S.topologicalClosure:Set K)=_
  suffices he:S.topologicalClosure=⊤ by rw [he]; rfl
  letI: CompleteSpace S.topologicalClosure:= by infer_instance
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.orthogonal_closure]
  apply eq_bot_iff.mpr; intro y z; change y=0; apply h; rw [map_zero]; apply ext_inner_left ℂ; intro x; rw [inner_zero_right]; rw [show A=A.adjoint from p.symm]; rw [ContinuousLinearMap.adjoint_inner_right]; exact z _ ⟨x,rfl⟩
-- pervasive cancellations
lemma dense_cancel {f g:H→L[ℂ] S}(q:DenseRange U ) (e:f.comp U=g.comp U): f=g:= DFunLike.coe_injective (q.equalizer f.continuous g.continuous (funext fun x:K=> DFunLike.congr_fun e x)) -- tune
lemma strict_cancel {f g:S→L[ℂ] K}(p:Injective U ) (e:U.comp f=U.comp g): f=g:= ContinuousLinearMap.ext (fun x=>p (DFunLike.congr_fun e x))
lemma peel_dense (p:Injective U) : DenseRange (peel U):= polar_dense (IsSelfAdjoint.of_nonneg (positive_peel _)) (peel_inj U p)
lemma get_polar (p:Injective U ) (q:DenseRange U): ∃ W:K≃ₗᵢ[ℂ]H, ∀ x,W (peel U x)=U x:=by
 let B: K→L[ℂ]H:= U.toLinearMap.extendOfNorm (peel U).toLinearMap
 have e(x:K): B (P x)=U x:= LinearMap.extendOfNorm_eq (peel_dense U p) (⟨1, fun x=> le_of_eq (show ‖U x‖=1*‖P x‖ by rw [one_mul,peel_funds])⟩) x
 have h:∀ x,‖B x‖=‖x‖:= by
   intro x; apply congrFun (a:=x) ((peel_dense U p).equalizer B.continuous.norm continuous_norm ?_); funext x; change ‖B (P x)‖=‖P x‖; rw [e,peel_funds]
 let W: K→ₗᵢ[ℂ] H:= ⟨B.toLinearMap,h⟩
 refine ⟨LinearIsometryEquiv.ofSurjective W (fun x=> ?_),e⟩
 exact closure_minimal (fun y h=> by obtain ⟨x,rfl⟩:=h; exact ⟨P x,e x⟩) W.isometry.isClosedEmbedding.isClosed_range (q x)
namespace Clasp
variable (C:Clasp K H D)
noncomputable def Left : K≃ₗᵢ[ℂ] H:= Classical.choose (get_polar C.l C.j C.p)
noncomputable def Right: K≃ₗᵢ[ℂ] D:= Classical.choose (get_polar C.r C.k C.q)
local notation "A" => C.Left
local notation "B" => C.Right
lemma left_done (x:K): C.Left (peel C.l x)= C.l x:= Classical.choose_spec (get_polar C.l C.j C.p) x
lemma right_done (x:K): C.Right (peel C.r x)= C.r x:= Classical.choose_spec (get_polar C.r C.k C.q) x
lemma registered : peel C.l * peel C.l + peel C.r * peel C.r=1:=by rw [peel_sq,peel_sq]; exact C.frame
noncomputable def angle : K.Op:= C.l.adjoint.comp C.l
lemma angle_pos: 0≤ C.angle:= (ContinuousLinearMap.nonneg_iff_isPositive _).2 C.l.isPositive_adjoint_comp_self
lemma complement : C.r.adjoint.comp C.r=1-C.angle:= eq_sub_of_add_eq (by rw [add_comm]; exact C.frame)
lemma angle_le : C.angle≤1:= sub_nonneg.mp (C.complement ▸ ((ContinuousLinearMap.nonneg_iff_isPositive _).2 C.r.isPositive_adjoint_comp_self))
end Clasp
end YM.CrossedFrame
