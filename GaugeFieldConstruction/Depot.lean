import GaugeFieldConstruction.Snip
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Coordinates in Grassmann pricing. Finite positions only. 
 Use compact subsequences, preserve strict comparison scheduling. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom.Sailing
open Function Filter Module Metric
open scoped Topology BigOperators InnerProductSpace
variable {F : Type*} [RCLike F]
variable {X Y A :Type*} [AddCommGroup X] [Module F X] [Module.Finite F X] [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] {l :Filter A}
local notation "S'" X => EuclideanSpace F (Fin (Module.finrank F X))

lemma grows [l.NeBot] (g : X→ₗ[F] Y) (x:A→X→ₗ[F]Y) (u:Injective g) (v:∀ i,Dips F l (fun k=> x k i) (g i)) (t:A→X) (z:Y) (w:Dips F l (fun k=> x k (t k)) z) : ∃ r:X,Dips F l t r ∧ g r=z:= by
  obtain ⟨L,h⟩:=g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr u)
  let R k:= L ∘ₗ x k
  have H :Dips F l t (L z):= by
    apply (ringed (L:=LinearMap.id) (f:=R) (fun i:X=> ?_) injective_id).2
    · exact maps w L
    have he : i=L (g i):=(LinearMap.congr_fun h i).symm
    have H : Dips F l (fun k=> R k i) (L (g i)):=maps (v i) L; rw [← he] at H; exact H
  exact ⟨_,H,individual (trav v t _ H) w⟩

-- all dimensions, choose orthonormal basis of scaled coordinates.
variable (F X) in
def pixels : X≃ₗ[F] EuclideanSpace F (Fin (Module.finrank F X)) := (Module.finBasis F X).equivFun.trans (EuclideanSpace.equiv _ F).symm.toLinearEquiv
variable [ProperSpace F]
lemma priceSweep (f : ℕ→ X→ₗ[F]Y) (h:∀ i, Injective (f i)): ∃ g:X→ₗ[F]Y, Injective g ∧ ∃ p:ℕ→ℕ, StrictMono p ∧ ∃ v : ℕ→ X≃ₗ[F] X, ∀ x,Dips F atTop (fun i=> f (p i) (v i x)) (g x):= by
  classical
  let E:= pixels F Y; let P:=pixels F X
  let Q:= EuclideanSpace F (Fin (Module.finrank F Y))
  let B k:= E.toLinearMap ∘ₗ f k -- poss Pi topology
  let W k:= LinearEquiv.ofInjective (B k) (show Injective _ from E.injective.comp (h k))
  let I:=Fin (Module.finrank F X)
  let T k: OrthonormalBasis I F (LinearMap.range (B k)):= (stdOrthonormalBasis ..).reindex (finCongr (W k).finrank_eq.symm)
  let C k:= (T k).repr.symm
  let V k: X≃ₗ[F] X:= (P.trans (C k).toLinearEquiv).trans (W k).symm
  let R k: EuclideanSpace F I →L[F] Q:= LinearMap.toContinuousLinearMap ((LinearMap.range (B k)).subtype ∘ₗ (C k).toLinearEquiv.toLinearMap)
  have H k: R k∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall,dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> ?_
    rw [one_mul]; exact ((C k).norm_map x).le
  have : ProperSpace ((EuclideanSpace F I)→L[F] Q):= FiniteDimensional.proper F _
  obtain ⟨A,_,p,hp,hA⟩:= (isCompact_closedBall ..).tendsto_subseq H
  have he x:Tendsto (fun i=> R (p i) x) atTop (𝓝 (A x)) := (show Continuous fun p : ((EuclideanSpace F I)→L[F] Q) => p x from continuous_id.clm_apply continuous_const).continuousAt.tendsto.comp hA
  have h : Injective A := by
    apply ((LinearMap.ker_eq_bot (f:=A.toLinearMap)).mp); apply LinearMap.ker_eq_bot'.mpr; intro x h
    have he:= tendsto_nhds_unique_of_eventuallyEq (he x|>.norm) tendsto_const_nhds (Eventually.of_forall (fun i=> ((C _).norm_map x))) -- p
    rw [show A x=0 from h,norm_zero] at he; exact norm_eq_zero.mp he.symm
  let g:= E.symm.toLinearMap ∘ₗ A.toLinearMap ∘ₗ P.toLinearMap
  refine ⟨g,E.symm.injective.comp (h.comp P.injective),p,hp,(fun i=> V (p i)),fun i=>?_⟩
  have U:= maps ((angel _ _).mpr (he (P i))) E.symm.toLinearMap
  refine constant U (Eventually.of_forall fun k=> ?_)
  apply E.injective
  change E (E.symm _) = _; rw [E.apply_symm_apply]; change ((C (p k) (P i)).val)=(W (p k) _).val
  unfold V; rw [LinearEquiv.trans_apply,(W (p k)).apply_symm_apply]; rfl
end YM.GaugeFieldConstruction.Fathom.Sailing
