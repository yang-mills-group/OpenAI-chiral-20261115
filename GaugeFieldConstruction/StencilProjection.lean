import YM.SU5.FiniteGaugeData.Tower.CompactFlight

/-!
# Comparing neutral and full frames when passing to continuous parts
-/
set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
open Function Set Filter Metric ContinuousLinearMap
open scoped Topology InnerProductSpace Classical
variable {I:Type*}{Γ:AddSubgroup ℝ}{H K:Hilbert}(S:Alliance I Γ H)(T:Alliance I Γ K)
variable (f:H→L[ℂ]K) (h:∀ (i:I)(a:Γ), f.comp ((S.crew i).play a) = ((T.crew i).play a).comp f)
  (d:Dense (Γ:Set ℝ))(l:List I)

local notation "η" => S.aviator l
local notation "Ά" => T.aviator l

include h
lemma markF (x:H)(v:x∈ S.aviator l) : f x∈ T.aviator l:= by
 rw [T.assembled]; intro i hi
 have he:ContinuousAt (fun a:Γ=> (S.crew i).play a x) 0 := (S.assembled l x).1 v i hi
 change ContinuousAt (fun a:Γ=> (T.crew i).play a (f x)) 0
 have hv(a:Γ): (T.crew i).play a (f x)=f ((S.crew i).play a x) := congrArg (fun A:H→L[ℂ]K=>A x) (h i a).symm
 simp_rw [hv]; exact f.continuous.continuousAt.comp he
lemma mark_back (x:K) (v:x∈ Ά) : f.adjoint x∈ η := by
 apply markF T S _ _ l x v
 intro i a; have he:= congrArg (fun (A:H→L[ℂ]K)=>A.adjoint) (h i (-a)); rwa [adjoint_comp,adjoint_comp,(S.crew _).neg_adjoint,(T.crew _).neg_adjoint,neg_neg,eq_comm] at he
-- star projection commutation. Can't just drop either projection from the continuation.
lemma level_projection (x:H):
    (T.aviator l).starProjection (f x)= f ((S.aviator l).starProjection x):= by
 apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (markF S T f h l _ ((η).starProjection_apply_mem _))
 intro p v; rw [←map_sub,← adjoint_inner_right]; exact Submodule.starProjection_inner_eq_zero _ _ (mark_back S T f h l _ v)

lemma maskProjectionL (A:H.Op)(B:K.Op)(p:f.comp A=B.comp f)(x:S.aviator l) :
   (T.aviator l).starProjection (B (f x.val))= f ((S.aviator l).starProjection (A x.val)) :=by
 rw [show B (f x.val)=f (A x.val) from congrArg (fun F:H→L[ℂ]K=> F x.val) p.symm]
 exact level_projection S T f h l _

lemma marksRaw(p:I→Γ)(x:H): f (S.raw l p x)= T.raw l p (f x):=by
 induction l with
 | nil=>rfl
 | cons i s ih=>
   rw [S.raw_step,T.raw_step]; change f ((S.crew i).play _ (S.raw s p x)) = (T.crew i).play _ (T.raw s p (f x)); rw [← ih]
   exact DFunLike.congr_fun (h i _) _
lemma marksReal(p:I→ℝ)(x:H)(v:x∈η): f (S.flight d l p x)= T.flight d l p (f x):= by
 have he(y:I→Γ): f (S.flight d l (fun i=>(y i:ℝ)) x)=T.flight d l (fun i=>(y i:ℝ)) (f x):=by
    rw [S.smooth_notch d l y,T.smooth_notch d l y]; change f (S.raw l y (S.stackS l x)) = T.raw l y (T.stackS l (f x)); rw [T.grounded l (markF S T f h l x v), S.grounded l v]; exact marksRaw S T f h l y x
 let F(p:I→ℝ):= f (S.flight d l p x); let G(p:I→ℝ):= T.flight d l p (f x)
 let X:= Set.pi Set.univ (fun _:I=> (Γ:Set ℝ))
 have hc:Continuous F:= f.continuous.comp (S.moves d l (fun p:I→ℝ=>p) (fun i _=> continuous_apply i) _ continuous_const)
 have hd:Continuous G:= T.moves d l (fun p:I→ℝ=>p) (fun i _=> continuous_apply i) _ continuous_const
 apply Set.EqOn.closure (show Set.EqOn F G X from ?_) hc hd (dense_pi (ι:=I) (α:=fun _=>ℝ) (s:=fun _=> (Γ:Set ℝ)) _ (fun _ _=>d) p)
 intro i hi; exact he (fun j=> ⟨i j,hi _ (Set.mem_univ _)⟩)

variable (F:H→ₗᵢ[ℂ]K) (u:∀ (i:I)(a:Γ), F.toContinuousLinearMap.comp ((S.crew i).play a) = ((T.crew i).play a).comp F.toContinuousLinearMap)
omit h
include u
noncomputable def mapLevels : ↥(S.Realm l) →ₗᵢ[ℂ] ↥(T.Realm l) where
 toFun y:= ⟨F y.val,markF S T F.toContinuousLinearMap u l y.val y.property⟩
 map_add' x y:= Subtype.ext (F.map_add x.val y.val)
 map_smul' c x:= Subtype.ext (F.map_smul c x.val)
 norm_map' x:=F.norm_map x.val
lemma flightLevels (p:I→ℝ)(x:S.Realm l): mapLevels S T l F u (S.aviation d l p x)=T.aviation d l p (mapLevels S T l F u x):= Subtype.ext (marksReal S T F.toContinuousLinearMap u d l p x.val x.property)
lemma mapFrameL (A:H.Op)(B:K.Op)(p:F.toContinuousLinearMap.comp A=B.comp F.toContinuousLinearMap)(x:S.Realm l):
    mapLevels S T l F u ((η).orthogonalProjectionOnto (A x.val))=
    ((Ά).orthogonalProjectionOnto (B (F x.val))) := by
 exact Subtype.ext (maskProjectionL S T F.toContinuousLinearMap u l A B p x).symm
#print axioms mapFrameL
#print axioms flightLevels
end YM.CF.Buffered.Afterglow.Tower.Germ.Alliance
end
