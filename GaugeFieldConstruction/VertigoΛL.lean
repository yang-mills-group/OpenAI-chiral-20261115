/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.SylvanΛL
/-!
 # Determining cyclic uniqueness. W words. Domain & P dominated. General pair proof adapted from YM.Next.Boundary.Core.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Finset Mink MeasureTheory Analysis Kernel
open scoped BigOperators Topology ContDiff InnerProductSpace
variable {G:Gauge}{L:Register G}{S:Table L}{Y X:Surface S}
lemma WordsWillΛL (h:∀ b:Sentence S,X.expect b=Y.expect b): X=Y:=by
 have hx(n:ℕ)(V:Fin n→ S.Union): X.W n V=Y.W n V:=by
    have he(b):X.W n V (Joint.materialize n b)=Y.W n V (Joint.materialize n b):=by
       have t:=h (List.ofFn fun i=>(V i,b i)); rw [Work.C29.expectOfFn,Work.C29.expectOfFn] at t; exact t
    let A:=X.W n V-Y.W n V; have ht: ⊤≤ (A.toLinearMap).ker :=calc
       _=(Submodule.span ℂ (Set.range (Joint.materialize n))).topologicalClosure:= (Work.C25.answer n).symm
       _≤ _:= Submodule.topologicalClosure_minimal _ (?_: Submodule.span ℂ (Set.range (Joint.materialize n)) ≤ A.toLinearMap.ker) A.isClosed_ker
    · apply sub_eq_zero.mp; ext1 x; exact ht (show x ∈ (⊤: Submodule ℂ (Joint n)) from trivial)
    apply Submodule.span_le.mpr; rintro i ⟨v,rfl⟩; exact sub_eq_zero.mpr (he v)
 cases X; cases Y; congr 1; exact funext fun i=> MultilinearMap.ext (hx i)
variable {F:Wightman S}{R:S.Rotation}{x:S.RealSpin}
variable (H:F.Realizes (W:=X) R x)
include H
noncomputable abbrev TraceWordΛL : Soil X F.J where
 H:= F.operators.H
 plant:= F.operators.vector
 dense:= H.total.cyclic ▸ H.total.everywhere
 measure:= F.operators.general _ H.meets _ H.adj
lemma WarCoveΛL (p:Poincare)(b:Sentence S): F.action.V p (F.operators.vector b)= F.operators.vector (F.spin.po p b):=by
 induction b with
 | nil=> exact H.covariance.vacuum p
 | cons i b ih=> cases i with
                 | mk x f=> change F.action.V p (F.operators.field x f (F.operators.evaluates b)).val=_; rw [H.covariance.covariance]; change (F.operators.field _ _ _).val= (F.operators.field _ _ _).val; congr 2; exact Subtype.ext ih
structure JointCloudΛL (F M: Wightman S) where
 space: F.operators.H≃ₗᵢ[ℂ] M.operators.H
 localH: F.operators.domain≃ₗᵢ[ℂ] M.operators.domain
 onLocal(v:F.operators.domain): (localH v).val= space v.val
 omega: space F.operators.vacuum= M.operators.vacuum
 evaluates(b:Sentence S): space (F.operators.vector b)= M.operators.vector b
 word(v:F.operators.domain) (x:S.Union)(f:Test4): localH (F.operators.field x f v)=M.operators.field x f (localH v)
 po(p:Poincare): space.toContinuousLinearEquiv.toContinuousLinearMap ∘L F.action.V p=M.action.V p ∘L space.toContinuousLinearEquiv.toContinuousLinearMap
variable {M: Wightman S}(u:M.Realizes (W:=X) R x)(j:M.J=F.J)(q:M.spin=F.spin)
include u j
private lemma DepotΛ : ∃ Z:F.operators.H→L[ℂ] M.operators.H,(∀ v:Sentence S,Z (F.operators.vector v)=M.operators.vector v) ∧ ∀ i:F.operators.H, ‖Z i‖=‖i‖:=by
 have he:= M.operators.general X u.meets M.J u.adj; rw[j] at he
 obtain ⟨A,-,h,p⟩:= Soil.universal_embed (TraceWordΛL H) (M:=M.operators.H) M.operators.vector he
 exact ⟨A,h,p⟩
include q
lemma OrbitUniqΛL : Nonempty (JointCloudΛL F M):=by
 obtain ⟨A,h,p⟩:= DepotΛ H u j; obtain ⟨Y,hY,-⟩:= DepotΛ u H j.symm
 have hv: A ∘L Y=ContinuousLinearMap.id ℂ _:= Kernel.Gram.by_bud (TraceWordΛL u) (fun i=>by change A (Y (M.operators.vector _))=_; rw[hY,h]; rfl)
 let T:F.operators.H→ₗᵢ[ℂ]M.operators.H:={ A.toLinearMap with norm_map':=p }
 have heT(v:F.operators.H) : T v=A v:=rfl
 let U:= LinearIsometryEquiv.ofSurjective T (fun y=>⟨Y y,DFunLike.congr_fun hv y⟩); let Ξ:= U.toContinuousLinearEquiv.toContinuousLinearMap
 have hs(v:Sentence S):U (F.operators.vector v)=M.operators.vector v:=h v
 let L:= U.toLinearEquiv.toLinearMap
 have he:F.operators.domain.map L=M.operators.domain:=by
    rw[H.total.cyclic,u.total.cyclic,Submodule.map_span]; congr 1; rw[← range_comp, show L ∘ F.operators.vector = M.operators.vector from funext hs]
 let J:= (U.submoduleMap F.operators.domain).trans (LinearIsometryEquiv.ofEq _ _ he)
 have hJ(p:F.operators.domain): (J p).val=U p.val:=rfl
 have hy(v:Sentence S): J (F.operators.evaluates v)= M.operators.evaluates v:= Subtype.ext (hs v)
 have hz(x:S.Union)(f:Test4)(v): J (F.operators.field x f v)=M.operators.field x f (J v):=by
    let T:=(J.toLinearEquiv).toLinearMap; let Y':=J.symm.toLinearEquiv.toLinearMap; let B:=F.operators.field x f; let B':=M.operators.field x f
    have h:B=Y' ∘ₗ (B' ∘ₗ T):=by
       apply DrivesΛL F.operators H.total; intro i; change B _= J.symm (B' (J (F.operators.evaluates i)))
       rw [hy]; exact (J.toLinearEquiv.eq_symm_apply).mpr (hy ((x,f)::i))
    change J (B v)=B' _; rw[h]; exact J.apply_symm_apply _
 have hw(v:Poincare) : Ξ ∘L F.action.V v=M.action.V v ∘L Ξ:=Kernel.Gram.by_bud (TraceWordΛL H) (fun b=>by change U (F.action.V v (F.operators.vector _))=M.action.V v (U (F.operators.vector _)); rw [WarCoveΛL H,hs,hs,WarCoveΛL u,q]) -- tune
 exact ⟨⟨U,J,hJ,hs [],hs,fun v x f=>hz x f v,hw⟩⟩
#print axioms OrbitUniqΛL
#print axioms WordsWillΛL
end YM.NSF.Boundary
end
