import GaugeFieldConstruction.VertigoΛL
/-!
 # Local *algebra, means adjoint *on invariant domain*. Have arbitrary Schwartz word domain; box of local Observ usually bounded open, algebra carries product of *Operators* on cyclic domain. Record formal adj star uniqueness & locality for polynomial OBS.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Finset Mink MeasureTheory Analysis Kernel
open scoped BigOperators Topology ContDiff InnerProductSpace
variable {G:Gauge}{L:Register G}{S:Table L}{Y X:Surface S}
variable {F:Wightman S}{R:S.Rotation}{x:S.RealSpin}
variable (H:F.Realizes (W:=X) R x)
def cargoΛL (W:Wightman S)(U:Set E4):Set (Module.End ℂ W.operators.domain):={t | ∃ (x:S.Union)(f: Test4), tsupport f⊆U ∧ t=W.operators.field x f}
def LockerΛL (W:Wightman S)(U:Set E4):Subalgebra ℂ (Module.End ℂ W.operators.domain):= Algebra.adjoin ℂ (cargoΛL W U)
local notation "D_K" => F.operators.domain
variable (U V:Set E4)
abbrev ActorVerΛL (F: Wightman S)(A B: Module.End ℂ F.operators.domain):Prop:=∀ p q:F.operators.domain, inner ℂ (A p) q=inner ℂ p (B q)
lemma ActorOneΛL (A T B :Module.End ℂ F.operators.domain)(p:ActorVerΛL F A T)(q:ActorVerΛL F A B): T=B:= LinearMap.ext fun x=> ext_inner_left ℂ fun z=> (p z x).symm.trans (q z x)
include H
local notation "Tζ"=> LockerΛL F U
lemma LockerStarΛL {A: Module.End ℂ F.operators.domain}(a:A∈LockerΛL F U): ∃ B∈ Tζ, ActorVerΛL F A B:=by
 apply Algebra.adjoin_induction (p:=fun A _=> ∃ B∈Tζ,ActorVerΛL F A B) ?_ ?_ ?_ ?_ a
 · rintro _ ⟨x,f,h,rfl⟩; refine ⟨_,Algebra.subset_adjoin (show F.operators.field (F.J x) (Probe.bar f)∈cargoΛL F U from ⟨_,_,?_,rfl⟩),fun i j=> H.adj x f i j⟩
   refine Set.Subset.trans (closure_mono ?_) h
   intro y hy; apply Function.mem_support.mpr; intro v; apply Function.mem_support.mp hy; rw[Probe.bar_at, v]; simp
 · intro c; refine ⟨algebraMap ℂ _ (star c),Subalgebra.algebraMap_mem _ _, fun x y=>?_⟩; simp only[Algebra.algebraMap_eq_smul_one]; simp [inner_smul_left,inner_smul_right]
 · rintro x y _ _ ⟨B,t,p⟩ ⟨C,u,q⟩; exact ⟨B+C,add_mem t u, fun x y=>by simp [inner_add_left,inner_add_right,p _ _,q _ _]⟩
 rintro x y _ _ ⟨B,t,p⟩ ⟨C,u,q⟩; exact ⟨C*B,mul_mem u t, fun x y=>by rw [Module.End.mul_apply,Module.End.mul_apply,p,q]⟩
lemma LockerΛSymL {A : Tζ}: ∃! B : Tζ, ActorVerΛL F A.val B.val:=by
 obtain ⟨B,e,h⟩:= LockerStarΛL H U A.property; exact ⟨⟨B,e⟩,h,fun i u=> Subtype.ext (ActorOneΛL _ _ _ u h)⟩
lemma StripeBΛL (e:∀ x∈U,∀ y∈V,x-y∈spacelike){A B:Module.End ℂ F.operators.domain}(p:A∈LockerΛL F U)(q:B∈ LockerΛL F V): A*B=B*A:=by
 apply Algebra.adjoin_induction (p:=fun X _=> Commute X B) ?_ ?_ (fun x y _ _ a b=> a.add_left b) (fun x y _ _ a b=> a.mul_left b) p
 · rintro _ ⟨x,f,h,rfl⟩; apply Algebra.adjoin_induction (p:=fun Z _=> Commute _ Z) ?_ ?_ (fun x y _ _ a b=> a.add_right b) (fun x y _ _ a b=> a.mul_right b) q
   · rintro _ ⟨y,g,u,rfl⟩; exact LinearMap.ext (H.localPairs x y f g (fun a t b v=>e a (h t) b (u v)))
   intro c; exact (show Commute _ _ from Algebra.commutes c (F.operators.field x f)).symm
 intro c; exact Algebra.commutes ..
#print axioms LockerΛSymL
#print axioms StripeBΛL
end YM.NSF.Boundary
end
