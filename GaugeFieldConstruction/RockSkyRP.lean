import GaugeFieldConstruction.WallSkyRP
import GaugeFieldConstruction.«VegaΛL»
/-! The local polynomial algebras; Reeh–Schlieder. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Mink Set Filter MeasureTheory Analysis Distribution LD Bid Work.C22 Work.C23 Work.C24 OS Small Complex Metric Poincare
open scoped BigOperators Topology ContDiff InnerProductSpace NNReal
variable {n m:ℕ}{G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}
variable {B:Small S C}{F:Waves S}{K:Spins S}{W:Surface S}{J:StarOp S}{D:∀ i,Blanket i}{R:S.Rotation}{s:S.RealSpin}
variable (d:PredictionL W F K J B R s){X:W.Aurora D}(H:X.FullBody F)(b: Hull B F J)
variable (U:Set E4)(o:IsOpen U)(q:U.Nonempty)
variable (p:Wightman S)
abbrev PolyBornRP (U:Set E4): Submodule ℂ p.operators.H:=Submodule.span ℂ (p.operators.vector '' {b|∀ l∈b,onSiteRP l U})
def LockerBornRP (U:Set E4): LockerΛL p U →ₗ[ℂ] p.operators.H where
 toFun A:= (A.val p.operators.omega).val
 map_add' :=fun _ _=>rfl
 map_smul' :=fun _ _=>rfl
lemma LockerBornAllRP (a:Sentence S)(h:∀ l∈a,onSiteRP l U): p.operators.pageRP a ∈ LockerΛL p U:=by
 induction a with
 | nil=> rw [Fields.pageZeroRP]; exact one_mem _
 | cons l a ih=> rw [Fields.pageMoreRP]; exact mul_mem (Algebra.subset_adjoin (show p.operators.edits l∈cargoΛL p U from ⟨l.1,l.2,(show anchoredRP l.2 U from h l (by simp)).1,rfl⟩)) (ih fun i t=> h i (by simp[t]))
lemma PolyBookingRP: PolyBornRP p U ≤ LinearMap.range (LockerBornRP p U):=by
 refine Submodule.span_le.mpr ?_; rintro _ ⟨a,t,rfl⟩; refine ⟨⟨_,LockerBornAllRP U p a t⟩,?_⟩
 have hx:p.operators.evaluates a=p.operators.pageRP a p.operators.omega:=by
    simpa [Fields.evaluates] using p.operators.fromPageRP a []
 exact congrArg Subtype.val hx.symm -- tune
include H b o q
lemma RockCrestRP: (PolyBornRP d.system U).topologicalClosure = ⊤:=by
 rw[← Submodule.orthogonal_orthogonal_eq_closure]; rw [Submodule.orthogonal_eq_top_iff]; refine le_antisymm ?_ bot_le
 intro x h; change x=0; refine (FillΩRP d H b U o x ?_ q); intro a v
 exact (Submodule.mem_orthogonal' _ _).1 h _ (Submodule.subset_span ⟨a,v,rfl⟩)
lemma TowerCrestRP: Dense (Set.range (LockerBornRP d.system U)):=by
 intro x; change x∈ (LinearMap.range (LockerBornRP d.system U)).topologicalClosure
 exact Submodule.topologicalClosure_mono (PolyBookingRP U d.system) ((RockCrestRP d H b U o q).symm ▸ (show x∈ (⊤:Submodule ℂ d.system.operators.H) from trivial))
variable {V:Set E4}
lemma LockWallRP(h:∀ x∈V,∀ y∈U,x-y∈spacelike)(a:LockerΛL d.system V)(p:LockerBornRP d.system V a=0):a=0:=by
 obtain ⟨B,e⟩:= (LockerΛSymL (F:=d.system) d.course V (A:=a)) -- tune
 let M:=d.system.operators
 have he:B.val=0:=by
    ext1 t; have hv(z:LockerΛL d.system U): a.val (z.val M.omega)=0:=by
       have hz:= StripeBΛL d.course V U h a.property z.property; rw [← Module.End.mul_apply,hz,Module.End.mul_apply,show a.val M.omega=0 from Subtype.ext p,map_zero]
    apply Subtype.ext; change (B.val t).val=0
    refine FillΩRP d H b U o _ (fun l k=>?_) q
    let Q := (⟨M.pageRP l,LockerBornAllRP U _ l k⟩ : LockerΛL d.system U); have hx: M.evaluates l = Q.val M.omega := by
       change M.evaluates l = M.pageRP l M.omega; simpa [Fields.evaluates] using M.fromPageRP l []
    apply inner_eq_zero_symm.mpr; change inner ℂ (M.evaluates l) (B.val t)=0; rw [hx, ← e.1, hv]; simp
 apply Subtype.ext; change a.val=0; ext1 x; apply (inner_self_eq_zero (𝕜:=ℂ)).1
 rw [e.1,he]; simp
#print axioms LockWallRP
end YM.NSF.Boundary
end
