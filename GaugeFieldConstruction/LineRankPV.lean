import GaugeFieldConstruction.ChalkRankPV
import GaugeFieldConstruction.Coronal
/-
# Full c-real counts & weak prices. Do not reduce all.kernel criterion to histogram guesses. U.Transfer Exhaustion
-/
set_option autoImplicit false
set_option synthInstance.maxSize 14000
noncomputable section
namespace YM.GaugeFieldConstruction.Sunpath
open Calibration Raw Filter Module Function Cauchy Conj Ortho Ember LabelAction
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open Empire Fathom Floor Dawn
variable {S: City}{P : Axis → Across} (L:Sheds S P) {u:ℕ→ Carat}
def duskPV {α:Type*}(A : Labels α)(d : Floor) : invariant A d→ₛₗ[bar] invariant A d where
 toFun x:=⟨fun i=>shade _ (x.val i),⟨fun a=>⟨by change bar (x.val a).1=0; rw [show (x.val a).1=0 from (x.property.1 a).1]; exact map_zero _,
    fun v=>by rw [← color_s,(x.property.1 a).2 v]⟩,
    fun i s=>by rw[← comp_s,x.property.2]; cases A.cost s i <;> simp⟩⟩
 map_add' _ _:= Subtype.ext (funext fun _=>map_add ..)
 map_smul' a x:= Subtype.ext (funext fun i=>LinearMap.map_smulₛₗ _ a (x.val i))

lemma polarPV {α:Type*}(A : Labels α)(d : Floor)(x): duskPV A d (duskPV A d x)=x:=Subtype.ext (funext fun i=>clear (d:=d) (x.val i))

lemma totalInventoryPV : finrank ℝ ↥(RayPV (duskPV symAct four))=7 ∧ finrank ℝ ↥(RayPV (duskPV Raw.v five))=6 ∧ finrank ℝ ↥(RayPV (duskPV vsAct five))=60:= by
 letI : Module.Finite ℂ ↥SymT:= finiteInvariant ..
 letI : Module.Finite ℂ ↥BothV:= finiteInvariant ..
 letI : Module.Finite ℂ ↥OneW:= finiteInvariant ..
 rw [peakPV (duskPV symAct four) (polarPV _ _),peakPV (duskPV Raw.v five) (polarPV _ _),peakPV (duskPV vsAct five) (polarPV _ _)]
 exact ⟨sym_count,vector_count,pair_count⟩
private instance : Module.Finite ℂ ↥SymT:= finiteInvariant ..
private instance : Module.Finite ℂ ↥BothV:= finiteInvariant ..
private instance : Module.Finite ℂ ↥OneW:= finiteInvariant ..

-- Actual trajectory. derivative identities for all tests. no formal sixth degree allocations.
abbrev DuplexPV := OneW × BothV
def twilightPV : DuplexPV →ₛₗ[bar] DuplexPV where
 toFun x:= ((duskPV Raw.v five) x.1, (duskPV vsAct five) x.2)
 map_add' i j:= Prod.ext (map_add _ i.1 j.1) (map_add _ i.2 j.2)
 map_smul' r i:= Prod.ext (LinearMap.map_smulₛₗ _ r i.1) (LinearMap.map_smulₛₗ _ r i.2)
lemma nightPV x : twilightPV (twilightPV x)=x:= Prod.ext (polarPV ..) (polarPV ..)
lemma behindPV (x:SymT): around P L.toBend (duskPV _ _ x) = twilightPV (around P L.toBend x):= by
 apply Prod.ext
 · apply Subtype.ext; ext1 i
   change (Bend.sum _ _ _).val i=shade five ((Bend.sum _ _ _).val i); rw [Bend.payW,Bend.payW,map_sum]; apply Finset.sum_congr rfl; intro j Hj; exact (L.realD ..).symm
 exact Subtype.ext (funext fun i=> (L.realD ..).symm)
def BrightPV (L:Sheds S P): RayPV (duskPV symAct four)→ₗ[ℝ] RayPV twilightPV:= (RadialPV (duskPV symAct four) (around P L.toBend)).codRestrict _ (fun i=> (heightPV _ _).mpr (by change twilightPV (around _ _ i.val)=around _ _ i.val; rw [←behindPV L, (heightPV _ _).mp i.property]))
variable {C: Supplies L}
-- expose around in R form
include L
lemma matchPV (p: Scope L)(v: DuplexPV): (∀ (n:ℕ)(y:Fin n→ UV five)(k:Fin n), check S y k v=0)↔ ∃! x: SymT, around P L.toBend x=v:=by
 constructor
 · intro H
   have hy : v ∈ LinearMap.ker (readTest S):= by
      rw [LinearMap.mem_ker]; ext1 ⟨i,j⟩; ext1 ⟨a,b⟩; rw [read_v,H]; rfl
   rw [kernel_full L p] at hy
   obtain ⟨x,Hx⟩:= hy; exact ⟨x,Hx,fun y hy=> precedes L p (hy.trans Hx.symm)⟩
 rintro ⟨x,rfl,_⟩ n y k; exact trail L y k ⟨x,rfl⟩
lemma relatePV (p: Scope L)(v: RayPV twilightPV): (∀ (n:ℕ)(y:Fin n→ UV five)(k:Fin n), check S y k v.val=0) ↔ ∃! x: RayPV (duskPV symAct four), BrightPV L x=v :=by
 rw [matchPV L p]
 constructor
 · rintro ⟨x,H,h⟩; have Hx : x∈ RayPV (duskPV symAct four):=(heightPV _ _).mpr (h _ (by change around P L.toBend _=v.val; rw [behindPV L,H,(heightPV _ _).mp v.property]))
   exact ⟨⟨x,Hx⟩,Subtype.ext H,fun y hy=>Subtype.ext (h _ (congr_arg Subtype.val hy))⟩
 rintro ⟨x,H,h⟩; have V : around P L.toBend x.val=v.val:= congr_arg Subtype.val H; exact ⟨x.val,V,fun y hy=> precedes L p (hy.trans V.symm)⟩
lemma shopCountPV (p: Scope L): 1≤ finrank ℝ ↥(RayPV (sbar L)) ∧ finrank ℝ ↥(RayPV (sbar L)) ≤ 3 ∧ finrank ℝ ↥(LinearMap.range (RadialPV twilightPV (readTest S)))=59:=by
 haveI : Module.Finite ℂ ↥(Tot S P L):=@FiniteDimensional.finiteDimensional_submodule ℂ ↥SymT _ _ _ _ _
 rw [peakPV _ (sbar_twice L),trailRankPV twilightPV nightPV (readTest S)]
 · refine ⟨(counts L p).1, (counts L p).2,?_⟩
   have hx:= LinearMap.finrank_range_add_finrank_ker (readTest S); rw [kernel_full L p,LinearMap.finrank_range_of_inj (precedes L p),sym_count,Module.finrank_prod,pair_count,vector_count] at hx; omega
 simp only [kernel_full L p]; rintro i ⟨x,rfl⟩; exact ⟨_,behindPV L x⟩

omit L in
lemma refRankPV : finrank ℝ ↥(LinearMap.range (RadialPV twilightPV mine))=59:=by
 rw [trailRankPV twilightPV nightPV mine]
 · exact own
 simp only[moon,exact_93]; rintro i ⟨x,rfl⟩
 refine ⟨duskPV _ _ x, ?_⟩; apply Prod.ext
 · apply Subtype.ext; ext1 j; change (divergence _).val j=shade five ((divergence _).val j)
   rw[component_div,component_div,map_sum]; exact Finset.sum_congr rfl (fun i _=>(real_d ..).symm)
 exact Subtype.ext (funext fun i=>(real_d ..).symm)
#print axioms relatePV
#print axioms totalInventoryPV
#print axioms shopCountPV
#print axioms refRankPV
end YM.GaugeFieldConstruction.Sunpath
