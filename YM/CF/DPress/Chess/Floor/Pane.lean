import YM.CF.DPress.Chess.Floor.Borel
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt Sermon
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough ComplexOrder Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{ℓ d r:ℕ}{β u k:ℝ}{P:Loom n}
namespace Porch
variable (S: Support (More n)) (F: Fixed.Test n)
open BPress
open Fixed (matterRegion)
private def seed (V:Pane n): Pane n :=fun i=> if i.1∈ S∧ i.1+step i.2∈ S then V i else 1
lemma local_seed : LocalOn S (seed S):=by
 intro i j p; funext k; unfold seed; split
 next t=> exact p k t.1 t.2
 rfl
lemma relate_seed(i:Pane n) : Agrees S (seed S i) i:= fun _ e v=> if_pos ⟨e,v⟩
lemma seed_c : Continuous (seed S):=by apply continuous_pi; intro i; unfold seed; split; exact continuous_apply _; exact continuous_const
lemma choices (p:Boss n S F):∃ (A:ℕ→ Fixed.Test n)(C:ℝ),(∀ i,IsMark S (A i) C)∧(∀ i,Continuous (A i))∧∀ᵐ x∂prior SU.group (More n), Tendsto (fun i=> A i x) atTop (𝓝 (F x)):=by
 obtain ⟨v,p⟩:=p; let K:Submodule ℂ (ReOp n):= Print.spaceS (matterRegion n S) false; let μ:= (prior SU.group (More n)); let ν:= μ.map (seed S); let Z:= K.restrictScalars ℝ; let f(x):Z:= ⟨F x,p.even x⟩; let h:MeasurePreserving (seed S) μ ν:=⟨(seed_c S).measurable,rfl⟩; have hf:Measurable f:=p.borel.subtype_mk; letI:IsProbabilityMeasure ν:=Measure.isProbabilityMeasure_map h.measurable.aemeasurable
 obtain ⟨g,G,l,t⟩:=tend ν f hf (by have hx:= p.nonneg; linarith : (0:ℝ)<v+1) (fun i=> (p.cost i).trans (le_add_of_nonneg_right zero_le_one)) -- omega real? nonneg v needed
 let X(i:ℕ):Fixed.Test n:= Subtype.val ∘ g i ∘ seed S; have ht(i:ℕ):Continuous (X i):= continuous_subtype_val.comp ((G _).comp (seed_c S)); refine ⟨X,v+1,fun i=> ⟨fun x y p=>congrArg Subtype.val (congrArg (g i) (local_seed S x y p)),fun x=>(g i (seed S x)).property,(ht _).measurable,fun x=>l i (seed S x)⟩,ht,?_⟩; filter_upwards [h.quasiMeasurePreserving.ae t] with x e; rw [← p.reads _ _ (relate_seed S x)]; exact (continuous_subtype_val.tendsto (f (seed S x))).comp e
end Porch
end YM.CF.DPress.Chess
