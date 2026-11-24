import YM.CF.DPress.Chess.Sermon.Stoic
import Mathlib.Analysis.Convex.Integral
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Sermon
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{K:Ratio n m}{S:StepData (More n) (More m)}{r ℓ d:ℕ}{β u k:ℝ}{P:Loom n}
lemma estate_mem {X R:Type*}[NormedAddCommGroup R][NormedSpace ℝ R][NormedSpace ℂ R][MeasurableSpace R][BorelSpace R][IsScalarTower ℝ ℂ R][FiniteDimensional ℝ R][SecondCountableTopology R][CompleteSpace R][MeasurableSpace X] {μ:Measure X}[IsProbabilityMeasure μ]{f:X→R}{S:Submodule ℂ R}(h:Envelope f)(t:∀ i,f i∈ S): (∫ x,f x∂μ)∈ S:=(S.restrictScalars ℝ).convex.integral_mem (S.restrictScalars ℝ).closed_of_finiteDimensional (Eventually.of_forall t) (Env.integrableX h _)
namespace Scope
variable {L:Side}(X: Scope L K S P ℓ d)
local notation "R_" => W.crop n Wall.rail
local notation "Q_" => W.crop n ℓ
local notation "ΨA"=> W.boost K.count
include X
variable [Nonempty (Forest (ratio K))] {A B:Fold K (ReOp m)} (h:Envelope A) (t:Envelope B)
include h
lemma estate {V:Support (More m)}(t:∀ i,RefineE V false (A i))(β:ℝ)(i:Stage m): RefineE V false (guide S β P A i):=by
 letI:IsProbabilityMeasure (Ξ SU.group S β i.1):=paid X.kernel _; let F:= Print.spaceE (Fixed.upperIndices m) (Fixed.matterRegion m V) false; apply estate_mem (S:=F) (Env.along (scoreH X.fee_m h) (g:=fun z=>(i,z)) measurable_prodMk_left); intro i; letI:=tight (K:=K) X.fee_m i; exact estate_mem (shelfK h ..) (fun i=>t _)
include t
lemma ferris {v:S.ratio=ratio K}(α:Hi W ℓ A)(γ:Hi W ℓ B)(x:Stage m)(i:Pane n): (∫ y, unc_N (retire W v A) x i y * unc_N B x i y∂νticket P i)= (sum_T P (retire W v A) x i)*(sum_T P B x i):=by
 obtain ⟨k,u,r,p,q,f⟩:= X.goodP; let Z:= W.negZ (Q_); let T:= root_M K Z; let J:= root_M K (Q_); let Y:= Ties (n:=More n) SU.group; let ν:=νticket (K:=K) P i; haveI:= tight (K:=K) X.fee_m i; haveI:=Robe.prob X.fee_m i; have hz:= Robe.twinP f _ _ i (W.rateF p n); let hp:Disjoint (Q_) Z:= W.night (a:=ℓ) (b:=ℓ) (by have ht:= Wall.Lot_h p; omega) n; have ht : Pairm ν J T:=by
    let M:=Counts (ratio K) (Q_); let R':= Bough.annual (ratio K); have he:Pairm (Bough.St _) M (R'.set Z):= Pairm.ofOrd (OrderF.extend R') (W.rateF p n|>.down (Nat.zero_le _) (halo_subset r _) (halo_subset r _)); exact he.joint hz
 exact ht.symm.money (shelfK (pension W v h) _ _) (shelfK t _ _) (fun x' y' p=> KnowH W α v x (i,x') (i,y') ⟨(Y _).iseqv.refl _,p⟩) (fun x' y' p=> knowingX W γ x (i,x') (i,y') ⟨(Y _).iseqv.refl _,p⟩)
-- $e$, multiplier equality. includes tag pairs and all needed-oracle priorities.
lemma prize {v:S.ratio=ratio K}(α:Hi W ℓ A)(γ:Hi W ℓ B)(β:ℝ): guide S β P ((retire W v A) * B) = fun x=> (ΨA).θ m (guide S β P A (wake (ΨA) x))*guide S β P B x:=by
 funext i; let ΞA:=Ξ SU.group S β i.1; letI:IsProbabilityMeasure ΞA:= paid X.kernel _; let y:=retire W v A; let p:=pension W v h; let a:=sum_T P y i; let b:=sum_T P B i; rw [←X.prism W h β i v]; have ht{Q:Fold K (ReOp m)}(p: Envelope Q): Envelope (sum_T P Q i):=Env.along (scoreH X.fee_m p) (g:=fun x=>(i,x)) measurable_prodMk_left
 have he:Pairm ΞA (Ties SU.group (R_)) (Ties SU.group (W.negZ (R_))):= Pairm.ofOrd (market (β:=β) X.kernel i.1) (BasicIid.P2U.mpr (W.night (a:=Wall.rail) (b:=Wall.rail) (by norm_num [Wall.rail]) n)); unfold guide; rw [show sum_T P (y* B) i=(fun i=>a i*b i) from funext (fun x=>X.ferris W h t α γ i x)]; exact he.symm.money (ht p) (ht t) (fun x y p'=> X.journey W p (KnowH W α v) i x y p') (fun x y p=> X.journal W t γ i x y p)
end Scope
end YM.CF.DPress.Chess.Sermon
