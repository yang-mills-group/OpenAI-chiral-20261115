import YM.CF.Plume.Cord
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Plume
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B))(x:ℝ)
local notation "G₀"=> SU.group
local notation "n₀"=> (Domain N B)
local notation "m₀"=> (Domain P B)
local notation "Tabs"=>Arena.Tab S
variable{S}
open scoped Classical ENNReal NNReal
open Girt
structure Spark (X:Support n₀)(a b:Cord S):Prop where
 sharesB : Arena.Kind S a.1 b.1 X
 sharesE(i:Bond m₀): S.ratio.parent i.1∈ X → a.2.1.1 i=b.2.1.1 i∧ a.2.1.2 i=b.2.1.2 i
 sharesL(i:Seat (mid P B)): S.ratio.parent i∈ X → a.2.2 i=b.2.2 i
lemma sparks(X:Support n₀)(a b:Cord S): Spark X (mixT X a b) a:=by
 refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩ <;> intro i h <;> simp only [mixT,bothQ,Arena.unite,Arena.token,prQ,if_pos h,and_self]
lemma spark_m(X Y:Support n₀)(a b:Cord S)(p:Disjoint X Y): Spark X (mixT Y a b) b:=by
 refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩ <;> intro i h <;> simp only [mixT,bothQ,Arena.unite,Arena.token,prQ,if_neg (Finset.disjoint_left.mp p h),and_self]
lemma sparkle(X Y:Support n₀)(a b:Cord S)(h:X⊆Y)(p:Spark Y a b): Spark X a b:=⟨⟨fun i p'=>p.sharesB.up i (h p'),fun i p'=>p.sharesB.ht i (h p'),fun i p'=>p.sharesB.site i (h p'),fun i p'=>p.sharesB.edge i (h p')⟩,fun i k=>p.sharesE i (h k),fun i k=>p.sharesL i (h k)⟩
variable {s:ℝ}
def Aster(X:Support n₀)(Y:Cord S→ Cipher (mid N B))(s:ℝ):Prop:=∀ a b,Fairy S s a→ Fairy S s b→ Spark X a b→Y a=Y b
local notation "ν"=> plummy S s
lemma fly_p(p:0<s){X Y:Support n₀}(f g:Cord S→ Cipher (mid N B))(h:Aster X f s)(v:Aster Y g s)(q:Disjoint X Y)(u:Integrable f ν)(hz:Integrable g ν) : let Z:=fun x=> f x*g x; Integrable Z ν ∧ ∫ x, Z x∂ν=(∫ x,f x∂ν)*(∫ x,g x∂ν):=by
 intro Z; haveI:=plum_p S p
 let w:Cord S×Cord S → Cord S×Cord S := rollQ (mixT X); let T (x:Cord S×Cord S):= f x.1 * g x.2
 have he:=tone_p (S:=S) p; have ht:= MeasurePreserving.quasiMeasurePreserving (plum_m (S:=S) (X:=X) p)
 have hf := plum_m (S:=S) (X:=X) p; let w':Cord S×Cord S ≃ᵐ Cord S× Cord S:={toFun:=w,invFun:=w,left_inv:=roll_in _ (mix_t _),right_inv:=roll_in _ (mix_t _),measurable_toFun:=hf.measurable, measurable_invFun:=hf.measurable}
 have hU:∀ᵐ x∂Measure.prod ν ν,Fairy S s x.1∧ Fairy S s x.2:=Eventually.and ((measurePreserving_fst («ν»:= ν)).quasiMeasurePreserving.ae he) (measurePreserving_snd.quasiMeasurePreserving.ae he)
 have hV:∀ᵐ x∂ Measure.prod ν ν,T (w x)=Z x.1:=by
    filter_upwards [hU,ht.ae hU] with x p' t; exact congrArg₂ (· * ·) (h _ _ t.1 p'.1 (sparks ..)) (v _ _ t.2 p'.1 (spark_m _ _ _ _ q.symm))
 have H:T ∘ w =ᵐ[Measure.prod ν ν] (fun x=>Z x.1) := hV; have hx:= u.mul_prod hz; have hh: Integrable (T∘w) (Measure.prod ν ν):= (hf.integrable_comp_emb w'.measurableEmbedding).mpr hx; have hl:=hh.congr H
 refine ⟨hl.of_comp_fst (by exact NeZero.ne ν),?_ ⟩ -- tune
 have hy: (∫ i, T i∂Measure.prod ν ν)=(∫ x,f x∂ν)*∫ x,g x∂ν :=by
    rw [integral_prod T hx]; unfold T; simp_rw [integral_const_mul_of_integrable hz,integral_mul_const_of_integrable u]
 rw [←hy,← hf.integral_comp w'.measurableEmbedding T, integral_congr_ae hV,integral_prod _ hl]; simp only [integral_const, probReal_univ,one_smul]
variable (f : Palot.leaf (Site (Domain N B))→ Cord S→ Cipher (mid N B))(h:∀ i,Aster i.val (f i) s)(q:∀ i,Integrable (f i) (plummy S s))(p:0<s)
include h q p
lemma port_l(R: Palot.hook (Site (Domain N B)))(hp: Palot.flow _ R): Integrable (fun x=>∏ j∈ R,f j x) (plummy S s)∧ ∫ x,(∏ j∈ R,f j x)∂(plummy S s)= (∏ j∈R,∫ x,f j x∂(plummy S s)):=by
 induction R using Finset.induction_on with
 | empty=> haveI:=plum_p S p; simp
 | insert i Yw u v=>
    let g(x):= ∏ j∈Yw,f j x; let Y:= Palot.robe Yw; have hh:Palot.flow _ Yw:= Palot.flow_m hp (subset_insert ..); obtain ⟨t,w⟩:= v hh
    have ht:Aster Y g s:=by intro x y e k p; exact prod_congr rfl fun j v=> h j x y e k (sparkle j.val Y x y (fun _ κ=>Finset.mem_biUnion.mpr ⟨j,v,κ⟩) p)
    have he:= fly_p p (f i) g (h i) ht (Palot.flow_d hp u) (q i) t
    dsimp only at he; simp_rw [prod_insert u]; rw [←w]; exact he
lemma high_r(O:Support (Domain N B)):Integrable (fun z=>hGas O (fun i=> f i z)) (plummy S s) ∧ ∫ z,hGas O (fun i=> f i z)∂(plummy S s)= hGas O (fun i=> ∫ z,f i z∂(plummy S s)):=by
 let Z:= univ.filter (fun R: Palot.hook (Site (Domain N B))=> Palot.flow _ R∧ O⊆ Palot.robe R); have he(R)(h':R∈ Z):Integrable (fun x=> ∏ j∈R,f j x) (plummy S s):=(port_l f h q p R (mem_filter.mp h').2.1).1; exact ⟨integrable_finsetSum Z he,(integral_finsetSum Z he).trans (sum_congr rfl fun i p'=> (port_l f h q p i (mem_filter.mp p').2.1).2)⟩
end YM.CF.Plume
