import YM.SU5.FiniteGaugeData.Tower.Cloaks
import YM.SU5.FiniteGaugeData.Tower.Ink
import GaugeFieldConstruction.PavilionFe
import GaugeFieldConstruction.GladeFe
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Native gauge holds also on the step lift (no Protected equality hypotheses).
-/
open Fock Laurent Bloch Next.Free Fir Branch Tap Tenant Precision Drapes Vault Tree
open Reed (Fine think)
open BrentFe
open YM.GaugeFieldConstruction (Flavor)
open YM.GaugeFieldConstruction.Flavor
open XGarden.MastTin.ArtCart
set_option maxHeartbeats 70000
section
variable {N P : Side}
variable (g:Flavor)
abbrev latticeFφFe (N:Side) (X:Mark N): Mark N:= twist (quantU (TVfe N g)) ∘ X
private lemma colorLFe {S:Finset (Single N)}(i:Single N)(p:i∈ S)(h: (clanVFe g N) i∈ S): withinM S (acts (TVfe N g).val (basisKet i)):=by
 apply (within_test ..).2; intro k q; rw [basis_act]; rw [ilkFe]; rw [if_neg (show (i.1,g.sensor i.2) ≠ k from fun p=> q (p ▸ (show (i.1,g.sensor i.2)∈S from h)))] -- equality p types
lemma plant_Fe(i:Single N): (i∈ Tset N→ withinM (Tset N) (acts (TVfe N g).val (basisKet i)))∧ (i∈(Tset N)ᶜ→ withinM (Tset N)ᶜ (acts (TVfe N g).val (basisKet i))):=by
 rcases i with ⟨⟨x,i⟩,k⟩; have he: (clanVFe g N) ((x,i),k) ∈ Tset N ↔ ((x,i),k)∈ Tset N:=by
    rw [show clanVFe g N ((x,i),k)= ((x,i),sensor g k) from rfl]; simp [mem_Tset]
 exact ⟨fun p=>colorLFe g _ p (he.mpr p),fun p=>colorLFe g _ p (mem_compl.mpr (he.not.mpr (mem_compl.mp p)))⟩
lemma groundFe {S:Finset (Single N)}{b: Bool}{x:FC (Single N)}(p:Fine (Tset N) S b x):Fine (Tset N) univ b (twist (quantU (TVfe N g)) x):=by
 induction p with
 | empty=> rw[map_zero]; exact .empty _
 | one=> rw[map_one]; exact .one
 | grow _ _ a b=> rw[map_mul]; exact .grow a b
 | add _ _ a b=>rw[map_add]; exact .add a b
 | scale _ _ a=>rw[twist_scalar]; exact .scale a _
 | seed i p=>
    by_cases h:i∈ Tset N
    · rw [show (think (Tset N)).term i=Fock.put i from if_pos h,← create_put,twist_create]; exact fine_create _ ((plant_Fe ..).1 h) (within_univ _)
    rw [show (think (Tset N)).term i= -takeF i from if_neg h,←remove_take,map_neg,twist_remove]; exact fine_neg (fine_remove _ ((plant_Fe ..).2 (mem_compl.mpr h)) (within_univ _))
variable (G:Ratio N P)(j:ℕ)(o: Odd G.count.val)(M:Male)(Q: Op SU.Slot)(p:Commute (Ferr (chipUFe g)).val Q)
private lemma foot_Fe(x:BigFe): foot G (FieldFe P x).val=(ΨtFe G x).val:=by
 let f:=blast G; ext i j; change ((1:Op _)⊗ₖ(Ferr x).val) (f i.1,i.2) (f j.1,j.2)= ((1:Op _)⊗ₖ(Ferr x).val) i j; rw[Matrix.kronecker_apply,Matrix.kronecker_apply]; simp [Matrix.one_apply]
include p
lemma bymode_fe (x:Nom N P)(b:Bool)(v:Ket (Single N)) : acts (TVfe P g).val (byMode G j Q M x b v)=byMode G j Q M x b (acts (TVfe N g).val v):=by
 unfold TVfe; let F:=chipUFe g; rw[byMode_eq,byMode_eq,route_foot,foot_Fe,← act_mul,(tw_fe _ _|>.mp (clothFe F G x j M)),act_mul,patchFe,←act_mul (FieldFe _ _).val,←act_mul]; change _= _ -- tune
 rw [(tw_fe _ _).mp (show twist (FieldFe N F) (feeL b N Q)=_ from ?_)]
 cases b<;> simp [feeL, breeze_exp,plankFe F Q p] -- tune explicit p commute
lemma substitutionFe {S:Finset (Single N)}{A:FC (Single N)} {b:Bool}(u:Fine (Tset N) S b A) (z:Nom N P):subF G j Q M o z (twist (quantU (TVfe N g)) A)=twist (quantU (TVfe P g)) (subF G j Q M o z A):=by
 induction u with
 | empty=> simp only [map_zero]
 | one=> simp only [map_one,sub_one]
 | add _ _ x y=> rw[map_add,map_add,map_add,map_add,x,y]
 | scale _ _ x=> simp only [map_smul,twist_scalar,x]
 | grow a b f t=> rw [map_mul,sub_mul _ _ _ _ _ _ (groundFe g a) (groundFe g b),sub_mul G _ _ _ _ _ a b,map_mul,f,t]
 | seed i h=>
   by_cases t:i∈Tset N
   · rw[show (think (Tset N)).term i= put i from if_pos t,←create_put,twist_create,sub_create _ _ _ _ _ _ ((plant_Fe ..).1 t),sub_create _ _ _ _ _ _ (within_basis _ _ t), twist_create, bymode_fe g G j M Q p]
   rw[show (think (Tset N)).term i= -takeF i from if_neg t,map_neg,map_neg,map_neg,map_neg,←remove_take,twist_remove,sub_remove _ _ _ _ _ _ ((plant_Fe ..).2 (mem_compl.mpr t)),sub_remove _ _ _ _ _ _ (within_basis _ _ (mem_compl.mpr t)),twist_remove,bymode_fe g G j M Q p]
omit p
private lemma lifeIntegralFe {X:Type*}[MeasurableSpace X](μ:Measure X) (V:X→FC (Single N))(U:UNI (Finset (Single N))): twist U (∫ i, V i∂μ)=∫ i, twist U (V i)∂μ:=by
 let L:FC (Single N) →L[ℝ] FC (Single N):= (twist U).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
 have he:Isometry L:= isometry_iff_dist_eq.mpr (fun i j=>by rw[dist_eq_norm,←map_sub,dist_eq_norm]; exact twist_norm _ _)
 exact (ContinuousLinearMap.integral_comp_comm' L he.antilipschitz _).symm -- omit p
include p
lemma SharpGenFe (z:ℝ)(B:StepData (More N) (More P))(q:Chi)(β:ℝ)(l:Loom N){S:Support (More N)}{b:Bool}(X:Mark N)(h:AtSupport b S X):pushMark G B j Q M o q z β l (latticeFφFe g N X)=latticeFφFe g P (pushMark G B j Q M o q z β l X):=by
 let Ku:=quantU (TVfe P g); unfold pushMark latticeFφFe linkLaw; funext i; simp only [Function.comp_apply]; rw [lifeIntegralFe]; refine integral_congr_ae (Eventually.of_forall fun v=>?_); unfold Advance.assembled; dsimp only; rw [map_smul,lifeIntegralFe]; apply congrArg; refine integral_congr_ae (Eventually.of_forall fun z=>?_); unfold gathered avgF Advance.before; dsimp only; simp_rw [map_smul,map_sum]; apply congrArg; apply sum_congr rfl; intro a u; exact substitutionFe g G j o M Q p (h.allV _) _ -- tune shadow
end
end YM.CF.Buffered.Afterglow.Tower
