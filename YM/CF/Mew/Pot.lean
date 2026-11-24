import YM.CF.Mew.Rain
import YM.CF.Mew.Terms
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 480000
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mew
open Function NormedSpace Filter Metric Finset MeasureTheory
open Skye Scree Jet Vow Lattice Wilson RG Forge Cube Fock Tulip Scroll Spire Peaks Pastry Lat -- tune Tint
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable{n: Side}{P:BudgetPoint}{I A E:Type*}[Fintype I][DecidableEq I][MeasurableSpace A][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
lemma pot_m (F:A→Key I→E)(h:∀ i,River (F i))(p:∀ z∈ hill I,Measurable fun i=>F i z)(u:List I):∀ z∈hill I, Measurable fun x=> lance (F x) u z:=by
 induction u generalizing F with
 | nil=> exact p
 | cons i l ih=>
    apply ih (fun x=> cutI (F x) i) (fun x=>(h x).flow i); intro z w
    let X(θ:ℝ)(x:A):E:= (homeB θ)⁻¹ • F x (update z i (homeB θ)); have ht:Measurable (uncurry X):=measurable_uncurry_of_continuous_of_measurable (fun a=>stayB (h a) w i) (fun j=>(p _ (fill_I w i (homeC _))).const_smul _) -- tune orientation
    exact ((ht.stronglyMeasurable.comp_measurable measurable_swap).integral_prod_right' (ν:=sky)).measurable
section complex
variable {J:Type*}[Fintype J][LinearOrder J]
local notation "𝓓"=>Dough J
-- expose without changing real operations outside client scope
scoped instance dough_scalar : SMul ℂ (Dough J) := ⟨fun i v=>⟨i • v.val,(fineShape v).smul i⟩⟩
scoped instance dough_algebra : Algebra ℂ (Dough J) where
 algebraMap:={toFun:=hollow,map_mul':=fun i j=>Subtype.ext (by change _ • (1:FC J)=(i • 1)*(j • (1:FC J)); simp; rw [smul_smul,mul_comm]), map_add':=fun i j=>Subtype.ext (show (i+j) • (1:FC J)=_ from add_smul ..),map_zero':=Subtype.ext (show (0:ℂ) • (1:FC J)=_ from zero_smul ..),map_one':=Subtype.ext (show (1:ℂ) • (1:FC J)=_ from one_smul ..)}
 commutes':=fun _ _=>mul_comm ..
 smul_def':=fun z v=>Subtype.ext (by change z • v.val=(z • (1:FC J))* v.val; rw [smul_mul_assoc,one_mul])
scoped instance dough_N : NormedAlgebra ℂ (Dough J) where
 norm_smul_le := fun z v => (norm_smul z v.val).le
scoped instance dough_p : IsScalarTower ℝ ℂ (Dough J) := ⟨fun x y a=>Subtype.ext (show (x • y) • a.val =x • y • a.val from smul_assoc ..)⟩
scoped instance dough_F : FiniteDimensional ℂ (Dough J) := Module.Finite.of_restrictScalars_finite ℝ .. -- tune
end complex

abbrev chipV(i: Finset (Dwell n)):Cipher n→L[ℂ]ℂ:= LinearMap.toContinuousLinearMap {toFun := fun x=> Pastry.crumb x.val i, map_add':=fun _ _=>rfl, map_smul':= fun _ _=>rfl}
variable (f:Key I→Cipher n)(p:River f)(i: List I)(j:Finset (Dwell n))
lemma leg_chip (p:River f): tipI (chipV j ∘ f) i= Pastry.crumb (tipI f i).val j:= sim_H p (chipV j) i roots
abbrev hueV (U: UNI (Single n)): Cipher n→L[ℂ]Cipher n:= LinearMap.toContinuousLinearMap
 {toFun:=paintR false false U, map_add':=fun x y=>map_add .., map_smul':=fun a x=> by
     apply Subtype.ext; change sings false _ (a • x.val)= a • sings false _ x.val; rw [singT,win_c, Fock.twist_scalar]; rfl} -- Uni namespace & False etc tune
lemma grainS(k: Finset (Dwell n))(p:River f)(u:∀ i∈hill I,Flour k (f i).val): Flour k (tipI f i).val:=by
 let v: Finset (Dwell n)→ℂ:=crumb (tipI f i).val; refine ⟨v,((fineShape (tipI f i)).allP).trans (Eq.symm (sum_subset (subset_univ _) fun j _ e=>?_))⟩
 unfold v; rw [←leg_chip f i j p,show tipI _ i= (0:ℂ) from ((lace_C i (f:=chipV j∘ f) (g:=fun _=>0) (fun y hy=> (u y hy).door e)) roots).trans (tip_0 i),zero_smul] -- tune
end YM.CF.Mew
