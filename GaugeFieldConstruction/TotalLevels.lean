import GaugeFieldConstruction.Formal

/-!
# The full (93)–(94) counts over complex scalars
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.GaugeFieldConstruction
open Function Cauchy Row Record Calibration Floor U1 Raw Conj Module Submodule Finset
open Matter (FlavorIndex Generation)
open scoped BigOperators
namespace Calibration

-- Implement (93) on cost Jets (ambient allows formal derivatives)
def probe (i : Axis) {α} {d} (j : α) : (α → UV d) →ₗ[ℂ] Shell := P i ∘ₗ shells _ ∘ₗ LinearMap.proj j

def combMap : (OneW× BothV) →ₗ[ℂ] Axis × Axis → Shell := LinearMap.pi fun j=>
  ((∑ i : Axis, probe i ((j.1,ordered i j.2) : VS)) ∘ₗ BothV.subtype ∘ₗ LinearMap.snd ℂ _ _) -
    probe j.1 j.2 ∘ₗ OneW.subtype ∘ₗ LinearMap.fst ℂ _ _
lemma combo (a : OneW× BothV) (k j : Axis) :
    combMap a (k,j)=(∑ i, P i (shells five (a.2.val (k,ordered i j))))-P k (shells five (a.1.val j)) := by
  change (∑ i : Axis, probe i ((k,ordered i j): VS)) a.2.val - _ = _ -- tweak
  rw [LinearMap.sum_apply]; rfl

def previous := LinearMap.prod divergence gradient
lemma combo_chain : LinearMap.range previous ≤ LinearMap.ker combMap := by
  rintro _ ⟨t,rfl⟩; rw [LinearMap.mem_ker]; ext1 ⟨k,j⟩; rw [combo]
  change _-_=(0:Shell); apply sub_eq_zero.mpr
  change _ = P k (shells five ((divergence t).val j))
  rw [component_div,map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _
  have h u b : shells five (deriv u b)=P u (shells four b) := LinearMap.congr_fun (scene u) b
  change P i (shells five (deriv k _))= _; rw [h,h,exchanges]; rfl

def liftG (s : SymT) : TT recG gFour := (package four symAct s).1
def liftF (s : SymT) (b:Bool) : TT ph fFour := (package four symAct s).2.1 b
def liftX (s : SymT) (b:Bool) : TT recX xFour := (package four symAct s).2.2 b

def reportG (a: OneW × BothV) : (WW recG gFive).prod (VV recG gFive) :=
  ⟨(_, _),⟨(package five Raw.v a.1).1.property,(package five vsAct a.2).1.property⟩⟩
def reportF (a: OneW × BothV) (b : Bool) : (WW ph fFive).prod (VV ph fFive) :=
  ⟨(_, _),⟨((package five Raw.v a.1).2.1 b).property,((package five vsAct a.2).2.1 b).property⟩⟩
def reportX (a: OneW × BothV) (b : Bool) : (WW recX xFive).prod (VV recX xFive) :=
  ⟨(_, _),⟨((package five Raw.v a.1).2.2 b).property,((package five vsAct a.2).2.2 b).property⟩⟩
private lemma binding {a p : OneW × BothV} (s : reportG a=reportG p) (h : reportF a=reportF p)
    (t : reportX a=reportX p) : a=p := by
  apply Prod.ext
  all_goals
    first | apply (package five Raw.v).injective | apply (package five vsAct).injective
    refine Prod.ext ?_ (Prod.ext (funext fun b => ?_) (funext fun b => ?_))
  · exact Subtype.ext ((Prod.mk.inj (Subtype.mk.inj s)).1)
  · exact Subtype.ext ((Prod.mk.inj (Subtype.mk.inj (congr_fun h b))).1)
  · exact Subtype.ext ((Prod.mk.inj (Subtype.mk.inj (congr_fun t b))).1)
  · exact Subtype.ext ((Prod.mk.inj (Subtype.mk.inj s)).2)
  · exact Subtype.ext ((Prod.mk.inj (Subtype.mk.inj (congr_fun h b))).2)
  · exact Subtype.ext ((Prod.mk.inj (Subtype.mk.inj (congr_fun t b))).2)

def coG : Shell→ₗ[ℂ] J g := LinearMap.fst .. ∘ₗ LinearMap.snd ..
def coF (j : FlavorIndex) : Shell →ₗ[ℂ] J f := LinearMap.proj j ∘ₗ LinearMap.fst .. ∘ₗ LinearMap.snd .. ∘ₗ LinearMap.snd ..
def coX (j : FlavorIndex) : Shell →ₗ[ℂ] J x := LinearMap.proj j ∘ₗ LinearMap.snd .. ∘ₗ LinearMap.snd .. ∘ₗ LinearMap.snd ..
lemma compG (a : OneW× BothV) (k j : Axis) : coG (combMap a (k,j))=
    div_check recG gFive (reportG a) (k,j) := by
  rw [combo,map_sub,map_sum]
  change _= recG.divA _ _ - _; rw [divV]; rfl
lemma compF (a : OneW × BothV) (b : Bool) (k j : Axis) : coF (first b) (combMap a (k,j))=
    div_check ph fFive (reportF a b) (k,j) := by
  rw [combo,map_sub,map_sum]; change _ = ph.divA _ _-_; rw [divV]; rfl
lemma compX (a : OneW× BothV) (b : Bool) (k j : Axis) : coX (first b) (combMap a (k,j))=
    div_check recX xFive (reportX a b) (k,j) := by rw [combo,map_sub,map_sum]; change _=recX.divA _ _-_; rw [divV]; rfl
lemma levelG (t : SymT) : reportG (previous t)=arr recG _ _ dG (liftG t) := by
  apply Subtype.ext; refine Prod.ext ?_ rfl
  ext1 i
  change centered_g five ((divergence t).val i)=recG.divP _ i; rw [component_div,map_sum,divT]; rfl
lemma levelF (t : SymT) (b : Bool) : reportF (previous t) b=arr ph _ _ dF (liftF t b) := by
  apply Subtype.ext; refine Prod.ext ?_ rfl; ext1 i
  change centered_f five (first b) ((divergence t).val i)=ph.divP _ i; rw [component_div,map_sum,divT]; rfl
lemma levelX (t : SymT) (b : Bool) : reportX (previous t) b=arr recX xFour xFive (fun _=>bot_le) (liftX t b) := by
  apply Subtype.ext; refine Prod.ext ?_ rfl; ext1 i
  change centered_x five (first b) ((divergence t).val i)=recX.divP _ i; rw [component_div,map_sum,divT]; rfl
lemma combo_unique : Injective previous := by
  intro a b h
  haveI : Subsingleton ↥(TT recX xFour) := by rw [t_classX]; infer_instance
  have he : liftG a=liftG b := economy _ _ _ _ driveG <| by rw [← levelG,← levelG,h]
  have hp (i) : liftF a i=liftF b i :=economy _ _ _ _ driveF <| by rw [← levelF, ←levelF,h]
  apply (package four symAct).injective
  exact Prod.ext he (Prod.ext (funext fun i=>hp i) (funext fun i=>Subsingleton.elim (liftX a i) (liftX b i)))

lemma exact_93 : LinearMap.ker combMap=LinearMap.range previous := by
  refine le_antisymm ?_ combo_chain
  intro a h
  have ht k i : combMap a (k,i)=(0:Shell) := by rw [show combMap a=_ from h]; rfl
  have hu : reportG a∈LinearMap.ker (div_check recG gFive) := by
    rw [LinearMap.mem_ker]; ext1 ⟨k,i⟩; rw [← compG,ht,map_zero]; rfl
  have hv (b : Bool) : reportF a b∈LinearMap.ker (div_check ph fFive) := by
    rw [LinearMap.mem_ker]; ext1 ⟨k,i⟩; rw [← compF,ht,map_zero]; rfl
  have hx (b : Bool) : reportX a b∈LinearMap.ker (div_check recX xFive) := by
    rw [LinearMap.mem_ker]; ext1 ⟨k,i⟩; rw [← compX,ht,map_zero]; rfl
  rw [← exact_g] at hu; simp_rw [← exact_f] at hv; simp_rw [←exact_x] at hx
  obtain ⟨T,hT⟩:=hu; choose F hF using hv; choose X hX using hx
  let J := (package four symAct).symm (T,F,X)
  refine ⟨J,binding ?_ (funext fun b=>?_) (funext fun b=>?_)⟩
  · rw [levelG,liftG]; dsimp only [J]; rw [LinearEquiv.apply_symm_apply]; exact hT
  · rw [levelF,liftF]; dsimp only [J]; rw [LinearEquiv.apply_symm_apply]; exact hF b
  rw [levelX,liftX]; dsimp only [J]; rw [LinearEquiv.apply_symm_apply]; exact hX b
end Calibration
end YM.GaugeFieldConstruction
