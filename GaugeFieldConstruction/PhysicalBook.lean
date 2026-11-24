import GaugeFieldConstruction.Formal
import GaugeFieldConstruction.FactorNames

/-!
# Placing the shell coordinates at their W2 slots
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Phys
open Cauchy Row Calibration Finset Function
open Matter (Slot FlavorIndex Generation)
open scoped BigOperators Matrix
abbrev Pig := Matter.G.ColorIndex
abbrev Pen := GIndex × Pig
abbrev Mode := FIndex × Slot
abbrev GaugePair := Pen × Pen
abbrev Spair := Mode × Mode
abbrev Trip := Spair × Pen
abbrev Book := ℂ × J GaugePair × J Spair × J Trip

def dye : OrthonormalBasis Pig ℝ Matter.C := EuclideanSpace.basisFun _ _
instance pigExists : Nonempty Pig := by
  haveI : Nontrivial Matter.C := CF.Thera.yet_one.nontrivial_color
  by_contra h
  haveI : IsEmpty Pig := not_nonempty_iff.mp h
  haveI : Subsingleton Matter.C := inferInstanceAs (Subsingleton (EuclideanSpace ℝ Pig))
  exact not_nontrivial_iff_subsingleton.mpr this inferInstance

variable {α β γ η : Type*}
/-- reindex with a color or a slot. -/
def atop (i : β) : J α →ₗ[ℂ] J (α×β) := times'.flip (ket i)
lemma heights (i : β) (x : α) : atop i (ket x)=ket (x,i) := takes ..
def strap (X : J α →ₗ[ℂ] J β) (Y : J γ →ₗ[ℂ] J η) : J (α×γ)→ₗ[ℂ] J (β×η) := onFirst X ∘ₗ onSecond Y
lemma straps (X : J α →ₗ[ℂ] J β) (Y : J γ →ₗ[ℂ] J η) (p q) : strap X Y (times' p q)=times' (X p) (Y q) := by simp only [strap, LinearMap.comp_apply,Cauchy.first,second] -- first

def sD (i j : Slot) : J f→ₗ[ℂ] J Spair := strap (atop i) (atop j)
def fD (i j : Slot) (k : Pig) : J x→ₗ[ℂ] J Trip := strap (sD i j) (atop k)
def yD (c d : Pig) : J g→ₗ[ℂ] J GaugePair := strap (atop c) (atop d)

lemma band (i j : Slot) (a b) : sD i j (ket (a,b))=ket ((a,i),(b,j)) := by rw [sD,← takes a b,straps,heights,heights,takes]
lemma crux (i j : Slot) (k) (a b c) : fD i j k (ket ((a,b),c)) = ket (((a,i),(b,j)),(c,k)) := by rw [fD, ← takes (a,b) c, straps,band,heights,takes]
lemma symd (i j : Pig) (a b) : yD i j (ket (a,b))=ket ((a,i),(b,j)) := by rw [yD,← takes a b,straps,heights,heights,takes]

def alpha (h : FlavorIndex) (i j : Slot) := Matter.jordan (Pi.single h 1) i j
def beta (h : FlavorIndex) (p : Pig) (i j : Slot) := Matter.forge (Pi.single h 1) (dye p) i j
/-- Factor 1/2 because U1 uses unordered *read* coordinates
 (both placements). -/
def graph_g : J g →ₗ[ℂ] J GaugePair := (1/2:ℂ) • ∑ p : Pig, yD p p

def tiap (h : FlavorIndex) : J f →ₗ[ℂ] J Spair := ∑ i : Slot, ∑ j:Slot, alpha h i j • sD i j
def tuap (h : FlavorIndex) : J x →ₗ[ℂ] J Trip := ∑ i : Slot, ∑ j:Slot, ∑ p:Pig, beta h p i j • fD i j p

def graph_f : Fragment (J f)→ₗ[ℂ] J Spair := ∑ h : FlavorIndex, tiap h ∘ₗ LinearMap.proj h
def graph_x : Fragment (J x)→ₗ[ℂ] J Trip := ∑ h : FlavorIndex, tuap h ∘ₗ LinearMap.proj h

def dress : Shell →ₗ[ℂ] Book := LinearMap.prodMap LinearMap.id (LinearMap.prodMap graph_g (LinearMap.prodMap graph_f graph_x))

abbrev test (i : α) : J α→ₗ[ℂ] ℂ := Finsupp.lapply i

private lemma coin {A B : Type*} (X : J A→ₗ[ℂ] J B) (t : B) (j : A) (u : Prop) [Decidable u] (q : A→ B)
    (H : ∀ i,X (ket i)=ket (q i)) (p : ∀ i,q i=t ↔ u ∧ i=j) (x) : test t (X x) = if u then test j x else 0 := by
  suffices h: test t ∘ₗ X= if u then test j else 0 by
    rw [← LinearMap.comp_apply,h]; split_ifs <;> rfl
  classical
  apply ket_ext; intro i
  rw [LinearMap.comp_apply,H]
  split_ifs with e
  · by_cases h:i=j <;> simp [test,ket,Finsupp.single_apply,p,e,h]
  simp [test,ket,Finsupp.single_apply,p,e]

lemma bank_g (i j : Pig) (a b) (x y z) : test ((a,i),(b,j)) (yD x y z) = if x=i ∧ y=j then z (a,b) else 0 :=
  coin _ _ (a,b) _ (fun v=>((v.1,x),(v.2,y))) (fun ⟨t,s⟩=> symd ..) (fun ⟨t,s⟩=>by simp only [Prod.mk.injEq]; tauto) _
lemma bank_f (i j : Slot) (a b) (x y z) : test ((a,i),(b,j)) (sD x y z) = if x=i ∧ y=j then z (a,b) else 0 :=
  coin _ _ (a,b) _ (fun v=> ((v.1,x),(v.2,y))) (fun ⟨t,s⟩=>band ..) (fun ⟨t,s⟩=>by simp only [Prod.mk.injEq]; tauto) _
lemma bank_x (i j : Slot) p (a b c) (x y k z) : test (((a,i),(b,j)),(c,p)) (fD x y k z)=
    if x=i ∧ y=j ∧ k=p then z ((a,b),c) else 0 := coin _ _ ((a,b),c) _ (fun v=>(((v.1.1,x),(v.1.2,y)),(v.2,k))) (fun ⟨⟨t,l⟩,s⟩=>crux ..) (fun ⟨⟨t,l⟩,s⟩=>by simp only [Prod.mk.injEq]; tauto) _

lemma income_g (a b : GIndex) (c d : Pig) (y) : test ((a,c),(b,d)) (graph_g y)=
    if c=d then (1/2:ℂ)*test (a,b) y else 0 := by
  rw [graph_g,LinearMap.smul_apply, LinearMap.sum_apply,map_smul,map_sum]
  simp_rw [bank_g, ite_and]; simp
lemma income_f (a b : FIndex) (i j : Slot) (h : FlavorIndex) (y) : test ((a,i),(b,j)) (tiap h y)=alpha h i j *test (a,b) y := by
  simp_rw [tiap,LinearMap.sum_apply,map_sum,LinearMap.smul_apply,map_smul,bank_f]
  simp [ite_and, Finset.sum_ite_irrel]
lemma income_x (a b : FIndex) (c : GIndex) (i j : Slot) (p : Pig) (h : FlavorIndex) (y) :
    test (((a,i),(b,j)),(c,p)) (tuap h y)= beta h p i j * test ((a,b),c) y := by
  simp_rw [tuap,LinearMap.sum_apply,map_sum,LinearMap.smul_apply,map_smul,bank_x]
  simp [ite_and, Finset.sum_ite_irrel]

lemma diagonals (p : FlavorIndex → ℂ) : ∑ k : FlavorIndex,p k • Pi.single k (1:ℂ)=p := by
  ext1 i; rw [Finset.sum_apply]; simp [Pi.single_apply]
lemma pocket_f (a b i j) (x) : test ((a,i),(b,j)) (graph_f x)=Matter.coeffs (fun k => x k (a,b)) i j := by
  unfold graph_f; rw [LinearMap.sum_apply, map_sum]; simp_rw [LinearMap.comp_apply, income_f,LinearMap.proj_apply]
  change _=Matter.jordan (fun k=>x k (a,b)) i j
  rw [← diagonals (fun k=>x k (a,b)),map_sum]; simp_rw [map_smul,Matrix.sum_apply]
  exact Finset.sum_congr rfl fun i _=> mul_comm ..
lemma pocket_x (a b i j c q) (X : Fragment (J x)) : test (((a,i),(b,j)),(c,q)) (graph_x X)=
    Matter.costing (fun k=> X k ((a,b),c)) (dye q) i j := by
  unfold graph_x; rw [LinearMap.sum_apply,map_sum]; simp_rw [LinearMap.comp_apply,income_x,LinearMap.proj_apply]
  change _=Matter.forge (fun k=> X k ((a,b),c)) (dye q) i j
  rw [← diagonals (fun k=> X k ((a,b),c)), map_sum, LinearMap.sum_apply]; simp_rw [map_smul,Matrix.sum_apply,LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun i _=> mul_comm ..
lemma gfaith : Injective graph_g := by
  intro a b h
  ext1 ⟨x,y⟩; let p : Pig := Classical.choice pigExists
  suffices (1/2:ℂ)*test (x,y) a=(1/2:ℂ)*test (x,y) b from mul_left_cancel₀ (by norm_num) this
  have he:= congr_arg (test ((x,p),(y,p))) h; simpa only [income_g,if_true] using he
lemma ffaith : Injective graph_f := by
  intro a b h
  ext1 i; ext1 ⟨x,y⟩
  suffices ∀ i:FlavorIndex,a i (x,y)=b i (x,y) from this i
  exact congr_fun (Matter.co_earn (Matrix.ext fun i j=> by rw [← pocket_f,← pocket_f,h]))
lemma xfaith : Injective graph_x := by
  intro a b h
  ext1 i; ext1 ⟨⟨x,w⟩,y⟩
  suffices ∀ i:FlavorIndex,a i ((x,w),y)=b i ((x,w),y) from this i
  exact congr_fun (Matter.cost_earn (dye.toBasis.ext fun k=> Matrix.ext fun i j=>by
    change Matter.costing _ (dye k) i j=Matter.costing _ (dye k) i j; rw [← pocket_x,← pocket_x,h]))
lemma dress_one (b : Shell) : (dress b).1=b.1:= rfl
lemma dressG (b : Shell) : (dress b).2.1=graph_g b.2.1:=rfl
lemma dressF (b : Shell) : (dress b).2.2.1=graph_f b.2.2.1:= by simp only [dress,LinearMap.prodMap_apply]
lemma dressX (b : Shell) : (dress b).2.2.2=graph_x b.2.2.2:= by simp only [dress,LinearMap.prodMap_apply]
lemma cred : Injective dress := by
  intro a b p
  apply Prod.ext
  · rw [← dress_one,← dress_one b,p]
  apply Prod.ext
  · apply gfaith; rw [← dressG,← dressG,p]
  apply Prod.ext
  · apply ffaith; rw [← dressF,← dressF,p]
  apply xfaith; rw [← dressX,← dressX,p]
end YM.GaugeFieldConstruction.Phys
