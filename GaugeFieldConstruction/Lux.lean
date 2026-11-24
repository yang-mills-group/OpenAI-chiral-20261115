import GaugeFieldConstruction.Enrol

/-!
# Single target slot identities against both comparison stress tensors (97).

Kernel pairing order: T(z) slot(x) rest(y). z-y pairing values in Fan.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Complex Cauchy Row Wick Phys Function Set Lamp U1 Gauge97
open YM.Maxwell (grad)
open Matter (Slot)
open scoped Topology ContDiff BigOperators
variable {x y z : E4}

-- purity & Touch
lemma prom (ac : ℂ) (s k l) (V : PW) (h : z≠x) (i j : Axis) : FG z x y (gStress ac i j) (sectionG s k l) V=
    ac * Photo.bip (fullG y s V) (Photo.placed 0 x k l) i j z := by
  let X:=sectionG s k l; let Y := fullG y s V; let T:= Photo.placed 0 x k l
  let B:=FG z x y
  have he (c i j a): B (times' (sectionG c i a) (sectionG c j a) + times' (sectionG c j a) (sectionG c i a)) X V= if c=s then 2*(Y i a z * T j a z + Y j a z*T i a z) else 0 := by
    rw [map_add, LinearMap.add_apply,LinearMap.add_apply]; simp only [B,overpay]
    change (outG x (sectionG c i a) z _ * outG y _ _ _+outG x (sectionG c j a) z _* outG y _ _ _)+ (_+_) = _
    by_cases ht:c=s
    · subst c
      have hp (i a) : eye (x-z) (ge (sectionG s i a) X)=T i a z:= Eq.trans (stampG s s k l i a h) (if_pos rfl)
      have hv (i a) : eye (y-z) (ge (sectionG s i a) V)=Y i a z:=rfl
      simp only [outG,hp,hv, if_true]; ring
    have hp (i a) : eye (x-z) (ge (sectionG c i a) X)=0 := Eq.trans (stampG s c k l i a h) (if_neg ht)
    simp [outG,hp,ht]
  have hg i j : B (graph_g (bill i j)) X V = ∑ a:Axis,(Y i a z*T j a z+Y j a z*T i a z) := by
    rw [gPalette]; simp_rw [map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,he]
    simp only [smul_eq_mul]
    have H' (c:Pig): (∑ a:Axis, if c=s then 2*(Y i a z*T j a z+Y j a z*T i a z) else 0)= if c=s then 2*(∑ a:Axis,(Y i a z*T j a z+Y j a z*T i a z)) else 0 := by split_ifs with h <;> simp [*,Finset.mul_sum]
    simp_rw [H']; rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ s)]; ring
  change B (gStress ac i j) X V= ac * Photo.bip Y T i j z
  unfold gStress recorded Photo.bip; simp only [map_smul,map_sub,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul,hg]
  split_ifs with H
  · -- Σ diag
    subst j; simp only [map_sum,LinearMap.sum_apply,hg,← two_mul,← Finset.mul_sum]; ring
  simp

-- F signs in Wick order. either one-cycle
lemma tune_F (z x y :E4) (s k z' a b) (V : FW) (u : Bool) (p : z≠x) (h : z≠y) :
    FF u z x y (sD z' z' (L b (Row.B a))) (sessionF s k) V = if z'=s then Tissue.shape u (fullF u y s V) (fun i z=>outF (!u) x (sessionF s i) z (sessionF s k)) a b z else 0 := by
  rw [degreeP]
  simp_rw [map_sum,map_smul,map_sub,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul]
  split_ifs with S
  · subst z'
    cases u
    · simp_rw [days]; unfold Tissue.shape; apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro d _
      have he (b : Bool) (i : Spin) (p : Axis) (x : FW) {r} (h : z ≠ r) : eye (r-z) (yarn b (stride b p (sessionF s i)) x)=grad p (fun z=> outF b r (sessionF s i) z x) z := (paidF b (show z∈intact r from h) _ _ _).symm -- args typo
      rw [he true _ _ _ p, he false _ _ _ h]; change _=Hij a c d * (outF false y _ _ _ * grad b (fun z=>outF true x _ z _) _- grad b (fun z=>outF false y _ z _) z * _)
      unfold outF; simp only [Bool.not_true,Bool.not_false]; ring
    simp_rw [sigh]; unfold Tissue.shape; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro d _
    have he (b : Bool) (i : Spin) (p : Axis) (x : FW) {r} (h : z ≠ r) : eye (r-z) (yarn b (stride b p (sessionF s i)) x)=grad p (fun z=> outF b r (sessionF s i) z x) z := (paidF b (show z∈ intact r from h) _ _ _).symm
    rw [he true _ _ _ h, he false _ _ _ p]; change _=Hij a d c * (outF true y _ _ _ * grad b (fun z=>outF false x _ z _) _ - grad b (fun z=>outF true y _ z _) z * _)
    unfold outF; simp only [Bool.not_true,Bool.not_false]; ring
  have hv (d : Bool) (i : Spin) (a:CJet): eye (x-z) (yarn d (atop z' a) (sessionF s i))=0 := by unfold yarn sessionF; rw [matchU,if_neg S,map_zero]
  have ht (d i) (j : Axis): eye (x-z) (yarn d (stride d j (sessionF z' i)) (sessionF s k))=0 := by rw [stride,sessionF,← Phys.here]; exact hv ..
  have hh (d i) : eye (x-z) (yarn d (sessionF z' i) (sessionF s k))=0:=hv ..
  cases u <;> simp only [days,sigh,hh,ht,zero_mul,add_zero,neg_zero,sub_self,mul_zero,Finset.sum_const_zero]

lemma leaf_eq (x y z : E4) (V : Bool→ℂ) (s k a b) (w : FW) (u : Bool) (p : z≠x) (h : z≠y) :
    FF u z x y (fStress V a b) (sessionF s k) w= V (rad s)* Tissue.force u (fullF u y s w) (Tissue.jewel u x k 0) a b z := by
  let G := fullF u y s w
  let J:= fun i z=>outF (!u) x (sessionF s i) z (sessionF s k)
  have hp i : J i =ᶠ[nhds z] Tissue.jewel u x k 0 i := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show z∈ intact x from p)] with y h; exact (stampF u s s k i h).trans (if_pos rfl)
  have hv c d : Tissue.shape u G J c d z = Tissue.shape u G (Tissue.jewel u x k 0) c d z := by
    unfold Tissue.shape; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro k _; rw [(hp k).self_of_nhds, show grad d (J k) z=_ from YM.Analysis.GermD _ (hp k)]; rfl
  have H (r p q) : FF u z x y (sD r r (L q (Row.B p))) (sessionF s k) w= if r=s then Tissue.shape u G (Tissue.jewel u x k 0) p q z else 0 := by
    rw [tune_F _ _ _ _ _ _ _ _ _ _ (h:=h) (p:=‹z≠x›)]
    split_ifs; exact hv p q
    rfl
  unfold fStress; simp_rw [map_sum,map_smul, map_add,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.add_apply,H]; rw [Finset.sum_eq_single s];
  · simp only [smul_eq_mul,↓reduceIte]; rfl
  · intro r _ v; simp [v]
  simp
end YM.GaugeFieldConstruction.Flux.One
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Complex Cauchy Row Wick Phys Function Set U1 Gauge97
open YM.Maxwell (grad)
open Matter (Slot)
open scoped Topology ContDiff BigOperators
variable {x y z : E4} {B : Dollars} {A : Lattice}

def Wd (A : Lattice) (k l : Axis) := ∑ i:Axis,( (↑(A i k):ℂ) • F i l + (↑(A i l):ℂ) • F k i)
def theta (A : Lattice) (b : Bool) (k c : Spin) := (1/4:ℂ)*∑ i:Axis,∑ j:Axis, (↑(A j i):ℂ)*∑ r:Spin,Tissue.M b j k r *star (Tissue.M b i c r)
def Wf (A : Lattice) (b : Bool) (k : Spin) := ∑ c:Spin,theta A b c k • C c 0

lemma pull {x y : E4} {χ : E4→ℝ} (u : Chassis x y χ) (W : Forms) (p : Forms) (K : Dollars) (r : ℂ)
    (h :∀ z:E4,z≠x→z≠y→∀ i j, W i j z = r • p i j z): Shell χ K W=r*Shell χ K p := by
  unfold Shell; rw [← atlas χ (currentZ K p)]
  refine only_grad _ _ (fun i z v=>?_)
  obtain ⟨x',y'⟩:= u.gate (YM.Maxwell.Free.gradient_part χ i v)
  change ∑ j : Axis,K j z • W i j z=r • ∑ j:Axis,K j z • p i j z; rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro j _; rw [h z x'.symm y'.symm]; exact smul_comm ..

lemma lampG (sk : Course B) (hv : Toll B A) (ac s k l) : (Flash (gStress ac)).Touch B ac
    (sectionG s k l) (atop s (Wd A k l)) := by
  let L:=Flash (gStress ac)
  intro x y χ c t
  have p : x ≠ y:=c.distinct
  let X:=L.toll x y (sectionG s k l) t
  let G:=Photo.bip (fullG y s t) (Photo.placed 0 x k l)
  let u (F : PW):= eye (y-x) (ge F t)
  change Shell χ B X = _
  rw [pull c X G B ac fun z h v i j=>prom _ _ _ _ t h i j]; congr 1
  unfold G Shell; rw [Photo.arc_pay B x c.toCost sk (out_wave ..) isOpen_compl_singleton (fun z h=>fun (q:z=y)=>c.there (q ▸ h)) c.here]
  change ∑ i : Axis,(_ + _ + _) = L.cost x y (atop _ (Wd A k l)) _ + ∑ i:Axis,_
  have he (i): grad i (fullG y s t k l) x=L.cost x y (lace i (sectionG s k l)) t := L.limit p _ t i
  simp only [he, Finset.sum_add_distrib,Wd,map_sum,map_add,map_smul, LinearMap.sum_apply,LinearMap.add_apply,LinearMap.smul_apply,Finset.sum_add_distrib]; simp only [real_smul,smul_eq_mul]
  have H a b : L.cost x y (atop s (F a b)) t=fullG y s t a b x := rfl
  simp_rw [H]; dsimp only [L,Flash]; unfold Toll at hv; simp_rw [hv]; abel
lemma lampF (sk : Course B) (hv : Toll B A) (V b s k) : (Glove (fStress V) b).Touch B (V (rad s)) (sessionF s k) (atop s (Wf A b k)) := by
  let L:=Glove (fStress V) b
  intro x y χ c t
  have p:=c.distinct
  let X:=L.toll x y (sessionF s k) t; let F:= fullF b y s t; let G:= Tissue.force b F (Tissue.jewel b x k 0)
  change Shell χ B X=_; rw [pull c X G B (V (rad s)) (fun z h v i j=> leaf_eq x y z V s k i j t b h v)] -- syntax
  congr 1; unfold Shell G; rw [Tissue.income isOpen_compl_singleton (out_law ..) c.toCost (fun z h=>fun (q:z=y)=>c.there (q ▸ h)) c.here sk k]
  unfold Tissue.payP
  have he (i): grad i (fullF b y s t k) x=L.cost x y (L.P i (sessionF s k)) t := L.limit p _ _ i
  change ∑ i:Axis, (B i x • grad i (fullF b y s t k) x + _)=L.cost x y (atop _ (Wf A b k)) _ + ∑ i:Axis,B i x • L.cost _ _ _ _
  simp only [he,Finset.sum_add_distrib,Wf,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]
  rw [add_comm]; congr 1
  have hp (j:Spin): L.cost x y (atop s (C j 0)) t=fullF b y s t j x:=rfl
  simp_rw [hp]; unfold theta; simp only [real_smul,smul_eq_mul, Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm (f:=fun j i=> ∑ l:Axis,_)] -- ambiguous
  apply Finset.sum_congr rfl; intro i _; -- inspect
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro k _; rw [hv i l x]; ring
end YM.GaugeFieldConstruction.Flux.One
