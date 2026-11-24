import GaugeFieldConstruction.ProductData
import GaugeFieldConstruction.Conj
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Certifier interface. Describe square decompositions by kernel value tables.
 Not prescribing triangular Cholesky by a decomposition theorem. Exposing
 frames so they tensor with the true Slot and Color multiplicities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice
open Cauchy Row Finset Conj Function Complex
open scoped BigOperators
variable {α β γ η : Type*}
abbrev Area (s : Finset α) := Finsupp.supported ℂ ℂ (s : Set α)
lemma map_area {V : Type*} [AddCommGroup V] [Module ℂ V] {X : J α →ₗ[ℂ] V} {s : Finset α} {P : Submodule ℂ V} (h : ∀ i∈s, X (ket i)∈P):
    Area s ≤ P.comap X := by rw [Area,Finsupp.supported_eq_span_single,Submodule.span_le]; rintro _ ⟨i,h',rfl⟩; exact h i h'
lemma decomp {s : Finset α} {x : J α} (h : x∈ Area s): ∑ i∈s,x i • ket i=x := by
  classical
  rw [← Finset.sum_subset (s₁:=x.support) (fun i p=> h p) (fun i a b=>by simp_all)]
  simp only [ket,Finsupp.smul_single',smul_eq_mul,mul_one]; exact Finsupp.sum_single _

/-- a Gram certificate on a specified support (actual entries at those kets). -/
structure Window (α β : Type*) where
  hom : β→α→ℂ
  fare : β→ℝ
  modes : Finset β
namespace Window
variable {M : Window α β} {N : Window γ η}
def glance (M : Window α β) (k l : α) : ℂ := ∑ i∈M.modes,(M.fare i : ℂ) * star (M.hom i k) * M.hom i l
def read (M : Window α β) (i : β) := jet (M.hom i)
structure Valid (A : Finset α) (x : Window α β) : Prop where
  funds :∀ i∈x.modes,0<x.fare i
  poses :∀ p : J α,p∈ Area A → (∀ i∈x.modes,x.read i p=0)→p=0

def heavy (M : Window α β) (p q : J α) := ∑ i∈M.modes,(M.fare i:ℂ) * star (M.read i p) * M.read i q

def beam (M : Window α β) : J α →ₛₗ[bar] J α→ₗ[ℂ] ℂ where
  toFun p:= {
    toFun:=heavy M p
    map_add' a b:= by simp [heavy,mul_add,Finset.sum_add_distrib]
    map_smul' z a := by change _= z * heavy M p a; unfold heavy; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; simp; ring }
  map_add' a b:= LinearMap.ext fun i=>by
    change heavy M (a+b) i=_+_; simp only [heavy,map_add,star_add,mul_add,add_mul,Finset.sum_add_distrib]; rfl
  map_smul' z a:= LinearMap.ext fun i=>by
    change heavy M (z • a) i= bar z * heavy M a i; unfold heavy; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    change _=star z*_; simp; ring
lemma beam_at (i j : α) : M.beam (ket i) (ket j)=M.glance i j := by simp only [beam,LinearMap.coe_mk, AddHom.coe_mk,heavy, read,on_ket,glance]

abbrev Form (α : Type*) := J α →ₛₗ[bar] J α→ₗ[ℂ] ℂ
variable {s : Finset α} {t : Finset γ}
lemma checked {x : Form α} (h : ∀ i∈s, ∀ j∈s,x (ket i) (ket j)= M.glance i j) {a b} (p : a∈ Area s) (q : b∈ Area s):
    x a b=M.heavy a b := by
  change _= M.beam a b
  conv_lhs=> rw [← decomp p]; arg 2; rw [← decomp q]
  conv_rhs=> rw [← decomp p]; arg 2; rw [← decomp q]
  rw [map_sum x, LinearMap.sum_apply, map_sum M.beam,LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i hi
  rw [LinearMap.map_smulₛₗ x, LinearMap.map_smulₛₗ M.beam]; simp only [LinearMap.smul_apply]
  rw [map_sum (x _),map_sum]; congr 1; apply Finset.sum_congr rfl; intro j hj; rw [map_smul,map_smul,h i hi j hj,beam_at]

lemma pigment (t : ℝ) (a : ℂ) : ((t:ℂ)*star a*a).re = t*Complex.normSq a := by
  rw [mul_assoc]; simp [Complex.normSq_apply]
lemma priced (u : Valid s M) (a : J α) : 0 ≤ (M.heavy a a).re := by
  rw [heavy,re_sum]; apply Finset.sum_nonneg; intro i hi; rw [pigment]; exact mul_nonneg (u.funds i hi).le (normSq_nonneg _)
lemma warmth (u : Valid s M) (a : J α) (p : a∈ Area s) (q : a≠0) : 0< (M.heavy a a).re := by
  rw [heavy,re_sum]; apply Finset.sum_pos'
  · intro i hi; rw [pigment]; exact mul_nonneg (u.funds i hi).le (normSq_nonneg _)
  classical
  obtain ⟨i,hi,ti⟩ : ∃ i∈M.modes,M.read i a≠0 := by
    by_contra h; push Not at h; exact q (u.poses a p h)
  refine ⟨i,hi,?_⟩; rw [pigment]; exact mul_pos (u.funds i hi) (normSq_pos.mpr ti)

def Cross (m : Window α β) (n : Window γ η) : Window (α×γ) (β×η) where
  hom i j:= m.hom i.1 j.1*n.hom i.2 j.2
  fare i:= m.fare i.1*n.fare i.2
  modes:=m.modes ×ˢ n.modes
lemma crossed (x y : α×γ) : (M.Cross N).glance x y = M.glance x.1 y.1 * N.glance x.2 y.2 := by
  simp only [glance,Cross,Finset.sum_product]; rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; push_cast; rw [star_mul]; ring
lemma hand (i : β×η) : (M.Cross N).read i=productRead (M.read i.1) (N.read i.2) := ket_ext (fun j=>by
  simp only [Cross,read,productRead,on_ket])

lemma lifting {K : J γ→ₗ[ℂ]ℂ} {x : J (α×γ)} (H : x∈ Area (s ×ˢ t)) : oneWay K x∈ Area s :=
  map_area (P:=Area s) (X:=oneWay K) (fun ⟨i,j⟩ (p : _∈s ×ˢ t) => by change oneWay K _ ∈ _; rw [oneWay,on_ket]; exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ 1 (Finset.mem_product.mp p).1)) H
lemma serving {K : J α→ₗ[ℂ]ℂ} {x : J (α×γ)} (H : x∈ Area (s ×ˢ t)) : another K x∈ Area t :=
  map_area (P:=Area t) (X:=another K) (fun ⟨i,j⟩ (p : _∈s ×ˢ t) => by change another K _ ∈ _; rw [another,on_ket]; exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ 1 (Finset.mem_product.mp p).2)) H

lemma together (p : Valid s M) (q : Valid t N) : Valid (s ×ˢ t) (M.Cross N) := by
  constructor
  · rintro ⟨i,j⟩ h; obtain ⟨x,y⟩:= Finset.mem_product.mp h; exact mul_pos (p.funds i x) (q.funds j y)
  intro x hx e
  have he (g : J α→ₗ[ℂ]ℂ) (h : J γ →ₗ[ℂ]ℂ) : productRead g h=g ∘ₗ oneWay h:= ket_ext (fun ⟨i,j⟩=>by simp only [productRead,LinearMap.comp_apply,oneWay,on_ket,map_smul,smul_eq_mul]; rw [mul_comm])
  have hv (i) (u : i∈N.modes) : oneWay (N.read i) x=0 := by
    apply p.poses _ (lifting hx)
    intro j v; have H:= e (j,i) (Finset.mem_product.mpr ⟨v,u⟩); rw [hand,he] at H; exact H
  have h (K : J α→ₗ[ℂ]ℂ) : another K x=0 := by
    apply q.poses _ (serving hx); intro i hi
    have hr : N.read i ∘ₗ another K = productRead K (N.read i) := ket_ext (fun ⟨u,v⟩=> by rw [another,LinearMap.comp_apply,on_ket,map_smul,productRead,on_ket]; rfl)
    rw [← LinearMap.comp_apply,hr,he, LinearMap.comp_apply,hv i hi,map_zero]
  classical
  ext1 ⟨u,v⟩
  have H : Finsupp.lapply (R:=ℂ) v ∘ₗ another (Finsupp.lapply u)=(Finsupp.lapply (u,v): J (α×γ) →ₗ[ℂ] ℂ) := by
    apply ket_ext; rintro ⟨i,j⟩; simp only [another,LinearMap.comp_apply,on_ket,map_smul]
    change ket i u * ket j v=ket (i,j) (u,v)
    by_cases a:i=u <;> by_cases b:j=v <;> simp [ket,a,b]
  change Finsupp.lapply (R:=ℂ) (u,v) x=0; rw [← H,LinearMap.comp_apply,h,map_zero]

def delta (β : Type*) [Fintype β] [DecidableEq β] : Window β β where
  hom i j:= if i=j then 1 else 0
  fare _ := 1
  modes:= Finset.univ
lemma slate [Fintype β] [DecidableEq β] (i j:β) : (delta β).glance i j= if i=j then 1 else 0 := by
  simp [glance,delta,eq_comm]
lemma checked_d [Fintype β] [DecidableEq β] (p : Finset β) : Valid p (delta β) := by
  constructor
  · intro i h; change 0 < (1:ℝ); simp
  intro a u h; ext1 i
  have hv : (delta β).read i=Finsupp.lapply i := ket_ext fun j=>by simp [delta,read,ket,jet,Finsupp.linearCombination_single,Finsupp.single_apply,eq_comm]
  have e:= h i (Finset.mem_univ _); rw [hv] at e; exact e
-- adjust overall factor

def gain (M : Window α β) (c : ℝ) : Window α β := {M with fare:=fun i=>c * M.fare i}
lemma earning {c : ℝ} (u : Valid s M) (g : 0<c) : Valid s (M.gain c):= ⟨fun i h=>mul_pos g (u.funds i h),u.poses⟩
lemma sum_g (c : ℝ) (i j : α) : (M.gain c).glance i j=(c:ℂ)* M.glance i j := by
  unfold glance gain; dsimp only; rw [Finset.mul_sum]; push_cast; simp_rw [mul_assoc]
end Window
end YM.GaugeFieldConstruction.Invoice
