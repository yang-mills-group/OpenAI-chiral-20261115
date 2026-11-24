import YM.SU5.Registration.Grading
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Operator blocks on the common domain

Tariff `(k,l,C)` for `A` means precisely `(m+1)^(k+2) ‖A m n‖ ≤ C*(n+1)^l`.
The two extra powers will pay l¹ on bands. Will use these estimates for
products of fields on the common domain, including passage to limits with
extra padding. **No pointwise field bound of this form presumed:** we will
prove these anisotropic bounds for *smeared* blocks from polynomial-growth
bounds on the point blocks by the true time-spectrum purchase on this sector.
Here deterministic Hilbert-space part.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinRegistration.Grading
open Set Filter Function
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace
variable {H : Hilbert}

/-- Only formal blocks, always on the indicated true spectral ranges. -/
@[ext]
structure Blocks (G : Grading H) where
  op : ℕ → ℕ → H.Op
  out (m n : ℕ) : (G.P m).comp (op m n)=op m n
  inlet (m n : ℕ) : (op m n).comp (G.P n)=op m n

variable (G : Grading H)
def dissect (B : H.Op) : Blocks G where
  op m n := ((G.P m).comp B).comp (G.P n)
  out m n := by ext1 x; exact G.project_same _ _
  inlet m n := by ext1 x; exact congrArg (fun y=> G.P m (B y)) (G.project_same x n)

theorem grade_ext {x y : H} (h : ∀ m, G.P m x=G.P m y) : x=y := by
  have hx:= G.sum x
  simp_rw [h] at hx
  exact hx.unique (G.sum y)

/-- Convenient positive l¹ weights for consuming the extra two powers. -/
def tariffW (n : ℕ) : ℝ := (weight 2 n)⁻¹
lemma tariffW_summable : Summable tariffW :=
  (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by omega))
lemma tariffW_nonneg (n : ℕ) : 0 ≤ tariffW n := inv_nonneg.mpr (weight_pos 2 n).le

/-- Domain map on the owning Hilbert. -/
def asPartial (A : G.domain →ₗ[ℂ] G.domain) : H →ₗ.[ℂ] H :=
  ⟨G.domain, G.domain.subtype.comp A⟩
lemma closable (A B : G.domain →ₗ[ℂ] G.domain)
    (h : ∀ x y : G.domain, inner ℂ x.1 (B y).1 = inner ℂ (A x).1 y.1) :
    (G.asPartial A).IsClosable := by
  have ha : (G.asPartial A).IsFormalAdjoint (G.asPartial B) := fun x y=> ?_
  · exact (LinearPMap.adjoint_isClosed G.grade_dense).isClosable.leIsClosable
      (ha.symm.le_adjoint G.grade_dense)
  exact (h x y).symm

namespace Blocks
variable {G} (A : Blocks G)

def Tariff (k l : ℕ) (C : ℝ) : Prop :=
  ∀ m n, weight (k+2) m * ‖A.op m n‖ ≤ C * weight l n
def Usable : Prop := ∀ k, ∃ l C, 0 ≤ C ∧ A.Tariff k l C

/-- Unconditional summable cost of these blocks on a domain input. -/
lemma point_bound {k l : ℕ} {C : ℝ} (h : A.Tariff k l C) (m n : ℕ) (x : H) :
    weight k m * ‖A.op m n x‖ ≤ (tariffW m*C) * G.due x l n := by
  have he : ‖A.op m n x‖ ≤ ‖A.op m n‖* ‖G.P n x‖ := by
    conv_lhs => rw [← DFunLike.congr_fun (A.inlet m n) x]
    exact (A.op m n).le_opNorm (G.P n x)
  apply le_of_mul_le_mul_left _ (weight_pos 2 m)
  calc weight 2 m * (weight k m * ‖A.op m n x‖) = weight (k+2) m* ‖A.op m n x‖ := by unfold weight; rw [pow_add]; ring
       _ ≤ weight (k+2) m * (‖A.op m n‖*‖G.P n x‖) := mul_le_mul_of_nonneg_left he (weight_pos _ _).le
       _ ≤ (C*weight l n)*‖G.P n x‖ := (mul_assoc _ _ _).ge.trans (mul_le_mul_of_nonneg_right (h m n) (norm_nonneg _))
       _ = _ := by unfold tariffW due; field_simp [(weight_pos 2 m).ne']

lemma series_cost {k : ℕ} (h : A.Usable) (x : G.domain) :
    Summable (fun p : ℕ×ℕ => weight k p.1 * ‖A.op p.1 p.2 x.1‖) := by
  obtain ⟨l,C,hC,p⟩:= h k
  exact ((tariffW_summable.mul_right C).mul_of_nonneg (rapid x.2 l)
    (fun m => mul_nonneg (tariffW_nonneg m) hC) (G.due_nonneg _ l)).of_nonneg_of_le
      (fun v => mul_nonneg (weight_pos k v.1).le (norm_nonneg _)) (fun v => A.point_bound p v.1 v.2 x.1)
lemma absolute (h : A.Usable) (x : G.domain) :
    Summable (fun p : ℕ×ℕ=> ‖A.op p.1 p.2 x.1‖) := by simpa only [weight,pow_zero,one_mul] using A.series_cost (k:=0) h x
lemma series_usable (h : A.Usable) (x : G.domain) : Summable (fun p : ℕ×ℕ=> A.op p.1 p.2 x.1) := (A.absolute h x).of_norm
lemma individual_rows (h : A.Usable) (m : ℕ) (x : G.domain) :
    Summable (fun n=> ‖A.op m n x.1‖) := (A.absolute h x).prod_factor m

def reach (x : G.domain) : H := ∑' p : ℕ×ℕ, A.op p.1 p.2 x.1
lemma row_eq (m : ℕ) (h : A.Usable) (x : G.domain) : G.P m (A.reach x) = ∑' n, A.op m n x.1 := by
  let r(p : ℕ×ℕ) := A.op p.1 p.2 x.1
  change G.P m (∑' p, r p)=_
  have he:Summable r:= A.series_usable h x
  rw [(G.P m).map_tsum he, (he.mapL (G.P m)).tsum_prod]
  rw [tsum_eq_single m]
  · exact tsum_congr fun n=> DFunLike.congr_fun (A.out m n) x.1
  intro i hi; rw [show (fun j:ℕ=> G.P m (r (i,j)))=fun _=>0 from ?_]; · rw [tsum_zero]
  funext j; trans G.P m (G.P i (r (i,j))); · exact congrArg _ (DFunLike.congr_fun (A.out i j) x.1|>.symm)
  exact G.project_other _ hi.symm

/-- Estimate shared with convergence proof. -/
lemma row_cost {k l : ℕ} {C : ℝ} (hC : A.Tariff k l C) (h : A.Usable) (x : G.domain) (m : ℕ) :
    G.due (A.reach x) k m ≤ (tariffW m * C) * G.budget l x.1 := by
  let v(n): H:= A.op m n x.1; have hv:Summable (fun n=>‖v n‖):=A.individual_rows h m x
  unfold due; rw [A.row_eq m h]
  calc weight k m * ‖∑' n, v n‖ ≤ weight k m * ∑' n, ‖v n‖ := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hv) (weight_pos k m).le
       _ = ∑' n, weight k m * ‖v n‖ := tsum_mul_left.symm
       _ ≤ ∑' n, (tariffW m * C) * G.due x.1 l n := (hv.mul_left _).tsum_le_tsum (fun n=>A.point_bound hC m n x.1) ((rapid x.2 l).mul_left _)
       _ = _ := tsum_mul_left

lemma reach_mem (h : A.Usable) (x : G.domain) : A.reach x ∈ G.domain := by
  intro k
  obtain ⟨l,C,-,u⟩:= h k
  exact ((tariffW_summable.mul_right C).mul_right (G.budget l x.1)).of_nonneg_of_le
    (G.due_nonneg _ k) (A.row_cost u h x)
lemma estimate {C : ℝ} {k l : ℕ} (h : A.Usable) (q : A.Tariff k l C) (x : G.domain) :
    G.budget k (A.reach x) ≤ ((∑' n, tariffW n)*C)*G.budget l x.1 := by
  refine ( (rapid (A.reach_mem h x) k).tsum_le_tsum (A.row_cost q h x) (((tariffW_summable.mul_right C).mul_right (G.budget l x.1)))).trans_eq ?_
  rw [tsum_mul_right,tsum_mul_right]

def acts (h : A.Usable) : G.domain →ₗ[ℂ] G.domain where
  toFun x := ⟨A.reach x,A.reach_mem h x⟩
  map_add' x y := by
    apply Subtype.ext
    change A.reach (x+y)=A.reach x+A.reach y
    unfold reach
    simp_rw [Submodule.coe_add,map_add]
    exact (A.series_usable h x).tsum_add (A.series_usable h y)
  map_smul' c x := by
    apply Subtype.ext
    change A.reach (c • x)= c • A.reach x
    simp only [reach,Submodule.coe_smul_of_tower,map_smul,tsum_const_smul'']

lemma reaches (h : A.Usable) (x : G.domain) : (A.acts h x).1=A.reach x:= rfl
lemma reaches_whole (B : H.Op) (e : A=G.dissect B) (h : A.Usable) (x : G.domain) :
    (A.acts h x).1=B x.1:= by
  subst A
  apply G.grade_ext
  intro m
  rw [reaches,row_eq _ m h]
  exact (((G.sum x.1).mapL B).mapL (G.P m)).tsum_eq

def dropBoth {ι : Type*} {f : Filter ι} (B : ι → Blocks G) :=
  ∀ k, ∃ l C, 0≤C ∧ A.Tariff k l C ∧ ∀ᶠ i in f, (B i).Tariff k l C
lemma row_approach {ι : Type*} {f : Filter ι} (B : ι → Blocks G)
    (hA : A.Usable) (hB : ∀ i, (B i).Usable) (h : A.dropBoth (f:=f) B)
    (u : ∀ m n (z : H), Tendsto (fun i => (B i).op m n z) f (𝓝 (A.op m n z)))
    (x : G.domain) (m : ℕ) : Tendsto (fun i=> G.P m ((B i).reach x)) f (𝓝 (G.P m (A.reach x))) := by
  simp_rw [row_eq A m hA x]
  rw [show (fun i=> G.P m ((B i).reach x)) = fun i=> ∑' n,(B i).op m n x.1 from funext fun i=>(B i).row_eq m (hB i) x];
  obtain ⟨l,C,-,-,hz⟩:= h 0
  refine tendsto_tsum_of_dominated_convergence ((rapid x.2 l).mul_left (tariffW m*C)) (fun n=> u m n x.1) (hz.mono fun i t n=>?_)
  simpa only [weight,pow_zero,one_mul] using (B i).point_bound t m n x.1

lemma approaches {ι : Type*} {f : Filter ι} (B : ι → Blocks G)
    (hA : A.Usable) (hB : ∀ i, (B i).Usable) (h : A.dropBoth (f:=f) B)
    (u : ∀ m n (z : H), Tendsto (fun i => (B i).op m n z) f (𝓝 (A.op m n z)))
    (x : G.domain) : G.Approaches f (fun i=> (B i).acts (hB i) x) (A.acts hA x) := by
  intro k; let y(i): H:= (B i).reach x; let z := A.reach x
  change Tendsto (fun i=> ∑' m, G.due (y i-z) k m) f (𝓝 0)
  rw [show (0:ℝ)=∑' _n:ℕ,(0:ℝ) from tsum_zero.symm]
  obtain ⟨l,C,-,hc,hv⟩:= h k
  refine tendsto_tsum_of_dominated_convergence ((tariffW_summable.mul_right C).mul_right (G.budget l x.1) |>.mul_left 2) (fun n=> ?_) (hv.mono fun i t m=>?_)
  · have hv := A.row_approach B hA hB h u x n
    have hw : Tendsto (fun i=> G.P n (y i-z)) f (𝓝 0) := by simp_rw [map_sub]; simpa only [z, sub_self] using hv.sub_const (G.P n z)
    simpa only [due,norm_zero,mul_zero] using hw.norm.const_mul (weight k n)
  rw [Real.norm_of_nonneg (G.due_nonneg (y i-z) k m), sub_eq_add_neg]
  let M:=(tariffW m*C)* G.budget l x.1; change G.due (y i + -z) k m ≤ 2*M
  rw [two_mul]; apply (G.due_add _ _ _ _).trans
  rw [G.due_neg]; exact add_le_add ((B i).row_cost t (hB i) x m) (A.row_cost hc hA x m)

lemma adjointness (B : Blocks G) (ha : A.Usable) (hb : B.Usable)
    (e : ∀ m n, (A.op m n).adjoint=B.op n m) (x y : G.domain) :
    inner ℂ (A.acts ha x).1 y.1 = inner ℂ x.1 (B.acts hb y).1 := by
  let p(s : ℕ×ℕ):= B.op s.1 s.2 y.1
  let K:=Equiv.prodComm ℕ ℕ
  have hv: ∀ s:ℕ×ℕ, inner ℂ (A.op s.1 s.2 x.1) y.1 = inner ℂ x.1 (p (K s)) :=
    fun s=> by change _= inner ℂ x.1 (B.op s.2 s.1 y.1); rw [←e,ContinuousLinearMap.adjoint_inner_right]
  let L:=innerSL ℂ x.1
  rw [A.reaches, B.reaches]; unfold reach
  have h: Summable p := B.series_usable hb y
  have ht: Summable (fun i:ℕ×ℕ=>p (K i)):=h.comp_injective K.injective
  suffices Q: inner ℂ (∑' s:ℕ×ℕ,A.op s.1 s.2 x.1) y.1 = ∑' s, inner ℂ x.1 (p (K s)) by
    rw [Q]; change (∑' s,L (p (K s)))= L (∑' s,p s); rw [←L.map_tsum ht, K.tsum_eq p]
  simp_rw [← hv]; let J:= (innerSL ℂ y.1)
  simp_rw [show ∀ z:H, inner ℂ z y.1=star (J z) from fun z=> (inner_conj_symm _ _).symm]; rw [J.map_tsum (A.series_usable ha x), tsum_star]

end Blocks
end YM.SatinRegistration.Grading
