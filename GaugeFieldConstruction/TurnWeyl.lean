import GaugeFieldConstruction.SpinPay

/-! Spin shell tests turn under the displacement Signed. Swap chirality
on the mirror, keep indices on Weyl rows and columns. Mixed vs pure sign
tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Cauchy
open Function Matrix Finset
open scoped BigOperators Matrix ComplexOrder
variable (s : Signed)

def charge (p : P4) : M2 := ∑ i, p i • cliff i

private lemma crin (u : Spin → ℂ) (p : P4) (i : Spin) :
    (u ᵥ* charge p) i=∑ j:Axis, ∑ k:Spin, p j*u k* coeffCR false j i k := by
  simp [vecMul,charge,dotProduct,Matrix.sum_apply,coeffCR,cliff,Finset.mul_sum]
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _; ring

private lemma crout (u : Spin → ℂ) (p : P4) (i : Spin) :
    (charge p *ᵥ u) i=∑ j:Axis, ∑ k:Spin, p j *u k* coeffCR true j i k := by
  simp [mulVec,charge,dotProduct,Matrix.sum_apply, coeffCR,cliff,Finset.sum_mul]
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _; ring
lemma atc (w : Weyl false) : w.u ᵥ* charge w.p = 0 := funext fun i => (crin w.u w.p i).trans (w.chiral i)
lemma atr (w : Weyl true) : charge w.p *ᵥ w.u = 0 := funext fun i => (crout w.u w.p i).trans (w.chiral i)
def forgeC (u : Spin → ℂ) (p : P4) (h : u ᵥ* charge p = 0) : Weyl false :=
  ⟨p,u,fun i => by rw [← crin,h]; rfl⟩
def forgeR (u : Spin → ℂ) (p : P4) (h : charge p *ᵥ u = 0) : Weyl true :=
  ⟨p,u,fun i => by rw [← crout,h]; rfl⟩

def trsp (b : Bool) (A : M2) := if b then A.transpose else A

lemma return_p (p : P4) (i : Axis) : s⁻¹.act p i = pay (s.flip i) (p (s.perm i)) := by
  simp [Signed.act,pay]
lemma ledger (s : Signed) (M N : M2) (b : Bool)
    (h : ∀ i : Axis, M*trsp b (cliff i)*N=pay (s.flip i) (cliff (s.perm i))) (p : P4) :
    M*trsp b (charge (s⁻¹.act p))*N = charge p := by
  rw [
    show trsp b _ = ∑ i:Axis, s⁻¹.act p i • trsp b (cliff i) from
      show trsp b (charge _) = _ by cases b <;> simp [trsp,charge,Matrix.transpose_sum], charge]
  rw [Finset.mul_sum, Finset.sum_mul]; conv_rhs => rw [← Equiv.sum_comp s.perm]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.mul_smul, Matrix.smul_mul, h i, return_p]; cases s.flip i <;> simp

lemma B_read (c : Weyl false) (r : Weyl true) (i : Axis) :
    productRead c.read r.read (Row.B i)=(c.u ᵥ* cliff i) ⬝ᵥ r.u := by
  simp only [Row.B,map_sum,map_smul,smul_eq_mul,read_times, Weyl.read_C, vecMul,dotProduct]
  simp [power,cliff]; ring

private lemma in_cancel (U : M2) (hU : U ∈ unitary M2) (u : Spin → ℂ) (h : u ᵥ* U=0) : u=0 := by
  have hp : u ᵥ* (U*star U)=0 := by rw [← vecMul_vecMul,h]; simp
  rwa [show U*star U=1 from hU.2, vecMul_one] at hp
private lemma out_cancel (U : M2) (hU : U ∈ unitary M2) (u : Spin → ℂ) (h : U *ᵥ u=0) : u=0 := by
  have hp : (star U*U) *ᵥ u = 0 := by rw [← mulVec_mulVec,h]; simp
  rwa [show star U*U=1 from hU.1, one_mulVec] at hp

private lemma pair (X Y : M2) (u v : Spin → ℂ) (A : M2) :
    ((u ᵥ* X) ᵥ* A) ⬝ᵥ (Y *ᵥ v)=(u ᵥ* (X * A * Y)) ⬝ᵥ v := by
  rw [dotProduct_mulVec,vecMul_vecMul,vecMul_vecMul,mul_assoc]

open Row
/-- Relation for B letters *before* differentiation; f means `extra=true`,
because - for improper from swapping C and R; for the x jet tests
choose the other orientation so `extra=false` (additional - from transpose
of the Lie slot; the latter interpretation verified separately). -/
structure BoundsCR (s : Signed) (extra : Bool) (W : Weyl false) (V : Weyl true)
    (c : Weyl false) (r : Weyl true) : Prop where
  cr : c.p = s⁻¹.act (if signBit s then V.p else W.p)
  ct : r.p = s⁻¹.act (if signBit s then W.p else V.p)
  tax (i : Axis) : productRead c.read r.read (Row.B i)=
    pay ((signBit s && extra).xor (s.flip i)) (productRead W.read V.read (Row.B (s.perm i)))

theorem costCR (W : Weyl false) (V : Weyl true) (extra : Bool) : ∃ c r, BoundsCR s extra W V c r := by
  obtain ⟨U,h⟩ := payment s
  cases hv:signBit s
  · rw [hv] at h; let X := block U.val false false; let Y:=star (block U.val true true)
    have ht (i) : X*cliff i*Y=pay (s.flip i) (cliff (s.perm i)) := spin_transport h i
    have hp (p) : X*charge (s⁻¹.act p)*Y=charge p := ledger s X Y false (fun i => ht i) p
    have h₁ : X∈unitary M2 := right_frame h false
    have h₂ : Y∈unitary M2 := Unitary.star_mem (right_frame h true)
    let c := forgeC (W.u ᵥ* X) (s⁻¹.act W.p) (in_cancel Y h₂ _ (by
      rw [vecMul_vecMul,vecMul_vecMul,← mul_assoc,hp,atc]))
    let r := forgeR (Y *ᵥ V.u) (s⁻¹.act V.p) (out_cancel X h₁ _ (by
      rw [mulVec_mulVec _ X, mulVec_mulVec, hp,atr]))
    refine ⟨c,r,?_,?_,fun i => ?_⟩
    · rw [hv]; rfl
    · rw [hv]; rfl
    rw [B_read, B_read]
    dsimp only [c,r,forgeC,forgeR]
    rw [pair,ht,hv]; cases s.flip i <;> simp only [Bool.false_and,Bool.false_xor, pay_false,pay_true,vecMul_neg,neg_dotProduct]
  rw [hv] at h; let X := block U.val false true; let Y := star (block U.val true false)
  have ht (i) : X*(cliff i).transpose*Y=pay (s.flip i) (cliff (s.perm i)) := spin_transport h i
  have hp (p) : X*(charge (s⁻¹.act p)).transpose*Y=charge p := ledger s X Y true (fun i => ht i) p
  have h₁ : X∈unitary M2 := right_frame h false
  have h₂ : Y∈unitary M2 := Unitary.star_mem (right_frame h true)
  let z := Y *ᵥ V.u
  have he : z ᵥ* charge (s⁻¹.act V.p) = 0 := by
    rw [← Matrix.mulVec_transpose]
    apply out_cancel X h₁
    unfold z; rw [mulVec_mulVec _ X, mulVec_mulVec,hp,atr]
  have he' : pay extra z ᵥ* charge (s⁻¹.act V.p)=0 := by cases extra <;> simp [he,neg_vecMul]
  let c := forgeC (pay extra z) (s⁻¹.act V.p) he'
  let r := forgeR (W.u ᵥ* X) (s⁻¹.act W.p) (by
    rw [← Matrix.vecMul_transpose]; apply in_cancel Y h₂
    rw [vecMul_vecMul, vecMul_vecMul,← mul_assoc,hp,atc])
  refine ⟨c,r,?_,?_,fun i => ?_⟩
  · rw [hv]; rfl
  · rw [hv]; rfl
  rw [B_read, B_read]
  have eh : z ᵥ* (cliff i) ⬝ᵥ (W.u ᵥ* X) =
      (W.u ᵥ* (pay (s.flip i) (cliff (s.perm i)))) ⬝ᵥ V.u := by
    rw [← ht, ← pair, dotProduct_comm, ← dotProduct_mulVec, ← mulVec_transpose,dotProduct_mulVec,dotProduct_mulVec]
  dsimp only [c,r,forgeC,forgeR]
  rw [hv]
  cases extra <;> cases hs:s.flip i
  · rw [hs] at eh; exact eh
  · rw [hs] at eh; simpa only [pay_false,Bool.true_and,Bool.false_xor,pay_true,vecMul_neg,neg_dotProduct] using eh
  all_goals
    rw [hs] at eh; rw [pay_true, neg_vecMul,neg_dotProduct, eh]; simp only [pay_false,pay_true,vecMul_neg,neg_dotProduct, neg_neg] <;> rfl
end YM.GaugeFieldConstruction.Cauchy
