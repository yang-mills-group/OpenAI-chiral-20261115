import YM.CF.Fock.Ratio
import YM.CF.Fock.Snow

/-! Change to the sector relative to a filled band. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
section core
variable {n : Type*} [Fintype n] [DecidableEq n] {P C : Op n}

def reserve (P C : Op n) := (stage P C)⁻¹ * P
lemma reserve_r (h : IsStarProjection P) : reserve P C*P=reserve P C := by rw [reserve,mul_assoc,h.isIdempotentElem]
lemma reserve_l (h : IsStarProjection P) (g : IsUnit (stage P C)) : cc P*reserve P C=reserve P C := by rw [reserve,←mul_assoc,stage_il h g,mul_assoc,h.isIdempotentElem]
lemma reserve_il (h : IsStarProjection P) (g : IsUnit (stage P C)) : reserve P C*body P C=cc P := by
  rw [reserve,mul_assoc, body_left h,←stage_right h,←mul_assoc,(live g).2,one_mul] -- tune
lemma reserve_ir (h : IsStarProjection P) (g : IsUnit (stage P C)) : body P C*reserve P C=P := by
  rw [←stage_left h,reserve, mul_assoc,(show stage P C*((stage P C)⁻¹ * P)=P by rw [←mul_assoc,(live g).1,one_mul]),h.isIdempotentElem]
lemma body_skew (h : IsStarProjection P) (g : Cᵀ= -C) : (body P C)ᵀ= -body P C := by
  have H : cc P=Pᵀ := by rw [cc,h.isSelfAdjoint]
  rw [body,H]; exact skew_form g
lemma stage_skew (h : IsStarProjection P) (g : Cᵀ= -C) : (stage P C)ᵀ= -stage P C := by rw [stage,Matrix.transpose_add,body_skew h g,body_skew h.one_sub g]; abel
lemma inv_skew {A : Op n} (e : IsUnit A) (g : Aᵀ= -A) : A⁻¹ᵀ= -A⁻¹ := by
  have he : A⁻¹ᵀ * (-A)=1 := by rw [←g,←Matrix.transpose_mul,(live e).1,Matrix.transpose_one]
  have ht : (-A)*(-A⁻¹)=1 := by rw [neg_mul_neg,(live e).1]
  calc A⁻¹ᵀ = A⁻¹ᵀ * ((-A)*(-A⁻¹)) := by rw [ht,mul_one]
       _ = _ := by rw [←mul_assoc,he,one_mul]
lemma reserve_skew (h : IsStarProjection P) (k : IsUnit (stage P C)) (g : Cᵀ= -C) : (reserve P C)ᵀ= -reserve P C := by
  rw [reserve,Matrix.transpose_mul,inv_skew k (stage_skew h g),mul_neg,show Pᵀ=cc P by rw [cc,h.isSelfAdjoint],stage_il h k]
-- four blocks
/-- hole--particle -/
def driftB (P C : Op n) := -(reserve P C*C*cc (1-P))
/-- particle--particle -/
def weldB (P C : Op n) := (1-P)*(C-C*reserve P C*C)*cc (1-P)
/-- meaningful in a coordinate frame frozen on its cut set -/
def blend (P C : Op n) := reserve P C+driftB P C-(driftB P C)ᵀ+weldB P C
lemma weld_skew (h : IsStarProjection P) (k : IsUnit (stage P C)) (g : Cᵀ= -C) : (weldB P C)ᵀ= -weldB P C := by
  apply body_skew h.one_sub
  rw [Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_mul,reserve_skew h k g,g]; simp only [neg_mul,mul_neg,neg_neg,←mul_assoc]; abel
lemma blend_skew (h : IsStarProjection P) (k : IsUnit (stage P C)) (g : Cᵀ= -C) : (blend P C)ᵀ= -blend P C := by
  rw [blend,Matrix.transpose_add,Matrix.transpose_sub,Matrix.transpose_add, reserve_skew h k g,Matrix.transpose_transpose, weld_skew h k g]; abel
end core
variable {n : Type*} [LinearOrder n] [Fintype n] {C P : Op n}
lemma slide_blend {s : Finset n} (e : P=cutM s) (k : IsUnit (stage P C)) (g : Cᵀ= -C) (a b : Ket n) (he : acts (1-P) a+acts P b=acts C (acts P a+acts (1-P) b)) : a=acts (blend P C) b := by
  let Q : Op n := 1-P; let S := reserve P C
  have h : IsStarProjection P := e ▸ cutM_idp s
  have ho := Porth h
  have hO : Q*P=0 := by unfold Q; rw [sub_mul,one_mul,h.isIdempotentElem,sub_self]
  have heP : cc P=P := by rw [e,cut_real];
  have hx : Pᵀ=P := by rw [e,self_t]
  have hy : Qᵀ=Q := by unfold Q; rw [Matrix.transpose_sub,hx,Matrix.transpose_one]
  have hyQ : cc Q=Q := by unfold Q; rw [cc_sub,cc_one,heP]
  have hS : S*C*P=P := by
    have ht := reserve_il h k; rw [body,heP] at ht
    rw [←mul_assoc,←mul_assoc,reserve_r h] at ht; exact ht
  have hA := congrArg (acts S) he
  have ht : S*Q=0 := by unfold Q; rw [mul_sub,mul_one, show S*P=S from reserve_r h,sub_self]
  change acts S (acts Q a+acts P b)=acts S (acts C (acts P a+acts Q b)) at hA
  rw [map_add,←act_mul,ht,act_zero,zero_add,←act_mul,show S*P=S from reserve_r h, ←act_mul, map_add,←act_mul,hS] at hA
  have h₁ : acts P a=acts (S+driftB P C) b := by
    rw [driftB]; change _=acts (S+ -(S*C*cc Q)) _; rw [hyQ,act_add,act_neg,act_mul (S*C),hA]; abel
  have hB := congrArg (acts Q) he
  change acts Q (acts Q a+acts P b)=acts Q (acts C (acts P a+acts Q b)) at hB
  rw [map_add, ←act_mul,←act_mul,show Q*Q=Q from h.one_sub.isIdempotentElem,hO, act_zero,add_zero, ←act_mul,h₁] at hB
  have h₂ : acts Q a=acts (-(driftB P C)ᵀ+weldB P C) b := by
    have hl : -(driftB P C)ᵀ=Q*C*S := by
      rw [driftB]; change -(-(S*C*cc Q))ᵀ=_
      rw [hyQ, Matrix.transpose_neg,neg_neg,Matrix.transpose_mul,Matrix.transpose_mul, hy,g, show Sᵀ= -S from reserve_skew h k g,neg_mul_neg,mul_assoc]
    have he : Q*C*((S+driftB P C)+Q)=Q*C*S+weldB P C := by
      rw [driftB]; change Q*C*(S+ -(S*C*cc Q)+Q)=Q*C*S+Q*(C-C*S*C)*cc Q
      rw [hyQ, mul_add,mul_add,mul_neg]; simp only [mul_assoc]; rw [sub_mul C (C * (S*C)),mul_sub Q]; simp only [mul_assoc]; abel
    rw [hB,hl,←he,act_mul (Q*C),act_add (S+driftB P C)]
  change a=acts ((S+_)-_+_) b; rw [sub_eq_add_neg,add_assoc,act_add, ←h₁, ←h₂]; unfold Q; rw [act_sub,act_one,add_sub_cancel]

def adjustK (f : n→FC n) (x : Wave n) (t : Finset n) : Ket n := WithLp.toLp 2 fun i=>(acts (f i) x).ofLp t
lemma paid {C : Op n} (g : Cᵀ= -C) (t : Finset n) : adjustK takeF (pairWave C) t=acts C (adjustK put (pairWave C) t) := by apply PiLp.ext; intro i; exact pull_rows g t i
lemma start_cut (s : Finset n) (x : Wave n) (t : Finset n) : adjustK takeF x t = acts (1-cutM s) (adjustK (fun i=> star (drift s i)) x t)+acts (cutM s) (adjustK (drift s) x t) := by
  apply PiLp.ext; intro i; rw [act_sub,act_one]; simp only [WithLp.ofLp_add,WithLp.ofLp_sub,Pi.add_apply,Pi.sub_apply,cut_apply, adjustK]
  by_cases h : i∈s <;> simp [h,drift,takeF]
lemma start_rim (s : Finset n) (x : Wave n) (t : Finset n) : adjustK put x t = acts (cutM s) (adjustK (fun i=> star (drift s i)) x t)+acts (1-cutM s) (adjustK (drift s) x t) := by
  apply PiLp.ext; intro i; rw [act_sub,act_one]; simp only [WithLp.ofLp_add,WithLp.ofLp_sub,Pi.add_apply,Pi.sub_apply,cut_apply,adjustK]
  by_cases h:i∈s <;> simp [h,drift,takeF]
lemma cash_pay {C : Op n} {s : Finset n} (g : Cᵀ= -C) (k : IsUnit (stage (cutM s) C)) (i : n) :
    acts (star (drift s i)) (pairWave C)=∑ j, blend (cutM s) C i j • acts (drift s j) (pairWave C) := by
  apply PiLp.ext; intro t
  have he := paid g t; rw [start_cut s,start_rim s] at he
  let x := pairWave C
  let a := adjustK (fun i=>star (drift s i)) x t; let b := adjustK (drift s) x t
  rw [WithLp.ofLp_sum,Finset.sum_apply]; change a.ofLp i=_; rw [slide_blend rfl k g a b he,act_at]; rfl
lemma laid {D : Op n} {x : Wave n} (h : ∀ i:n, acts (takeF i) x=acts (coupleRow D i) x) {q p : Wave n} (g:q=x-p) (k : ∀ i:n, acts (takeF i) p=acts (coupleRow D i) p) (u : q.ofLp ∅=0) : q=0 := by
  have he (i : n) : acts (takeF i) q=acts (coupleRow D i) q := by rw [g,map_sub,h,k,map_sub]
  apply PiLp.ext; intro i
  change q.ofLp i=0
  induction i using Finset.strongInductionOn with
  | _ i ih =>
    by_cases h : i.Nonempty
    · obtain ⟨j,H⟩ := h; let t := i.erase j
      have ht : t⊂ i := erase_ssubset H
      have hp := congrArg (fun x : Wave n => x.ofLp t) (he j); dsimp only at hp
      rw [take_row,if_neg (show j∉t from notMem_erase j i),show insert j t=i from insert_erase H,
        coupleRow,act_sum, WithLp.ofLp_sum,Finset.sum_apply,sum_eq_zero] at hp; swap
      · intro l _; rw [act_smul,WithLp.ofLp_smul,Pi.smul_apply,put_row]; by_cases k:l∈t
        · rw [if_pos k, ih _ (lt_of_le_of_lt (erase_subset ..) ht),mul_zero,smul_zero]
        rw [if_neg k,smul_zero]
      rw [← one_mul (q.ofLp i), ← parity_sq j t,mul_assoc,hp,mul_zero]
    rw [not_nonempty_iff_eq_empty.mp h,u]
lemma pair_only {D : Op n} {x : Wave n} (g : Dᵀ= -D) (h : ∀ i:n, acts (takeF i) x=acts (coupleRow D i) x) :
    x=x.ofLp ∅ • pairWave D := by
  let z := x.ofLp ∅ • pairWave D; apply sub_eq_zero.mp
  apply laid h rfl; intro i; rw [map_smul,map_smul,pull g]
  rw [WithLp.ofLp_sub,WithLp.ofLp_smul,Pi.sub_apply,Pi.smul_apply,paired_vac,smul_eq_mul,mul_one,sub_self]
lemma freeze (s : Finset n) {C : Op n} (g : Cᵀ= -C) (k : IsUnit (stage (cutM s) C)) :
    pairWave C=pf C s • acts (flake s).val (pairWave (blend (cutM s) C)) := by
  let x := pairWave C; let U := flake s; let V := star U; let y := acts V.val x
  let P := cutM s; let D := blend P C
  have he (i) : acts (takeF i) y=acts (coupleRow D i) y := by
    have hg := congrArg (acts V.val) (cash_pay g k i)
    rw [swivel V,show twist V _=takeF i from flake_flip_t s i] at hg -- tune
    unfold coupleRow; rw [act_sum]; simp_rw [act_smul]
    simp only [map_sum,map_smul,swivel V,show ∀ i, twist V (drift s i)=put i from flake_flip_p s] at hg
    exact hg
  have h : y.ofLp ∅=pf C s := by
    change (acts (star U.val) _).ofLp _=_; rw [←basis_inner, ←act_inner,star_star,show acts U.val (basisKet ∅)=basisKet s from flake_vac s,basis_inner]; rfl
  have hz : y=pf C s • pairWave D := by rw [←h]; exact pair_only (blend_skew (cutM_idp _) k g) he
  calc pairWave C=acts U.val y := (act_starUnit ..).symm
       _ = _ := by rw [hz,map_smul]
end YM.CF.Fock
