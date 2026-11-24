import SatinStress.Internal.RealColor
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import YM.CF.Fock.PfMinor
/-!
# determinant-line invariance of the true generation action

For a representation on the one-particle space extending to SL on
generations and commuting with the one-particle star projection, its
`quant` action on this Sea line is the identity. We'll use this for the
actual Sea of the project (Color/copies coupled to same x) as required in
R4. It's cheap to show even for arbitrarily large dimension of the one-
particle projector, without knowing its rank: apply `line_quant_comm` and
show that the resulting line action is trivial. For the latter adapt the SL2
simplicity proof idea in Mathlib `Matrix.SpecialLinearGroup`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.SatinStressData
open SU Gauge Matrix Fock Finset Function
open scoped Matrix Kronecker Topology BigOperators InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
abbrev SL3 := Matrix.SpecialLinearGroup Age ℂ

section Character
variable (chi : SL3 →* ℂ)

private lemma un (A : SL3) : chi A ≠ 0 := by
  intro h; have e : (1:ℂ)=0:=by rw [← map_one chi,← mul_inv_cancel A,map_mul,h,zero_mul]
  exact one_ne_zero e
open SpecialLinearGroup (diag2n diag2n_coe)
local notation "beam" => Matrix.SpecialLinearGroup.transvection
private lemma lit {i j : Age} (p : i ≠ j) (c : ℂ) : chi (beam p c) = 1 := by
  let D := diag2n p (2:ℂ) (by norm_num)
  let y : ℂ := c / 3
  have he : D * beam p y = (beam p (c+y))*D := by
    apply Subtype.ext; change (D.val : Op Age)*(1+single i j y)=(1+single i j (c+y))*D.val
    rw [mul_add,add_mul,mul_one,one_mul]
    congr 1
    dsimp only [D,diag2n]; ext a b
    by_cases hA : a = i <;> by_cases hB : b=j
    · simp [mul_diagonal,hA,hB,Ne.symm p,y]; ring
    all_goals simp [mul_diagonal,single_apply, hA,hB, eq_comm] ; grind
  have hv := congr_arg chi he
  rw [SpecialLinearGroup.transvection_add] at hv; simp only [map_mul, mul_assoc] at hv
  exact mul_right_cancel₀ (mul_ne_zero (un chi _) (un chi _)) (hv.symm.trans (by rw [one_mul,mul_comm]))

private lemma form {i j : Age} (p : i≠j) (c : ℂ) (h : c≠0) :
    diag2n p c h = beam p c * beam p.symm (-c⁻¹) * beam p c * beam p (-1) * beam p.symm 1 * beam p (-1) := by
  apply Subtype.ext; ext a b
  -- expand product, simplifying elementary column operations.
  change (diagonal _) a b = (Matrix.transvection i j c * Matrix.transvection j i (-c⁻¹) *
       Matrix.transvection i j c * Matrix.transvection i j (-1:ℂ)*Matrix.transvection j i (1:ℂ)*Matrix.transvection i j (-1:ℂ)) a b
  by_cases hx:b=i; swap
  · by_cases hy:b=j; swap
    · -- all other columns unchanged
      simp only [mul_transvection_apply_of_ne _ _ _ _ hx, mul_transvection_apply_of_ne _ _ _ _ hy]
      by_cases h':a=b
      · subst a; simp [hy,hx,Matrix.transvection,Ne.symm hy]
      simp [h',Matrix.transvection,Ne.symm,hy]
    subst b
    simp only [mul_transvection_apply_of_ne _ _ _ _ p, mul_transvection_apply_of_ne _ _ _ _ p.symm, mul_transvection_apply_same]
    by_cases ha:a=i
    · subst a; simp [Matrix.transvection,p, Ne.symm p,h] -- tune
    by_cases hb:a=j
    · subst a; simp [Matrix.transvection,p,Ne.symm p,h]
    simp [Matrix.transvection,hb,ha,Ne.symm ha]
  subst b
  simp only [mul_transvection_apply_of_ne _ _ _ _ p, mul_transvection_apply_of_ne _ _ _ _ p.symm, mul_transvection_apply_same]
  by_cases ha:a=i
  · subst a; simp [Matrix.transvection,p,Ne.symm p,h]
  by_cases hb:a=j
  · subst a; simp [Matrix.transvection,p,Ne.symm p,h]
  simp [Matrix.transvection,ha,hb,Ne.symm ha]

lemma settles (A : SL3) : chi A = 1 := Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun z : SL3 => chi z=1) A
  (fun _ _ p {a} h=> by -- v binder implicit a? tune
    rw [form p _ h]; simp only [map_mul,lit chi,one_mul])
  (fun _ _ p => lit chi p)
  (fun x y h1 h2 => (map_mul chi x y).trans (by rw [h1,h2]; simp))
end Character

-- determinant phase trivially settled on SL. No conjugation conventions here.
section Wave
variable {I : Type*} [LinearOrder I] [Fintype I] (B : Op I) (h : IsStarProjection B)
  (X : Wave I) (t : Sea B X) (R : SL3 →* Op I) (p : ∀ x : SL3, Commute B (R x))
include h t p
private lemma quantized (U : SL3) : acts (quant (R U)) X=inner ℂ X (acts (quant (R U)) X) • X := by
  rw [← Sea.scalar h t]
  nth_rw 1 [← t.1]; rw [← act_mul,line_quant_comm (p _).symm.eq, act_mul]
theorem fixedSea (g : SL3) : acts (quant (R g)) X=X := by
  let f (g : SL3) := inner ℂ X (acts (quant (R g)) X)
  have he g : acts (quant (R g)) X = f g • X := quantized B h X t R p g
  have hx : X≠0 := norm_pos_iff.mp (t.2.symm ▸ zero_lt_one) -- tune
  let r : SL3 →* ℂ :=
    { toFun := f
      map_one' := by apply smul_left_injective ℂ hx; dsimp only; rw [← he,map_one,quant_one,act_one,one_smul]
      map_mul' := fun x y => by apply smul_left_injective ℂ hx; dsimp only; rw [← he,map_mul,quant_mul,act_mul,he y,map_smul,mul_comm,mul_smul,he x] }
  exact (he g).trans (by rw [show f g = 1 from settles r g,one_smul])
end Wave
end YM.CF.SatinStressData
