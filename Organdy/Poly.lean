import Organdy.Dune
import YM.SU5.Exchange.Reg.Incidence
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Sault Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive Vow.TreasuryFog Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]


variable {m:ℕ}
def polySight (B m:ℕ):ℝ:=(Real.exp 1*m*taxIns (4*B))
local notation "xB" => p.B
lemma sight (x:Seat n) (o:Seat n)(i:Aura n)(w:x∈i.val)(e:o∈i.val):
    tact (highPace p) p.B i ≤
    Real.exp 1 * Real.exp (-(((4*xB:ℕ):ℝ)^2)⁻¹/2*separation x o) *
    tact (p.supportExponent+8*biscuit p) p.B i:=by
  let j:Scree.Hub n:=⟨⟨o,i.val⟩,e⟩
  have ht:=inSeat p x j w
  let k:ℝ:=widthK n xB i
  let s:ℝ:=separation x o
  let h:=p.supportExponent; let b:ℝ:=xB
  let t:ℝ:=b⁻¹; let y:= -(b^2)⁻¹/2
  change h *k+10/b*k≤ y*s+1+(h+20/b)*k at ht
  have hx:-t*k ≤ (y*s+1)/10:=by
    rw [div_eq_mul_inv (10:ℝ),div_eq_mul_inv (20:ℝ)] at ht
    unfold t; linarith
  have hh : -(((4*xB:ℕ):ℝ)^2)⁻¹/2=y/16:=by
    push_cast
    unfold y b
    rw [mul_pow,mul_inv]
    ring
  have hp:y*s≤0:=mul_nonpos_of_nonpos_of_nonneg
       (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity))
       (Nat.cast_nonneg _)
  rw [Sour.tact,Sour.tact,←Real.exp_add,←Real.exp_add,Real.exp_le_exp,hh]
  change (h+7*t)*k≤1+y/16*s+(h+8*t)*k
  linarith

/-- Membership rate 1+7/b for the gas on a sparse layout with at most m labels
per seat; shift per-root launch accounts (already after the two knocks). -/
lemma dredge (A: I→Aura n→ℝ)(w:∀ j:I,0≤A j)
    (z:∀ j:I,voyageB (A j) p.B (p.supportExponent+8*biscuit p) ≤ c)
    (v:0≤c)
    (σ:I→Seat n)(t:∀ i:I,∀ X:Aura n,σ i∉ X.val → A i X = 0)
    (r:∀ x:Seat n, (univ.filter fun j=>σ j=x).card ≤ m)
    (x:Seat n):
    tallB (∑ j:I,A j) p.B (highPace p) x ≤ polySight p.B m * c:=by
  let l:=p.supportExponent+8*biscuit p
  let d:=fun o:Seat n=> Real.exp (-(((4*xB:ℕ):ℝ)^2)⁻¹/2*separation x o)
  have e(j:I):
      tallB (A j) p.B (highPace p) x ≤ Real.exp 1*d (σ j)*c:=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (z j)
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    unfold voyageB; rw [mul_sum]
    change (∑ i∈spark x, A j i* tact (highPace p) p.B i) ≤_
    unfold Cadre.spark
    rw [sum_filter]
    refine sum_le_sum fun i _=>?_
    split
    · rename_i h
      rw [mul_left_comm _ (A j i)]
      by_cases u:σ j ∈i.val
      · exact mul_le_mul_of_nonneg_left (sight x (σ j) i h u) (w j i)
      rw [t _ _ u,zero_mul,zero_mul]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (mul_nonneg (w j i) (Real.exp_pos _).le)
  have hsum : (∑ j, d (σ j)) ≤ m*taxIns (4*p.B):=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (placeExpense (4*p.B) (by
      have hv:=p.B_pos; omega) x) (Nat.cast_nonneg m))
    rw [←sum_fiberwise_of_maps_to (t:=univ) (g:=σ) (fun _ _=>mem_univ _),mul_sum]
    refine sum_le_sum fun i _=>?_
    rw [sum_congr rfl (g:=fun _=>d i) (fun j v=> by rw [(mem_filter.mp v).2]),
      sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (r _)) (Real.exp_pos _).le
  unfold tallB
  simp_rw [Finset.sum_apply,sum_mul]
  rw [sum_comm]
  apply le_trans (sum_le_sum (fun j (_:j∈univ)=> e j))
  rw [←sum_mul,←mul_sum,polySight, mul_assoc (Real.exp 1) (m:ℝ)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le) v

variable (σ:I→ Seat n)
local notation "sun" => p.supportExponent+8*biscuit p
abbrev breeze (σ:I→Seat n)(m:ℕ) :Prop:=∀ x:Seat n, (univ.filter fun j=>σ j=x).card ≤ m
lemma receipt {V:I→Bag n} {B:I→ Support (More n)}
    (r:breeze σ m)(j:∀ i, σ i∈ B i)
    (u:∀ i:I, Barrage p q (B i) h (V i) sun a b)
    (va:0≤a)(vb:0≤b):
    ∃ f g: I→Aura n→ℝ,Pollen p q h σ V f g ∧
      (∀ x,tallB (∑ i:I, f i) p.B (highPace p) x ≤ polySight p.B m*a) ∧
      (∀ x,tallB (∑ i:I, g i) p.B (highPace p) x ≤ polySight p.B m*b):=by
   choose f g fare far take give using (fun i=>(u i).price)
   refine ⟨f,g,⟨fare,fun i X o=>(far i X (fun z=>o (z (j i)))).1⟩,
    dredge f (fun i X=>(fare i X).tube.price) take va σ (fun i X o=>(far i X
      (fun z=>o (z (j i)))).2.1) r,
    dredge g (fun i X=>voucher (fare i X)) give vb σ (fun i X o=>(far i X
      (fun z=>o (z (j i)))).2.2) r⟩

end YM.CF.Organdy
