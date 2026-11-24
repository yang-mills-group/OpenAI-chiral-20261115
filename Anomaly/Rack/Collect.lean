import Anomaly.Rack.Patina
import YM.SU5.Exchange.Reg.Incidence
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour
variable {n:Side} {k m s l:ℕ} {d x:ℝ}
local notation "bφ" => (k:ℝ)

lemma place_here (p:1 ≤ k) (V:Aura n)(o : Seat n)(t : Seat n)(l:t ∈ V.val)(v:o ∈ V.val)(f:ℝ):
    tact f k V ≤ Real.exp ((-(((10*k:ℕ):ℝ)^2)⁻¹/2)* (separation o t : ℝ))*Real.exp 1 *tact (f+bφ⁻¹) k V := by
  let D:=widthK n k V
  have h:0≤D:=(by unfold D widthK; positivity)
  have hg:=Lattice.Corona.extent V.val k v l
  have hp:1≤ bφ:=by exact_mod_cast p
  have hx:0< bφ:=zero_lt_one.trans_le hp
  have hv : (separation o t:ℝ) ≤ D*(4*bφ+2)+2*bφ:=by unfold D widthK; exact_mod_cast hg
  change Real.exp (f*D)≤_*_*Real.exp ((f+bφ⁻¹)*D)
  simp only [Nat.cast_mul,Nat.cast_ofNat,← Real.exp_add]; apply Real.exp_monotone
  suffices H: ((10*bφ)^2)⁻¹/2*(separation o t:ℝ) ≤ 1 + bφ⁻¹*D by linarith
  calc
   _ ≤ ((10*bφ)^2)⁻¹/2*(D*(4*bφ+2)+2*bφ) := mul_le_mul_of_nonneg_left hv (by positivity)
   _ ≤ _ := by field_simp; nlinarith

-- pay actual pin supports (not multiplied by flag-choice entropy)
variable {I:Type}[DecidableEq I][Fintype I]

/-- `t` bounds multiplicity per site exactly; for example `Force_M`
spaced layouts are included. Spend 1/k of rate. -/
theorem tallyPins {V:I→ Aura n → ℝ}{σ:I→ Seat n}
    (h:∀ i:I, 0 ≤ V i)(e:∀ (i:I)(X:Aura n),σ i ∉ X.val → V i X=0)(t:ℕ)
    (p:∀ o:Seat n,(univ.filter fun j=>σ j=o).card ≤ t)
    (u:∀ i:I,voyageB (V i) k (x+bφ⁻¹) ≤ d)(z:0≤d)(g:1 ≤ k)(o : Seat n) :
    nook ((∑ i:I,V i)*tact x k) o ≤ taxIns (10*k) * (t:ℝ)*(Real.exp 1*d) := by
  let C (t:Seat n):=Real.exp ((-(((10*k:ℕ):ℝ)^2)⁻¹/2)* (separation o t:ℝ))
  have hv(i:I): ∑ j∈Cadre.spark o,V i j*tact x k j ≤ C (σ i)*(Real.exp 1*d):=by
    rw [←mul_assoc]
    apply le_trans _ (mul_le_mul_of_nonneg_left (u i) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)); unfold voyageB; rw [mul_sum]
    refine le_trans (sum_le_sum (g:=fun j=> C (σ i)*Real.exp 1*(V i j*tact (x+bφ⁻¹) k j)) (fun j w=> ?_)) (sum_le_sum_of_subset_of_nonneg (subset_univ (Cadre.spark o)) (fun j _ _=> mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (mul_nonneg (h i _) (Real.exp_pos _).le)))
    by_cases l:σ i∈ j.val
    · exact (mul_le_mul_of_nonneg_left (place_here g j o _ l (mem_filter.mp w).2 x) (h i j)).trans_eq (by unfold C; ring)
    rw [e i j l,zero_mul,zero_mul,mul_zero]
  unfold Cadre.nook; simp only [Pi.mul_apply,Finset.sum_apply,sum_mul]; rw [sum_comm]
  refine (sum_le_sum (fun i _=> hv i)).trans ?_
  rw [←sum_mul]; refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.exp_pos _).le z)
  rw [←Finset.sum_fiberwise_of_maps_to (s:=univ) (t:=(univ:Finset (Seat n))) (g:=σ) (fun i _=>mem_univ _)]
  apply le_trans (b := (∑ t:Seat n,C t)*(t:ℝ)); swap; · exact mul_le_mul_of_nonneg_right (placeExpense (10*k) (by omega) o) (by positivity)
  rw [sum_mul]; apply sum_le_sum; intro j _; let S:= univ.filter fun i:I=>σ i=j
  rw [Finset.sum_congr rfl (s₁:=S) (g:=fun i=> C j) (fun i w=>by rw [(mem_filter.mp w).2]),sum_const,nsmul_eq_mul,mul_comm (C j)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast p j) (Real.exp_pos _).le

lemma pinsFromLamp {I:Type} [LinearOrder I][Fintype I] {σ:I→Seat n} (p:lamp_B s k m σ) (x:Seat n) :
    (univ.filter (fun j=>σ j=x)).card ≤ m := by
  apply le_trans ?_ (p x); apply card_le_card; intro i u; refine mem_filter.mpr ⟨mem_univ _,?_⟩
  rw [(mem_filter.mp u).2, separation_self]; omega

end YM.CF.Vow.TreasuryFog
