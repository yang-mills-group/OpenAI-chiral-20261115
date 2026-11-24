import Anomaly.Rack.TailPrice
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor
variable {n:Side} {q:ℕ} {b:BudgetPoint} {δ ca d h G U:ℝ}

-- ℓ for inputs at P.exponent budget.
def thresholdOcclus (v:ThresholdPool b.B δ ca G d U): Occlus b :=
 {uΓ:= b.supportExponent+5*δ, w:=δ, η:=δ, κ:=1, c:=|ca|, d:=δ⁻¹ * spanV b.B * |ca|, γ:=U, e:=|d|, degree0:=v.rank.2, degree:=v.rank.1,
  still:=v.dollars, covers:=v.cover, hγ:=v.κval, hη:=v.roof_limit.1, hw:=by ring_nf; linarith}

local notation "off" => b.supportExponent
local notation "Vϵ" => widthK n b.B
local notation "b_" => spanV b.B
local notation "Γ" => b.supportExponent+5*δ
local notation "Lux" => loom_v (b.supportExponent+5*δ) δ (widthK n b.B) 0

-- Event budget consumption for single stroke + any number of spreads. Uses project structural hypotheses on old K pay.
variable {r:Cadre.Tape (A:=Seat n)}{F K: Aura n→ℝ}(v:ThresholdPool b.B δ ca G d U)
theorem thresholdTimer (f:∀ X,F X≥0)(y:∀ X,K X≥0)
    (w:∀ o:Seat n,nook (F*tact (b.supportExponent+7*δ) b.B) o ≤ |ca|)
    (D:∀ o:Seat n,nook (K*tact Γ b.B) o ≤ |d|)
    (e:∀ X:Aura n,∀ D⊆ X.val,0≤ r X D)
    (g:∀ o:Seat n,tallB (Cadre.roofL r 1) b.B (b.supportExponent+1/2) o ≤ G) :
    let C:=thresholdOcclus v
    Timer (uChip F K r) F C.κ C.uΓ C.w Vϵ b_ C.γ C.c C.d C.e 1 K := by
  intro C; let z:= uChip F K r
  let W:= tact (b.supportExponent+7*δ) (n:=n) b.B
  let w0:=tact (b.supportExponent+6*δ) (n:=n) b.B; let F0:= Cadre.fog Lux F U; let B':=b_; have ht:=vigor n b.B; have h0:0≤ b_ := Nat.cast_nonneg _
  have hF(X:Aura n): 0≤F0 X:= mul_nonneg (mul_nonneg (f X) (Real.exp_pos _).le) (Real.exp_pos _).le
  have hδ:= v.roof_limit.1; have h1:=v.κval
  have hV(X:Aura n): F0 X ≤ F X * w0 X:=by
    unfold F0 Cadre.fog waveL; simp only [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (f X)
    unfold loom_v w0 Sour.tact; rw [←Real.exp_add, mul_zero,sub_zero]; apply Real.exp_monotone
    have he:=mul_le_mul_of_nonneg_right (ht.rate X) h1.le; have hl:=mul_le_mul_of_nonneg_right v.fog (zero_le_one.trans (ht.pos X)); linarith only [he,hl]
  refine uGears _ _ _ f y e _ _ _ _ _ _ _ _ _ ht ?tight ?win (fun o=>?_) le_rfl h0 hδ.le h1.le v.price (abs_nonneg _) ?boot v.void ?_
  case tight => exact fun i=> (sum_le_sum (s:=spark i) (fun X _=> (hV X).trans (mul_le_mul_of_nonneg_left (show w0 X ≤ W X from tact_para (by linarith only [hδ]) _) (f X)))).trans (w i)
  case win =>
    intro i
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (w i) (mul_nonneg (inv_nonneg.mpr hδ.le) h0))
    unfold nook shelfR; rw [mul_sum]; apply sum_le_sum; intro X _
    change F0 X*(X.val.card:ℝ) ≤ (δ⁻¹*b_)*(F X*W X)
    have hv : w0 X*(X.val.card:ℝ) ≤ (b_*δ⁻¹)*W X:= (mul_comm ..).le.trans ((shelf_pay (n:=n) (k:=b.B) (s:=off+6*δ) hδ X).trans_eq ?_)
    · exact (mul_le_mul_of_nonneg_right (hV X) (Nat.cast_nonneg _)).trans ((mul_assoc ..).le.trans ((mul_le_mul_of_nonneg_left hv (f X)).trans_eq (by ring)))
    rw [show off+6*δ+δ=off+7*δ by ring]
  case boot=> change 0≤ off+5*δ-δ*1; linarith only [hδ,b.exponent_pos]
  · change nook (K*Lux) _ ≤ |d|
    simp_rw [show Lux=Sour.tact Γ b.B from funext fun j=>by unfold loom_v Sour.tact; rw [mul_zero,sub_zero]]
    exact D o
  intro i
  rw [←Sour.parse]; -- perhaps aims C.uΓ-C.w*0
  change tallB (roofL r 1) b.B (Γ - δ*0) i < U
  have he : 0 ≤ roofL r 1 := fun X=> sum_nonneg fun D v => mul_nonneg (zero_le_one.trans (Cadre.duty_i _ le_rfl)) (e _ _ (mem_powerset.mp v))
  refine lt_of_le_of_lt (Larch.tall_m (roofL r 1) he ?_ _|>.trans (g i)) ((le_abs_self _).trans_lt v.start); linarith only [v.roof_limit.2]
end YM.CF.Vow.TreasuryFog
