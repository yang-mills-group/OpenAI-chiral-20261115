import GaugeFieldConstruction.Ileon
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry
variable {n:Side} {α β I J:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype J]
namespace Grotto
variable (σ:I→ Seat n){S:α→ Support (More n)} {z:β→Force n}
variable (Γ:J→ Grotto I S z)(r:J→ℝ)(V:α→ℝ)(U:β→ℝ)
def verr:=∑ j:J with (Γ j).needs>0,exp_R σ (Γ j) (r j) V
def blerr:=∑ j:J with (Γ j).needs=0,exp_R σ (Γ j) (r j) V
def flair:=∑ j:J,exp_Y σ (Γ j) (r j) V U
def white:=∑ j:J with (Γ j).needs=0,Rinc σ (Γ j)
def gray:=∑ j:J with (Γ j).needs>0,Rinc σ (Γ j)
def fullY:=∑ j:J,Kinc σ (Γ j)
-- orientation etc.Atlas keeps record of these terms.
variable (o y:Seat n){Ω a η:ℝ}{b:ℕ}{L:List (Site (More n))}(p:∀ j,(Γ j).anchor.val.1=o)
local notation "Θ"=> Summit b a
local notation "PZ"=>RedB b a η L
local notation "ΩΠ"=>ColdB b a η L
local notation "Δπ"=>respite b (a+2*ζd) η L (plateI z) U o y
local notation "Γπ"=>respite b (a+6*ζd) η L S V o y
local notation "gπ"=> Cube_M b* Ω
local notation "Mπ"=> windPulse b o y
variable (u:0≤V)(v:0≤U)(l:Scales b a η L)(HP : ∀ y:Site (More n),postG S V (RedB b a η L) y≤ Ω)(HV:∀ y:Site (More n),postG (plateI z) U (ColdB b a η L) y≤ Ω)(t:Cube_M b*Ω≤1)(g:0≤Ω)(ℓ:ℝ)(c: (∑ j:J,r j * Summit b a (Γ j).anchor.val.2) ≤ ℓ) (y0:∀ j,0 ≤r j)
include u p l c y0
lemma whitePay : pointX cloudP (blerr σ Γ r V) PZ y≤ℓ*Mπ :=by
 unfold blerr; rw [pointX_sum]; apply le_trans _ (mul_le_mul_of_nonneg_right c (pulse_pos _ _ _|>.le)); rw [sum_mul]
 refine (sum_le_sum (g:=fun j=> r j* Θ (Γ j).anchor.val.2*Mπ) fun i t=> ?_).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>mul_nonneg (mul_nonneg (y0 i) (Real.exp_pos _).le) (Real.exp_pos _).le))
 rw[←p i]; exact (Γ i).XP_white σ _ y V (y0 _) u l (mem_filter.mp t).2 -- order
include HP HV t g v
lemma grayPay : pointX cloudP (verr σ Γ r V) PZ y+pointX cloudK (flair σ Γ r V U) ΩΠ y≤ℓ*(2*Mπ*gπ+4*η⁻¹*(Δπ+Γπ)) :=by
 unfold verr flair; rw[pointX_sum,pointX_sum,sum_filter,←sum_add_distrib]
 apply le_trans _ (mul_le_mul_of_nonneg_right c (show 0≤ 2*Mπ*gπ+4*η⁻¹*(Δπ+Γπ) from add_nonneg (mul_nonneg (mul_nonneg zero_le_two (pulse_pos ..|>.le)) (mul_nonneg (cube_M_pos ..|>.le) g)) (mul_nonneg (by have t:= l.pos; positivity) (add_nonneg (respite_0 _ _ (fun i=>v i) _ _ _ _ _ _ l.pos.le) (respite_0 _ _ (fun i=>u i) _ _ _ _ _ _ l.pos.le)))))
 rw[sum_mul]; apply sum_le_sum; intro i _; have h:= (Γ i).fiscal_gray σ (r i) y V U (y0 _) u v l HP HV t g
 simp only[p] at h; change pointX cloudP (if _ then _ else _) _ _+_ ≤ _ at h; split_ifs at h ⊢ with ht ht' -- tune
 · exact h
 rw[pointX_0] at h; exact h
variable (P:BudgetPoint)(h q:ℝ)(k:ℕ)(sq:0<q)(hq:∀ i,Pits σ (Γ i) (r i) V U P q h k)
omit HP HV g p c y0 l t
include hq sq
lemma hour : BillX P σ h q (blerr σ Γ r V) (white σ Γ) ∧ BillX P σ h q (verr σ Γ r V) (gray σ Γ) ∧ BillF P σ h q k (flair σ Γ r V U) (fullY σ Γ):=by
 have hp(i:J):= (hq i).lease.ready _ _ _ _ (hq _).clarity u sq; have ht(i:J):= (hq i).packs.ready _ _ _ _ _ u v (hq _).clarity
 exact ⟨ReefX.registry_sum σ (fun i:Hub n=>i.val.2) (T:=PitR P h q) ReefxR _ (fun j=> Rinc σ (Γ j)) (fun j=>exp_R σ (Γ j) (r j) V) (fun i _=>hp i),ReefX.registry_sum σ (fun i:Hub n=>i.val.2) (T:=PitR P h q) ReefxR _ (fun j=> Rinc σ (Γ j)) (fun j=>exp_R σ (Γ j) (r j) V) (fun i _=>hp i),ReefX.registry_sum σ (fun i:Force n=>i.val.1.val.2) (T:=PitF P h q k) (ReefxF k) _ (fun j=> Kinc σ (Γ j)) (fun j=> exp_Y σ (Γ j) (r j) V U) (fun i _=>ht i)⟩
#print axioms hour
#print axioms grayPay
end Grotto
end YM.CF.Scree.Ing
end
