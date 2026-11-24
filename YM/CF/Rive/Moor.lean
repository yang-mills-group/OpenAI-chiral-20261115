import YM.CF.Rive.Wally
import YM.CF.Rive.Boil
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Rive
open Mew Ione
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
open Vow Larch Rue Push.AbsoluteSums Trees Ursell
-- two readings; sum-bound tail with varying witnesses at fixed price
open Bake Gas Palot
variable {J:Type}[Fintype J][LinearOrder J](K:Mew.Key J→ Cusp n)(L:Aura n→Support (More n)→Orbit n→Cipher n)(pT:∀ i∈hill J,Turf (fun X=> K i X ∅))
variable {γ δ q q' γ' L₁ L₂ κ :ℝ}(A:Mew.Key J→ Aura n→ℝ)(U:Mew.Key J→ Aura n→ Support (More n)→ℝ)(Bv:Aura n→ℝ)
local notation "θ"=> P.supportExponent+1+1
local notation "YO"=> fun i:Key J=>fun X:Aura n=> K i X ∅
variable (H:∀ i∈hill J,Ready Palot.stern P.B (A i) (P.supportExponent+1+1) γ δ q)(p:∀ i∈hill J,∀ x,Medal P x.val ∅ (K i x ∅) h (A i x))(u:∀ i∈hill J,ArmsK P (K i) (U i) h)(hw:1 ≤ h)
variable (l:Anuk (n:=n) L Bv P h)(h₁:∀ i:Seat n,tallB Bv P.B (P.supportExponent+1+1) i ≤ L₁)(h₂:∀ i∈hill J,∀ v:Seat n,tallB (Vow.hymn (U i)) P.B (P.supportExponent+1+1) v ≤ L₂)
local notation "W'"=> (γ*q^0*(1-q)⁻¹)
variable (hC:1≤κ)(et:L₁+γ*q^0*(1-q)⁻¹ ≤1)(qV: degreePrice P.B γ' 1 ≤q') (qH:q'< 1)(ph:0< γ')(hpS:κ*L₂+Real.exp 1*(γ*q^0*(1-q)⁻¹+L₁) ≤γ')
local notation "μ"=>P.supportExponent+(1:ℝ)/2
local notation "P'" x=> (roomV P (fun i=>K x i ∅) (K x) L)
local notation "VQ" x=> FeeD P (fun i=>K x i ∅)
variable (T0:Ids n)
abbrev hint_E (p:BudgetPoint)(K:Mew.Key J→ Cusp n)(T0:Ids n)(i:Key J):=cast_E (FeeD p (fun x=>K i x ∅)-FeeD p (fun x=>K 0 x ∅)) T0
include H p u hw l h₁ h₂ et qV qH ph hpS hC pT
lemma echo_B(i)(hc:i∈hill J) : ForgeB (hint_E P K T0 i) (filmK P (μ)) P h (fun _=>reserveT P.power P.order P.B (3/2:ℝ)*(W'+ W')) ∧ SanB (budgetR (P' i)) (giftK P (μ)) P h (fun _=> reserveT P.power P.order P.B (1/2:ℝ)*(κ⁻¹*(γ'*q'^0*(1-q')⁻¹))):=by
 have hp:0 ≤ P.supportExponent+1:= by linarith [P.exponent_pos]
 have hf: μ+(1/2:ℝ)=P.supportExponent+1:=by linarith
 have ht:μ+(3/2:ℝ)= (θ):=by linarith
 have hx: 0≤ (θ):=by linarith
 have hz(i:Aura n):Bv i+γ*q^0*(1-q)⁻¹ ≤1:=by refine le_trans (add_le_add_left ?_ _) et; obtain ⟨j,hj⟩:=i.property; apply le_trans _ (h₁ j); exact (le_mul_of_one_le_right (l.1 i) (Real.one_le_exp (mul_nonneg hx (by exact Nat.cast_nonneg (coverNumber P.B i.val))))).trans (single_le_sum (s:=Finset.univ.filter (fun i:Aura n=>j∈i.val)) (f:=fun i=>Bv i * Trees.currency P.B (θ) i.val) (fun i _=>mul_nonneg (l.1 i) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,hj⟩))
 obtain ⟨c,w⟩:= rent_x (u i hc) l.2 l.1 (H i hc) hp (p i hc) zero_lt_one hw hC hz h₁ (h₂ i hc) qV qH ph hpS
 have hu(j t x):=glenP x hw (p j t) (H j t) hx 0
 let V1(v:Key J):=VQ v; let U1(v) := fun x:Aura n=>spanD x (A v) 0
 have hh(j t):Turf (V1 j):= turfK _ (pT j t)
 refine ⟨quoteE (U1 i+U1 0) (V1 i-V1 0) (fun x=>by rw [Pi.sub_apply,sub_eq_add_neg]; exact (hu _ hc _).plus (hu 0 roots x).negT) (fun x v t=>congrArg₂ (·-·) (hh i hc x v t) (hh _ roots x v t)) T0 (fun x=>by rw [ht,Larch.tall_add]; exact add_le_add (thinX (H i hc) hx x 0) (thinX (H _ roots) hx x 0)) (zero_le_one.trans hw) (by norm_num), quoteK _ _ c (fun i=>?_ ) (zero_le_one.trans hw) (by norm_num)⟩; rw [hf]; exact (le_inv_mul_iff₀ (zero_lt_one.trans_le hC)).2 (w _)
omit u hw l h₁ h₂ et qV qH ph hpS hC -- no unused
open Lilt
variable (U0:RegBudget n)(Δ:Pane n→ℝ)(gA:∀ i:Orbit n,FleetS P.threshold i.1→coldE P (FeeD P (fun X=>K 0 X ∅)) i= Larch.owed_E n (Δ i.1)+exponentL P U0 i.1 + fuelV P L i) -- tune namespace
include gA hw
lemma sole_U(u:Key J)(pu:u∈hill J)(V:Orbit n)(p:FleetS P.threshold V.1): hGas (flags P.threshold V.1) (keyL P (K u) (fun X=>K u X ∅) V)= Real.exp (Δ V.1) • (exp (exponentL P (U0+ hint_E P K T0 u) V.1)*fueled P (budgetR (roomV P (fun i=>K u i ∅) (K u) L)) V):=by
 rename_i r₀ -- tune shadow hp explicit
 let T:=FeeD P (fun X=>K u X ∅); let T':= FeeD P (fun X=> K 0 X ∅); let a:=T-T'; have hu:= pT u pu; have he: exponentL P (hint_E P K T0 u) V.1=coldE P a V:=Ione.ocean _ a _ (fun i x j=> congrArg₂ (·-·) (turfK _ hu i x j) (turfK _ (pT _ roots) i x j)) _
 let x:=Δ V.1; let V':=exponentL P (U0+ hint_E P K T0 u) V.1; have hh:coldE P a V=coldE P T V-coldE P T' V:=by unfold coldE a; simp_rw [Pi.sub_apply,sum_sub_distrib]
 have ht: owed_E n x+V' + fuelV P L V=coldE P T V:=by unfold V'; rw [ripe_H,he,hh,gA V p]; abel
 have hp:0≤ P.supportExponent+1:=by linarith [P.exponent_pos]
 rw [asterT (H u pu) hp (r₀ u pu) zero_lt_one hw V p _ ht]; letI :NormedAlgebra ℚ (Cipher n):=NormedAlgebra.restrictScalars ℚ ℝ (Cipher n); rw [exp_add]; change exp (owed_E n x)* exp _* _= Real.exp x • _; rw [owed_E, ←thim_v, ←Iva.yeaH, ←Complex.ofReal_exp, thim_v]; unfold Lilt.thim; rw [smul_mul_assoc,one_mul,smul_mul_assoc] -- tune
end YM.CF.Rive
