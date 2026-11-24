import YM.CF.Feu.Ash
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Feu
open Nor
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
-- L ar.Positive. factor chosen before exposure and h κ. Coin momentum knob effect.Certified
abbrev dipK (s k:ℕ)(a v d:ℝ):ℝ:= 2*Real.exp (a*(Yaw.χ s:ℝ))*lip k*d*(population*v)
abbrev sliceK(P:Side)(s k:ℕ)(a v d:ℝ):ℝ := (1+abs (dipK s k a v d))*followV [] P
lemma healthY (a d ν:ℝ)(s k:ℕ)(P:Side)(E:Stake.Isle): (0< sliceK P s k a ν d) ∧∀ᶠ H:ℝ in atTop,Coin_ (d*H) (population*(ν*followV [] P)) (population*E.r1) a s k ≤ sliceK P s k a ν d * H:=by
 let S:= sliceK P s k a ν d; let t:= followV [] P; have hx:0<t:= Vpos ..; let v:= dipK s k a ν d; have hb:0 < S:=mul_pos (by positivity) hx; refine ⟨hb,?_⟩; have hu:0< S-v*t:= sub_pos.mpr (mul_lt_mul_of_pos_right (by linarith [le_abs_self v] : v< 1+|v|) hx)
 let C₀:= 1+4*(Real.exp (a*(Yaw.χ s:ℝ))*lip k*(population*E.r1)+1); filter_upwards [eventually_ge_atTop (C₀/(S-v*t))] with x h; have hg: Coin_ (d*x) (population*(ν*followV [] P)) (population*E.r1) a s k=C₀ +(v*t)*x:=by unfold v t C₀ Coin_ dipK; ring
 rw [hg]; change _ ≤ S*x; linarith only [(div_le_iff₀ hu).mp h]
lemma shareK (s k:ℕ)(a ν d:ℝ):∃ C:ℝ,1 ≤ C∧∀ R: Patch,(sliceK R.L s k a ν d)^4 = C*(R.L.val:ℝ)⁻¹^6:=by
 let S:=1+abs (dipK s k a ν d); have hs:1≤ S:=le_add_of_nonneg_right (abs_nonneg _); refine ⟨S^4,one_le_pow₀ hs,fun P=>?_⟩
 unfold sliceK followV; rw [mul_pow,div_pow]; let t:ℝ:=P.L.val; have hp:0<t:=by unfold t; positivity
 change S^4*(Real.sqrt t^4/(t^2)^4)=_
 have hh:(Real.sqrt t)^4=t^2:=by rw [show (4:ℕ)=2*2 from by decide,pow_mul,Real.sq_sqrt hp.le]
 rw [hh]; change _=S^4*t⁻¹^6; field_simp <;> ring
end YM.CF.Feu
