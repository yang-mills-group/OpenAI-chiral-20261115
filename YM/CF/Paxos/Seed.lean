import YM.CF.Paxos.Heron
import YM.CF.Bloom.Sequence
set_option autoImplicit false

set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Beau Haro Ione Salt
set_option maxHeartbeats 1000000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)(M:Side)(ht:T.q ≤ M.val)(l0:ℕ)(k₀:ℕ)
variable (B0:ℕ→ℝ)(D:Due V a p i N0 T M ht l0 B0)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)
local notation "Xc"=> cell M B R.L
local notation "Lr"=>dleaf R.L
local notation "Fh"=> hueR V a p i N0 T M ht l0 B0
local notation "μh"=> hat R.L x
variable (R0 E C δ:ℝ→ℝ){wα:ℝ}(y:ℝ)(D':Heron V a p i N0 k₀ J q h wα R0 E C δ y)(hy:y ≤ x)
abbrev StarPS(n:ℕ):= Moen.Space.rangeB (Fin n → ℝ × Haro.SpaceM) 1
local notation "S'"=> StarPS l0
abbrev ν_PS (L:Side):= Vale.billX L/4
local notation "e0"=> ν_PS R.L
variable {l0}
def ra_C (L:Side)(v: StarPS l0)(k:ℕ):ℝ:= if h:k<l0 then ν_PS L*(v.val ⟨k,h⟩).1 else 0
local notation "ρ'"=> ra_C (l0:=l0) R.L
lemma credit_z (L:Side)(v:StarPS l0)(i:ℕ):|ra_C L v i|≤ν_PS L:=by
 have hp:0 ≤ ν_PS L:=by unfold ν_PS; linarith [pitch L]
 unfold ra_C; split; swap; · simpa using hp
 next h=> let j:Fin l0:=⟨i,h⟩; rw [abs_mul,abs_of_nonneg hp]; refine (mul_le_mul_of_nonneg_left ?_ hp).trans (mul_one _|>.le); change ‖(v.val j).1‖ ≤ 1; exact (norm_fst_le _).trans ((norm_le_pi_norm _ _).trans v.property) -- name?
lemma ra_c (L:Side)(j:ℕ):Continuous (fun z:StarPS l0=>ra_C L z j):=by unfold ra_C; split; exact continuous_const.mul (continuous_fst.comp ((continuous_apply _).comp continuous_subtype_val)); exact continuous_const
section
include V
lemma billx_T :0 < ν_PS R.L:=by
 have hx:1<R.L.val:=by have hp:= V.tallX; omega
 unfold ν_PS; exact div_pos (mul_pos (Gauge.slopeConstant_pos yet_one) (Real.log_pos (by exact_mod_cast hx))) (by norm_num)
end
def θ_guess (Z:ℕ→ℝ)(H:∀ i,0 ≤ Z i)(j:ℕ)(v:StarPS l0): Haro.ΘS (Z j):=
 if h:j< l0 then ⟨Z j • (v.val ⟨j,h⟩).2,by rw [norm_smul,Real.norm_of_nonneg (H j)]; exact (mul_le_mul_of_nonneg_left ((norm_snd_le _).trans ((norm_le_pi_norm v.val ⟨j,h⟩).trans v.property)) (H j)).trans_eq (mul_one _)⟩ else ⟨0,by rw [norm_zero]; exact H _⟩
lemma ts_θ (Z:ℕ→ℝ)(H:∀ i,0 ≤ Z i)(j:ℕ): Continuous (θ_guess (l0:=l0) Z H j):=by 
 unfold θ_guess; split; next h=>
    have hz:Continuous fun z:StarPS l0=> z.val (⟨j,h⟩:Fin l0):=(continuous_apply _).comp continuous_subtype_val; exact Continuous.subtype_mk ((continuous_snd.comp hz).const_smul (Z j)) _
 exact continuous_const
-- forecast β upwards exactly in fixed point. shift cutoff irrelevant at off-shell.
def debt_p (L:Side)(z:StarPS l0)(v:ℕ):ℝ:=∑ j∈Finset.range v, ra_C L z j
def tempo_b (L:Side)(B0:ℕ→ℝ)(z:StarPS l0)(v:ℕ):=B0 v+debt_p L z v
lemma mood_c (j:ℕ)(L:Side):Continuous (fun v:StarPS l0=>tempo_b L B0 v j):=by unfold tempo_b debt_p; exact continuous_const.add (continuous_finsetSum _ fun k _=>ra_c _ _)
lemma mood_z (j:ℕ)(L:Side)(v:StarPS l0): tempo_b L B0 v (j+1)=tempo_b L B0 v j+B0 (j+1)-B0 j+ra_C L v j :=by unfold tempo_b debt_p; rw [sum_range_succ]; ring
include D D' hy
lemma mood_a (v:StarPS l0)(j:ℕ)(p':j≤l0): matchedX (μh j) (tempo_b R.L B0 v j):=by
 apply bond_C V a p i N0 T M ht l0 k₀ B0 D J q h R0 E C δ y D' hy j p'; unfold tempo_b; rw [add_sub_cancel_left]; apply (Finset.abs_sum_le_sum_abs _ _).trans; refine (sum_le_sum fun i _=>credit_z R.L v i).trans_eq ?_; simp
-- tilt increase vs nominal
end YM.CF.Py
