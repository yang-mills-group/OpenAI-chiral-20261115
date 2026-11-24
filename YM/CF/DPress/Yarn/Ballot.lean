import YM.CF.DPress.Yarn.Harvest
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
namespace Crib
open Silo
local notation "jS" j:max=> Dh V M B (n-1-j) j
local notation "jA" j:max=> cell M B R.L j
local notation "jO" j:max=> Λ.O (hat R.L x j)
local notation "jC" j:max=> Tew.tiny R (hat R.L x j)
local notation "Xt" j:max=> venue D j
open Chaff Gloss Maize Tye RP RP.Str Brace
open Source
variable {T : Source P_ J}{Jp:ℕ→ℝ→ℝ}
variable (Y:StarPS n)(hk:Beacon T F n Jp k)
local notation "hx'"=> hat R.L x
local notation "U♥"=> StarPS n
open Cap
abbrev σmove (i:ℕ):= grant_B R.L (hat R.L x i)
lemma note_σ(i:ℕ): σmove (x:=x) (R:=R) i= Real.sqrt (hat R.L x (i+1)):= by rw [hat_succ]; rfl
include D in
lemma σcoin(i:ℕ) : 0<σmove (x:=x) (R:=R) i:= note_σ (R:=R) (x:=x) i ▸ Real.sqrt_pos.mpr (F.now (i+1))
abbrev δv (v:StarPS n):= wake (σmove (R:=R) (x:=x)) v
abbrev BQ(i:ℕ)(v:StarPS n):= D.β i+(D.b_T Y k-D.β k)+∑ i∈Finset.Ico k i, δv (R:=R) (x:=x) v i
lemma con_B (i:ℕ): Continuous (fun z:StarPS n=> BQ (k:=k) D Y i z):=by unfold BQ; exact continuous_const.add (continuous_finsetSum _ fun j _=>Cap.wakeC _)
lemma BQk(c:StarPS n): BQ (k:=k) D Y k c= D.b_T Y k:=by unfold BQ; rw [Ico_self,sum_empty,add_zero]; ring
lemma grow(c:StarPS n)(p:k ≤ i): BQ (k:=k) D Y (i+1) c+toll D i=BQ (k:=k) D Y i c+δv (R:=R) (x:=x) c i:=by unfold BQ; rw [Finset.sum_Ico_succ_top p]; unfold toll; ring
include D hk
lemma treaty (v:StarPS n) (u:k ≤ i)(p:i ≤ n) : matchedX (hat R.L x i) (BQ (k:=k) D Y i v):=by
 unfold BQ; obtain ⟨h,t⟩:= D.βnarrow p; have hx:= F.now i; have he:k*Thrift.σ R≤ (hx' i)/16:= (D.wage (i:=k)).trans (div_le_div_of_nonneg_right (F.age k u) (by norm_num)); let X:= hx' i
 let G:= δv (R:=R) (x:=x) v; have hg(j:ℕ)(g:j∈Finset.Ico k i): |G j| ≤ Real.sqrt X:= le_trans (Cap.wakeB _ _ (D.σcoin j).le) ((note_σ j).trans_le (Real.sqrt_le_sqrt (F.age (j+1) (by have he:=(mem_Ico.mp g).2; omega))))
 have hv: |∑ j∈Finset.Ico k i,G j|≤ X/16:=by
    have v':i-k≤T.b+1:=by have h:=hk.h; omega
    have u': ((T.b+1:ℕ):ℝ) *Real.sqrt X ≤ X/16:=(hk.ok _ (F.time (i:=i))).1.stim; refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum hg).trans ?_); rw [sum_const, Nat.card_Ico,nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr v') (Real.sqrt_nonneg _)).trans u'
 obtain ⟨b1,b2⟩:= abs_le.mp hv; obtain ⟨k1,k2⟩:= abs_le.mp ((D.δT Y k).trans he)
 change X/2≤ D.β i+ (D.b_T Y k-D.β k)+(∑ j∈Finset.Ico k i,G j) ∧ _; constructor <;> (unfold G X at *; linarith)
end Crib
end FitD
end YM.CF.Py.Kay
