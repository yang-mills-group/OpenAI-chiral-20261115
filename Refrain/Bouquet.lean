import Refrain.Corridor
import Refrain.Earning
set_option autoImplicit false
set_option maxHeartbeats 164000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
open Pitching.Focus AnalyticBridge.Annulus1AD
local notation "H'"=> Pannier.halfLie SU.group
variable {P}
open CF.Refrain BProof
local notation "G5"=>SU.group
local notation "Yx"=> Scales.y G5 R.L
open Fineness
namespace Branch
local notation "X"=> hat R.L x
variable {A:Branch W m k x N0}
variable {i:ℕ}{α:ℝ}(p:CorridorSharp J q h P N0)(H:Service V U W J q h D C R0 P N0 delay)
local notation "dL"=> 8* H'*Real.log R.L.val
include p H
lemma brakeSharp (E:LocalRatio L) :∀ᶠ i in atTop,∀ (m:Side)(k:ℕ)(A:Branch W m k x N0)(b:Bet k), Bon J q h D delay A → Solved P A α b→ A.last.music W.z → i<k →
 let G: ℕ→ℝ := fun n=>entryFin V (k-n) (cell m B R.L n) (A.gram P b n).J ((A.gram P b n).beta); let Z(n):=(A.gram P b n).v.re; |(Z i-Z (i+1))-(G (i+1)-G i)| ≤ 7*shrift R.L (hat R.L x i)*sites (cell m B R.L i):=by
 let C':= dL; let M:=guardFee (W:=W); let T':=1+|M|
 filter_upwards [(stage_slope V x).eventually p.toll, height_shrift V B x |dL|, (stage_slope V x).eventually (entryFiner V E T')] with i u h ξ m k A b t c a e G Z
 let d:=3*shrift R.L (hat R.L x i)
 let X₀:=A.toSpine.address i; let F:=A.gram P b; let v:= (b.read (i+1)).re; let Hφ:=A.active P b i; let w:=A.corr P b (i+1); let U₀:= A.offset P b (i+1); let P':=A.op P i
 obtain ⟨hu,hκ,hA⟩:= yearFit t H c e a; let G':= entryFin V (k-i) _ (F i).J v
 have hpV:|G' - G i| ≤ d*sites (cell m B R.L i):=ξ v (F i).beta hu hκ ((by rw [abs_sub_comm]; exact hA.trans ((le_abs_self M).trans (le_add_of_nonneg_left zero_le_one))) : |v-(F i).beta| ≤ T') _ _ _
 have H₀: Heed V X₀ d v U₀ (F i).v :=by
    have hr:=u _ _ _ _ _ (t.request i e) v w.1 (hat_step i ▸ (t.beta_ok H c.toRealQ (i+1) e).2) (t.flow (t.charged H c.toRealQ (i+1) e)) U₀; change Heed V X₀ d v U₀ (A.offset P b i); rw [offset.eq_1 P A b i,dif_pos e]; exact hr
 have hR:crestDue V X₀ v= G (i+1)-G'-C':=by unfold crestDue; change entryFin V (k-1-i) _ _ _-entryFin V (k-1-i+1) _ _ _-_= _; rw [show k-1-i+1=k-i from by omega,show k-1-i=k-(i+1) from by omega]; rfl
 unfold Heed at H₀; rw [hR] at H₀
 have he:=abs_le.mp (h m); change -_ ≤ C'∧C' ≤ shrift R.L (hat R.L x i)*sites (cell m B R.L i) at he
 change |Z i-Z (i+1)-(G (i+1)-G'-C')| ≤ d*sites (cell m B R.L i) at H₀; rw [abs_le] at hpV H₀ ⊢; unfold d at *; constructor <;> linarith only [he.1,he.2,H₀.1,H₀.2,hpV.1,hpV.2]
end Branch
end YM.CF.Py.Rate
