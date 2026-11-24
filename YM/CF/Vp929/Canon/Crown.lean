import YM.CF.Vp929.Canon.Cedar
import YM.CF.Vp929.Stage.Costs
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace TestW
open Fir
open SU Bloch Tap
variable {n L:Side} {M:Male} {j:ℕ} {q C d a b v A t:ℝ}
variable {F:RegBudget n}{P:BudgetPoint}{s:Finset (Scree.Hub n)} (vS:liveB s)
local notation "E0"=> Op (Single n)
local notation "E2"=> SpinIdx × SU.Slot
local notation "WW" u:max=> heroP u
local notation "Ψ"=> StackL F s
local notation "μX"=> (1:Pane n)
local notation "ρX"=> spar j M (1:Pane n)
open Salt Vow Bake Larch Cycle929
open Sour Sour.MatchW Sour.MatchW.Technique
variable {T U:BeatL n}{e h r θ b0 b1 b2:ℝ} [Nonempty (Haro.ΘS r)]{O:Scree.Loom n}{N:ℕ}
local notation "pP"=> P

variable (χ:Technique P h e θ N O T U b0 b1 b2 r)(p:2*P.supportExponent*Fief.tileN 1 ≤ b0/2*P.B)
def lmap : ↥SpaceM →ₗ[ℝ] RegBudget n := (χ.lerQ).1.choose
private lemma lerS (i : Haro.ΘS r):χ.ler i= lmap χ i.val:=(χ.lerQ).1.choose_spec i|>.symm

local notation "Wa"=> Haro.ΘS r
local notation "K0"=> L.val
variable (qB:0 < r)(u:1 ≤ j)(X Y: RegBudget n)(i: Haro.ΘS r)
include χ
lemma vaultX (v:∀ x:Scree.Hub n,coverNumber P.B x.val.2 ≤1 → x∈s) : StackL (χ.ler i) s= -(plankP n (Haro.riseV i)):=
 χ.bond.stackF χ.H χ.pay h χ.floor i χ.hope χ.v0 χ.threshold χ.tally χ.rate χ.Bsize χ.economic s v

omit χ in
lemma plank_get (u:1 ≤j)(v0:↥SpaceM) : pointW n j u M (plankP n v0.val)= v0:=by
 have hx:= wave_z j u M v0.val; change projectorMind (τ_ j M (plankP n v0.val))=_; unfold τ_; rw [show heroP (plankP n v0.val)= (fun _=>waveB v0.val) from funext fun i=> Exa.wave_o ..,hx]; exact Submodule.projectionOnto_apply_left _ _
include u
open Fixed.Voltage
local notation "Φ"=> (Fixed.Voltage.frame_P (s))
local notation "Σ_"=> pointW n j u M
lemma getS (v:∀ x:Scree.Hub n,coverNumber P.B x.val.2 ≤1 → x∈s): pointW n j u M (StackL (χ.ler i) s)= - i.val:=by rw [vaultX χ i v,map_neg, plank_get]
omit u
include qB
lemma normalize_ray (x:↥SpaceM)(p:x≠0): ∃ y:Wa,(‖x‖/r) • y.val=x:=by
 have ht:=norm_pos_iff.mpr p
 let z:= (r/‖x‖) • x; have hg:‖z‖=r:=by unfold z; rw [norm_smul, Real.norm_of_nonneg (div_pos qB ht).le]; field
 refine ⟨⟨z,hg.le⟩,?_⟩; change (‖x‖/r) • ((r/‖x‖) • x)=x; rw [smul_smul]; field_simp; rw [one_smul]
lemma vaultY (u:1 ≤ j)(x:↥SpaceM)(v:∀ x:Scree.Hub n,coverNumber P.B x.val.2 ≤1 → x∈s) : pointW n j u M (StackL (lmap χ x) s)= - x:=by
 change pointW _ _ _ _ (Φ _)= _; by_cases q:x=0
 · subst x; rw [map_zero,map_zero,map_zero,neg_zero]
 obtain ⟨y,k⟩:=normalize_ray χ qB x q; let c:= ‖x‖/r
 let W:=pointW n j u M; change W (Φ (lmap χ x)) = -x
 nth_rw 1 [←k]; rw [map_smul,map_smul,map_smul,←lerS,show W (Φ _)= - y.val from getS χ u y v,smul_neg,k]
def u_early:= Py.u0 Pitching.Focus.HI

include p
lemma wageL (x:ℝ)(t:P=Pitching.Focus.epoch x)(Z: ↥SpaceM) : IncX Utrue (lmap χ Z) P h (u_early*h^2*‖Z‖):=by
 by_cases e:Z=0; · rw [e,map_zero,norm_zero,mul_zero]; exact (Vale.lye _ _ _).1
 obtain ⟨Y,w⟩:= normalize_ray χ qB Z e
 obtain hv:= χ.bond.starH (p:=P) χ.H χ.pay h χ.floor Y χ.hope χ.v0 χ.threshold χ.tally χ.rate χ.Bsize χ.economic χ.pos p
 change IncX Utrue (χ.ler Y) P h _ at hv
 obtain hh:= crestV _ _ hv (‖Z‖/r); rw [lerS,←map_smul,w,abs_of_nonneg (div_nonneg (norm_nonneg _) qB.le), show Glyph.cap1 _ _ _=u_early*r*h^2 from ?_] at hh
 · convert hh using 1; field
 rw [t]; exact Py.cap1_g ..
end TestW
end Test
end YM.CF.Py.Rate
