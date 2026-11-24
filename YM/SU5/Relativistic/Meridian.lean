import YM.SU5.Relativistic.Tankard
import YM.SU5.Relativistic.Wheedle
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Window Eire Girt VolumeRate
open Pitching Focus Papyrus.GaugeFlux
namespace LocalLimit
open Preparation
variable {P: Preparation} {l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable (p: FairRoute P.P P.J P.h P.N0 Chi.canonical)
local notation "kT" k:max=>Y.uv k
local notation "Xs" i:max k:max s:max => ((Y.voyage i).X (Y.uv k)).gram s
local notation "Mt" i:max=>Y.ir i
local notation "N" i:max s:max => P.Ctor (Y.ir i) s
local notation "E"=>P.V
local notation "T"=>Y.meter
local notation "G5"=> SU.group
open Pannier
private lemma smoothCount (i s d:ℕ) : More (N i (s+d))= More (N i s) * P.R.L^d:=by
 induction d with
 | zero=> rw [Nat.add_zero,pow_zero,mul_one]
 | succ k ih=>
    rw [← Nat.add_assoc, pow_succ,←mul_assoc,←ih]; exact Subtype.ext (kint ..)
private lemma tiles_present (z:ℕ) (i d s:ℕ)(h:d≤ s) : ∃ (C: Side)(L:Ratio C (More (N i s))),2≤ C.val ∧ L.count=P.R.L^d:=by
 obtain ⟨p,rfl⟩:=Nat.exists_eq_add_of_le h; rw [Nat.add_comm d p]
 let A:= More (N i p); refine ⟨A,⟨P.R.L^d,?_⟩,(show 2≤ (N i p).val*2 from Nat.le_mul_of_pos_left _ (N i p).property),rfl⟩
 rw [smoothCount Y i p d]; rfl
lemma ration (z f:ℝ)(u:0≤f)(e:0<z) :∀ᶠ s in atTop,∀ i k:ℕ,s ≤ Y.uv k→ let B:=Xs i k s; let p:=P.K.top
   Integrable (Papyrus.Mosaic.grain G5 B.path B.funds B.p B.beta f) (prior G5 (More (N i s))) ∧
   ∫ U, Papyrus.Mosaic.grain G5 B.path B.funds B.p B.beta f U ∂ prior G5 (More (N i s)) ≤ Real.exp (z * sites (N i s)+preGa P.V (More (N i s)) (kT k - s) B.beta) :=by
 let t:=P.K.top; let H:=Papyrus.Mosaic.lumin G5 P.L P.chart t.clip t.width t.paths P.V.W.bar f z u ((le_of_lt (by norm_num : (1:ℝ)<12)).trans t.slow_selector) t.width_pos t.paths_pos.le ?bar e
 case bar=> exact le_trans (tsum_nonneg (P.V.L.mood 0).two.1) (P.V.L.mood 0).two.2.2
 obtain ⟨x,hx⟩:=H.exists; obtain ⟨d,k⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (show 1<P.R.L.val by have h:= P.V.tallX; omega)).eventually_ge_atTop x).exists -- tune Nat lemma
 have hv:x ≤ (P.R.L^d).val:=by exact_mod_cast k
 filter_upwards [(turnover P).eventually (hx _ hv),eventually_ge_atTop d] with s z q i r u B
 obtain ⟨ψ,f,g,v,-⟩:= Papal.prices_plot Y s i r u; change B.path=_ at f; change B.funds= t.clip at g
 let C:= (More (N i s)); have η:2≤C.val:= Nat.le_mul_of_pos_left 2 (N i s).property; obtain ⟨A,L,hT,hP⟩:=tiles_present Y 0 i d s q
 have ht: B.p.threshold=temp (hat P.R.L P.x s):=by rw [show B.p=_ from ψ]; exact (Y.meter.boot s).1
 let V:=P.V; let a:=Y.uv r - s; rw [f,g]; refine ⟨Papyrus.Mosaic.grain_int _ _ _ (P.V.L.mood a), (z _ v _ ht L η hT hP _ (P.V.L.mood a) _ ((V.L.roof a).2.1 _) (P.V.L.tied a)).trans ?_⟩
 unfold Papyrus.Mosaic.oppZ preGa views; simp only [sub_eq_add_neg,neg_div,neg_mul]; rfl -- sites
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.ration
