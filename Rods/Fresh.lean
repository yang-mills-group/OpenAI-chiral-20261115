import Rods.Shelter
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
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
open Ione Beau Haro Cascade Fief VolumeRate
open Roots Buffered LocalLimit LocalLimit.Papal Dyad Dyad.Keeping Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
open Buffered Advance Afterglow YM.CF.Pannier.Chancel
namespace Decaf
open Stencil Push.SectorMeasure Larch
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{e kL:ℝ}{B:Side}{P:Grasp V.U B e}{qχ:Chi}(A:SiteLedger V P kL qχ){φ:Vxpert V A}{D0 f v D Q U:ℕ}(J:PaperTrace V A f v φ D0)(S:Tickets V D0 D Q R.L A f v)(h:Margin R.L D0 D Q U)
variable(j r p:ℕ){G:Calibration}{m:Side}(u₁: U=G.ℓ)(hf:f≤ j)(hr:j≤r)(hv:r≤ v)(hp:22≤ p)(C D₁:ℕ→ℝ)(he:Scree.mid (A.side j) B=G.c m)
local notation "tK"=> sportT A h j r p u₁ J S h hf hr hv u₁ hp C D₁ he
local notation "Σs" k:max=>mid (A.side k) B
variable (l:List (Tix A j))
lemma add_game{c n:ℝ}(h:0≤c)(v:1 ≤ n): Real.exp (c*n)+1 ≤ Real.exp ((c+1)*n):=by
 let b:= Real.exp (c*n); let d:= Real.exp n; have h₁:1 ≤ b:= Real.one_le_exp (mul_nonneg h (zero_le_one.trans v))
 have h₂:2 ≤ d:=by linarith only [Real.add_one_le_exp n,v]
 rw [add_mul,one_mul,Real.exp_add]; change b+1 ≤ b*d
 linarith only [mul_le_mul_of_nonneg_left h₂ (show 0 ≤ b from (Real.exp_pos _).le),h₁]

-- condition sup eV*n. same. no Prop replacing actual.
lemma countF{l:ℕ}{n:Side}(x:Fin l→ Site n)(w: Injective (node∘ x)): (l:ℝ) ≤ sites n:=by
 have e:= Fintype.card_le_of_injective _ w
 rw [Fintype.card_fin, site_card] at e
 unfold sites; exact_mod_cast e
#check sites
section own
variable (Ξs Ξt:Mark (Scree.mid (A.side v) B)→ℂ)
local notation "n'" => (G.c m)
local notation "n₂"=> mid (A.side j) B
local notation "E"=> (steamPrice R.L j r v (A.gram v).p (A.gram r).p (A.money v) (A.money r))
include J S h u₁ hf hr hv hp
lemma purchase(c:ℝ)(hc:0≤c)
  (Hs:∀ (I:Type)[LinearOrder I][Fintype I](o:I→Site n₂)(l:List (PairKey I)),Very_Ψ o (A.gram j).p.B→(wrap0 l).Nodup→ ‖Ξs (braidP (Yz:=φ) (v:=v) V A j r o C D₁ l)‖≤Real.exp (c*sites n₂))
  (tM:(A.gram j).p.B^3+(A.gram j).p.B≤ p/2)(w:∀ i,j≤ i → i<v→Niche R.L (C i) 0)(y:|revenue R.L C D₁ r j-1|≤1/4)
  (pΞ:Twosome G (Scree.mid (A.side v) B) Ξt)
  (pS:∀ t:Mark (mid (A.side v) B), RG.Envelope t→(∀ x,‖t x‖≤Real.exp (E*sites n₂))→ ‖Ξs t-Ξt t‖≤1)
  {d:ℕ}(e₃:d+addgap G ≤ (G.c m).val)(w₃:∀i, rest G m (Sport.hopit tK l) i d)(q:Sport.race tK l): ‖Ξt (Sport.film tK l)‖ ≤ Real.exp ((c+1)*(4*((d:ℝ)+(addgap G)))^4):=by
 apply Sport.till _ Ξt pΞ (c+1) (add_nonneg hc zero_le_one) _ l e₃ w₃ q
 intro l q
 have u:= sharpRace A J S h j r p u₁ hf hr hv hp C D₁ he l Ξs _ Hs tM q
 obtain ⟨e₁,h₁⟩:=shelter A J S h j r p u₁ hf hr hv hp C D₁ he l w y
 have ht: (l.length:ℝ)≤ sites n₂:= countF _ (spreadRoster A J S h j r p u₁ hf hr hv hp C D₁ he l tM q).1
 let F:=Sport.film tK l
 have hx : ‖Ξt F-Ξs F‖ ≤1:=by rw [norm_sub_rev]; apply pS F e₁; intro x; exact (h₁ x).trans (Real.exp_monotone (mul_le_mul_of_nonneg_left ht (mul_nonneg (bpayG ..) (add_nonneg (pc_pos ..) (pc_pos ..)))))
 change ‖Ξs F‖ ≤ Real.exp (c*sites n₂) at u
 refine (norm_le_insert' Ξs Ξt F hx u).trans ?_; rw [←he]; exact add_game hc (sites_pos _)
where norm_le_insert' {α:Type}(A B:α→ℂ)(x:α){r:ℝ}(b:‖B x-A x‖≤1)(w:‖A x‖≤r):‖B x‖≤r+1:= by have e:= norm_add_le (A x) (B x-A x); rw [add_sub_cancel] at e; exact e.trans (add_le_add w b)
#print axioms purchase
end own
end Decaf
end YM.CF.Py.Rate
end
