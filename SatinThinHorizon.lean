import SatinThinHare
import YM.CF.Stax.Horizon
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z:Aura n→ℝ)
variable {M:Orbit n→Aura n→ FC (Dwell n)}(T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> Cadre.chip (cribR z) r
local notation "Qd"=> nutL K F
local notation "Nd"=> nutL (cribR z) r
variable (w:0≤h)
open PowerSeries
open Salt Ione Levier Sour
variable (s:Sweep n)
local notation "Ta"=> Salt.actY s
local notation "Tu"=> moldA s
local notation "Pu"=> Palot.robe
local notation "SD"=> Support (More n)
local notation "Πt"=> (boxA s).symm.toEmbedding
local notation "σX'"=> σX (n:=n) P
variable {H:Bag n}(V:Orbit n)(c:Bias δ H P h z)(p:Injective (priorP V.2)) -- tune shadow
variable (hb:∀ i:Orbit n,Injective (priorP i.2)→∀ X:Aura n,H (moldA s X) (yellA s i)=sauce s.charge (detX s.s) (Sour.γS s) (H X i))
local notation "M"=> Cadre.chip (Bias.payX c) F
local notation "M'"=> nutL (Bias.payX c) F
local notation "Λ"=> Ione.suit_Y s
local notation "W'"=> yellA s V
variable (F0:Vow.Cusp n)(e:∀ X:Aura n,∀ D⊆X.val,F0 (moldA s X) (actY s D) (yellA s V)= Ione.suit_Y s (F X D V))
local notation "MU"=> Cadre.chip (Bias.payX c) F0
local notation "Mc"=> nutL (Bias.payX c) F0
variable {m:ℕ}
variable (l:3 ≤ P.B)(w_:1 ≤ h)
include hb c p e l hF w_
lemma rel_cloudT (X:Aura n)(D:SD)(u:D⊆ X.val)(hz:Aqua (Nd X D)): rem_X (P:=P) F0 c.payX (Tu X) (Ta D) W'=Λ (rem_X (P:=P) F c.payX X D V):=by
 have hp:= hz.of_norm; let Tk(i:ℕ):= coeff i (M' X D) V; have H':= c.buys l (zero_le_one.trans w_)
 unfold rem_X Vow.lasting Vow.zenS; rw [← sail_l]; split_ifs with v; swap; exact (map_zero _).symm
 have hv:Summable Tk:=lend (fun i=> (deck F r hF c.payX z H' (zero_le_one.trans w_) X D u i).merit) hp w_ V v
 let L:=(suit_Y s).toLinearMap.toContinuousLinearMap; change _=L (∑' i,Tk i); rw [L.map_tsum hv]; exact tsum_congr fun i=> rel_nut_k F z s V c p hb F0 e X D i u
lemma rel_lightC(X:Aura n)(D:SD)(u:D⊆ X.val)(hz:Aqua (Nd X D)): lamp (P:=P) F0 c.payX (Tu X) (Ta D) W'=Λ (lamp (P:=P) F c.payX X D V):=by
 unfold lamp; simp only [Pi.add_apply,map_add]; rw [rel_bark F z s V c p hb F0 e _ D u, rel_cloudT F r hF z s V c p hb F0 e l w_ X D u hz,e X D u] -- tune
end YM.CF.Stax
