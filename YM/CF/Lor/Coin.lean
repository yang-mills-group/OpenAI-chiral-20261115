import YM.CF.Lor.Ton
import YM.CF.Corne.Peru
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Nacre BoreP Font Fief rates Braid Rel
variable(P:Side)(L T:ℕ→ℝ)(σ:ℝ)(l j n m:ℕ)
-- gauge loop α subtraction and ψ
lemma roll_k (u:ℕ→ℕ)(h:CapY u)(p:nib L)(ht:nib T)(hv:l+77≤ j)(hs:0<σ)(v:3 ≤ n) :∃ r:ℕ, j≤r ∧∃ f g:ℝ→ℝ,sizeK P 2 f ∧ sizeK P 3 g∧∀ᶠ x:ℝ in atTop, let p:= u (radiusB x); let y:= L (radiusB x); let d:= T (radiusB x)*temp x; p ≤ (r-1)*radiusB x∧∀{c f':Side}(S:StepData c f')(V:Tab S→FileM c G₅)(A:Tab S→DirP c),(r+r+101)*radiusB x ≤ c.val → Wick V A p n σ y d →∀ t:Tab S,(∀ o,CakeF (V t o) o (Cay.horn x l) n σ y∧ cFoot 2 (satX (V t o))) →∀ (R:Stores S)(U:Config G₅ c),R.flags=RG.flags (temp x) U→∀ o:Site c, let X:=issued x j r V A R t o ∘Vmove x U
 Allows n X 0 (f x)∧(o∉ R.dome (p+r*radiusB x) → Allows n X 0 (g x)):=by
 have hj:=h; obtain ⟨s,h⟩:=h; let r:= j+2*s+1; have hy:j ≤r:=by unfold r; omega
 obtain ⟨a,b,hX,hB,hZ⟩:=Corne.beamW j r n σ hs v (by omega) hy
 let P'(x):=u (radiusB x); let Y(x):=L (radiusB x); let d(x):=T (radiusB x)*temp x; let U(r x:ℝ):= Jet.composeCost n (vatP 1 1 n (Y x) 0 (Arena.rankC r x)) (1/2); let W(x):= plot (P' x)*U b x; let V(x):= U a x+(W x+W x); let X(x):= Arena.compass n 2 x (Y x) (d x) b
 have he:= BoreP.nob _ p radius_c; have hf(r):sizeK P 2 (U r):=tempo_x _ _ _ (he.creditK _); have hh:=beam_b P hj radiusB radius_c _ (hf b)
 refine ⟨r,hy,V,X,(hf a).accrue (hh.accrue hh),beamZ P n hj _ _ he (((BoreP.nob _ ht radius_c).creditK _).tint (sizeK.tempo P)),?_⟩
 filter_upwards [hZ, Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x p v; intro ℓ t y; have hh : ℓ ≤ (r-1)*radiusB x:=by
    apply (h _).trans; unfold Pad; have he:= Nat.mul_le_mul_left s (le_refl (radiusB x)); have hv:= Nat.mul_le_mul_left s v; rw [Nat.mul_add]; unfold r; simp_rw [Nat.add_sub_cancel,Nat.add_mul]; rw [Nat.mul_assoc]; omega -- risk
 refine ⟨hh,fun S V A hp h t' hb R U hv o=>?_⟩; exact p.2.2 S V A _ _ _ _ hh (Nat.mul_le_mul_right _ (by omega)) hp (hib ‹nib L› _) (mul_nonneg (hib ht _) (temp_nonneg _)) h _ hb R U hv o
end YM.CF.Lor
