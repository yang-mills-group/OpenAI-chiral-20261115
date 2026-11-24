import GaugeFieldConstruction.Emu
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
open TableF.Axon Siete Lenten.ModuleB MultiNext.SignedSource Lyre Banjo Analysis
variable {c f:Side}{Z:Scree.Hub f}{P:BudgetPoint}{Q:InkD f}{C s h:ℝ}{r k m:ℕ}{M:Male}{T:Script Male}{G:Ratio c f}{V:Scree.Hub f}{σ U B:Bool→ℝ}{g: Finset (Dwell f)→ℝ}{X:SM f→ℝ}{o:Skye.Seat c}
abbrev PLuck (s:ℝ):ℝ:= DevelopCost* DepTotal s
lemma posLuck (u:1 ≤ s):0 ≤ PLuck s:=by have h:0 ≤ xHoch 6:=zero_le_one.trans (multip 6).choose_spec.1; have hs:=zero_le_one.trans u; unfold PLuck; apply mul_nonneg (Finset.sum_nonneg (fun i _=> Nat.cast_nonneg _)); unfold DepTotal DepotPrice; positivity
abbrev ΦMint (G:Ratio c f)(U:Pane f)(Q:InkD f)(u:Odd G.count.val)(T:Script Male)(M:Male):Op (Single c):= Hove.totF 4 G u T M (orbitPH (Q U))
-- robust on any directions on FiniteGaugeData. currency
variable (w:Odd G.count.val)(p:PressB P V Q h C)(u:Nonwrapping V.val.2 V.val.1)(v:∀ i,0≤g i)(dV:∀ U,BedP P U Q V g)
variable (hp:0<h)(q:10 ≤(More f).val)(s₀:1≤ s)(wZ:Stakes s (αN G.count) V P) (vM:r=3→landA M V.val.1 Q P h=0)(gR:r ≤3)(qt:quote_B M (orbitPH (Q 1)) V.val.1 h r)
variable (hv:100 < f.val)(α:Silks σ U B m)(u₀:3 ≤ m)(he:Use 4 G.count T)
abbrev φlens (G:Ratio c f)(M:Male)(o:Skye.Seat f)(s:ℝ)(g: Finset (Dwell f)→ℝ)(r:ℕ):= LanceZ G M o (PLuck s) (Zinc g) r
open Nacre Tap
include p u v dV hp q s₀ wZ vM gR qt hv α u₀ he
lemma φToss (E:BudgetPoint)(y:E.order=6)(F:tangD c→tangD f)(l:LocalCurve P V F {z| E.dirBound o z} s (αN G.count))(dP:∀ k≤6,∀ u:Fin k→tangD c,(∀ j,E.dirBound o (u j))→ StrongE P V s (αN G.count) (iteratedFDeriv ℝ k F 0 u))(a b:Single c): Signs E o (fun z=> ΦMint G (increment 1 (F z)) Q w T M a b) (φlens G M V.val.1 s g r (a,b)):=by
 let X:= fun i=> orbitPH (Q (increment 1 (F i))); let U:=Op (Single f); let K: U →L[ℝ]ℂ:= LinearMap.toContinuousLinearMap (show U→ₗ[ℝ]ℂ from ⟨⟨(fun i=> totF 4 G w T M i a b),fun i j=>by rw [tot_add]; rfl⟩,fun r v=>by change totF 4 G w T M (r • v) a b = _; rw [tot_scale]; rfl⟩)
 have hg:= Zinc_pos v
 have hh:=l.home.2 1 (by simp)
 have hb(i j:Single f): ContDiffAt ℝ (6:ℕ∞ω) (fun z=> X z i j) 0:= (PortProof p dV _ (by simpa only [one_smul] using hh) i j).comp 0 l.smooth
 -- Op equivalence
 let A:=coordL (k:=Single f)
 have hz:ContDiffAt ℝ (6:ℕ∞ω) (A ∘ X) 0:= contDiffAt_pi.mpr fun i=> contDiffAt_pi.mpr (hb i)
 have hk:ContDiffAt ℝ (6:ℕ∞ω) X 0:=by simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using (A.symm.contDiff.contDiffAt.comp 0 hz)
 have he':= Lance_cost (M:=M) (e:=w) α u₀ (posLuck s₀) hg gR V.val.1 -- binder M needed
 refine ⟨he'.1 (a,b),by rw [y]; exact K.contDiff.contDiffAt.comp 0 hk,fun i j Uι h=>?_⟩
 rw [y] at j; have h1:αN G.count ≤1:= by unfold αN; exact inv_le_one_of_one_le₀ (by exact_mod_cast G.count.property)
 have hx:= MastBill (b:=αN G.count) p u v dV q (α_pos _).le h1 s₀ wZ vM gR qt _ _ l dP Uι h j -- shadows. use explicit
 let W:= Matrix.of fun (i' j':Single f)=> iteratedFDeriv ℝ i (portE Q i' j'∘ F) 0 Uι; have he'':iteratedFDeriv ℝ i X 0 Uι=W:=by
    ext i' j'; let P':= (show U→ₗ[ℝ]ℂ from ⟨⟨fun x=> x i' j',fun i j=>rfl⟩,fun _ _=>rfl⟩).toContinuousLinearMap; exact (DFunLike.congr_fun (P'.iteratedFDeriv_comp_left (f:=X) hk (Nat.cast_le.mpr j)) Uι).symm
 change ‖iteratedFDeriv ℝ i (K∘ X) _ Uι‖ ≤ _; rw [K.iteratedFDeriv_comp_left hk (Nat.cast_le.mpr j)]; change ‖K (iteratedFDeriv ℝ i X 0 Uι)‖ ≤ _; rw [he'']; exact pull_v (e:=w) α u₀ he hv hp.ne' hx (posLuck s₀) hg gR (a,b)
end Boom
end YM.CF.TableF
end
