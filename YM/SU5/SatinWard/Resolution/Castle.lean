import YM.SU5.SatinWard.Resolution.Snowy
import YM.SU5.SatinWard.Resolution.Gossip
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
variable {s:ℕ}(a b' c d:ℝ)
open BProof Pressure
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
local notation "K'"=> P.calibration
local notation "τ" s:max=> Pressure.temp (hat P.par.R.L P.par.x s)
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open Quire LampsQ LitCurrent Surplus Next.Rank Next.Rank.Spindle PSE
local notation "Δ★"=> P.run
local notation "H★"=> P.large
local notation "Lp"=> lapQ P.run
local notation "U'S" => WCash Δ★ s
section
variable {Z:ℕ→ WCash P.run s × ℂ}{z:WCash P.run s × ℂ}{D:ℝ}{u:ℕ}{L:Chamber.Division}(p:Tendsto Z atTop (𝓝 z)) (m:∀ᶠ i in atTop, Curie P.run s u L D (Z i).1 (Z i).2)
local notation "B"=> P.thresholdF s
include p m
lemma castle_curie : Curie P.run s u L D z.1 z.2:=by
 let g:= p.fst_nhds; have hx:∀ c i,Tendsto (fun j=>(Z j).1 c i) atTop (𝓝 (z.1 c i)):=fun c i=> tendsto_pi_nhds.mp (tendsto_pi_nhds.mp g c) i
 have h(s':Signed)(l:Sage): Tendsto (fun j=> concQuery B (Z j).1 s' l) atTop (𝓝 (concQuery B z.1 s' l)):= tendsto_finsetSum _ (fun i _=>tendsto_finsetSum _ (fun k _=>(((hx i k).mul_const _).mul_const _)))
 constructor
 · intro i l; exact ⟨tendsto_nhds_unique_of_eventuallyEq (h (sailUp i) l) (p.snd_nhds.const_mul _) (m.mono fun k v=> (v.style i l).1),tendsto_nhds_unique_of_eventuallyEq (h (sailDown i) l) (p.snd_nhds.const_mul _) (m.mono fun k v=> (v.style i l).2)⟩
 · exact le_of_tendsto (tendsto_finsetSum _ (fun i _=>tendsto_finsetSum _ (fun j _=> (hx i j).norm))) (m.mono fun i v=> v.budget)
 exact le_of_tendsto (p.snd_nhds.sub_const _|>.norm) (m.mono fun i v=> v.buoy)
omit p
lemma castle_sub : ∃ z': WCash P.run s × ℂ, ∃ c:ℕ→ℕ, StrictMono c∧ Tendsto (Z ∘ c) atTop (𝓝 z')∧ Curie P.run s u L D z'.1 z'.2:=by
 let V:=(bmass u:ℂ)* IndexMag.medalD L; let x:= polishQ P s; let S:=((bmass u:ℝ)+1)/x+‖V‖; let E:=max D S
 have hx:∀ᶠ i in atTop,Z i∈ Metric.closedBall 0 E:=m.mono fun i h=> by
    rw [mem_closedBall,dist_zero_right,Prod.norm_def]; apply max_le; swap; · exact ((norm_le_norm_sub_add _ V).trans (add_le_add_left h.buoy (‖V‖))).trans (le_max_right ..)
    have hG: (∑ c:Sheds B,∑ k:Sheds B, ‖(Z i).1 c k‖) ≤ D:= h.budget; have he:0≤ E:=(le_max_left D S |>.trans' hG) |>.trans' (sum_nonneg fun i _=>sum_nonneg fun j _=> norm_nonneg _)
    apply (pi_norm_le_iff_of_nonneg he).2; intro a; apply (pi_norm_le_iff_of_nonneg he).2; intro b; refine le_trans (b:=∑ c:Sheds B,∑ k:Sheds B, ‖(Z i).1 c k‖) ?_ (hG.trans (le_max_left ..)); exact (single_le_sum (s:=univ) (fun j _=>norm_nonneg ((Z i).1 a j)) (mem_univ b)).trans (single_le_sum (s:=univ) (fun a _=> sum_nonneg fun j (_:j∈univ)=> norm_nonneg ((Z i).1 a j)) (mem_univ _)) -- syntax
 obtain ⟨m',u⟩:=eventually_atTop.mp hx; let g:=fun m:ℕ=> m'+m; let A:StrictMono g:=fun i j p=>by unfold g; omega
 obtain ⟨a,u,b,H,ht⟩:= (isCompact_closedBall (0: WCash P.run s × ℂ) E).tendsto_subseq (x:=Z ∘ g) (fun i=> u (g i) (by unfold g; omega)); exact ⟨a,g∘b,A.comp H,ht,castle_curie (Z:=Z ∘ (g ∘ b)) ht ((A.comp H).tendsto_atTop.eventually m)⟩
end
-- chip turn.restricted path. powers any Tab with constant faces and variable tax.
section
local notation "iv" i:max=> P.period (P.projection.rows (σ i))
local notation "kv" i:max=> P.cutoff (P.projection.columns (σ i))
variable (Ψ : (i:ℕ) → Wave (Single (Papal.count P.run s (P.period (P.projection.rows (σ i))))))
abbrev flicker (P:Spine)(s)(σ:ℕ→ℕ)(W:(i:ℕ)→Wave (Single (count P.run s (P.period (P.projection.rows (σ i)))))):Prop:=
    ∀ᶠ i in atTop, IsStarProjection (FlatPaneP 4 (gram P.run s (P.period (P.projection.rows (σ i))) (P.cutoff (P.projection.columns (σ i)))).J.M (count P.run s (P.period (P.projection.rows (σ i))))) ∧ Fock.Sea (FlatPaneP 4 (gram P.run s (P.period (P.projection.rows (σ i))) (P.cutoff (P.projection.columns (σ i)))).J.M (count P.run s (P.period (P.projection.rows (σ i))))) (W i)
-- very big later.
variable {I:Type}[DecidableEq I]{Z:ℕ→ Tab I}{V:Tab I}{w:ℕ→ℕ} (g:1 ≤ hat P.par.R.L P.par.x s) (p:Tendsto w atTop atTop) (φ:∀ i,(Z i).w=V.w∧ (Z i).cover=V.cover)(v:∀ i,Tendsto (fun k=>(Z k).tax i) atTop (𝓝 (V.tax i))) (t': flicker P s σ Ψ)
include Ψ T φ p v g t'
lemma chip_city (y:ℝ): Tendsto (fun i=> Chip P.run y (iv (w i)) (kv (w i)) s (Z i) (Ψ (w i))) atTop (𝓝 (V.issues (β s) (W s) y)):=by
 simp only [Chip,VistaP,Tab.issues]; simp_rw [(φ _).1,(φ _).2]; apply tendsto_finsetSum; intro i h; exact (v i).mul ((Picker.kalon P.run P.law P.history T.order.tendsto_atTop T.path_permanent s g Ψ t' (V.w i) (fun _=>y) tendsto_const_nhds).comp p)
end
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
