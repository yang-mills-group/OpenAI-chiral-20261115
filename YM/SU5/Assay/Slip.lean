import SatinFixedContrastNovember4
import YM.SU5.Assay.Patina
import YM.SU5.Assay.Chandelier
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set Six Ballad
local notation "Zs"=> Ballad.Lead.Clan
variable (P:Spine)(x:P.Spectrum0 3) (D N:Doorway) (F G:SampleDose)
variable (C E:Ballad.Lead.Clan→P.Apron)(l m:Ballad.Lead.Clan→P.Folio)(t:ℕ)
local notation "Φ"=>D.canopy N
local notation "ν"=>P.singleState 3 t x
local notation "W"=>P.prepared t
local notation "α" z:max=> W (C z) F
local notation "β" z:max=> W (E z) G
/-!
 Earnings table: JOINT and both SINGLE receipts. Slip `P.called`
 defined on the raw marks, hence usable also for regulator pricing
 (viewer NOT a change of these marks; also retain original
 separator costs). Earlier stance is chronological `C`. Tables
 permit joint accuracy and lower bounds, including on connected
 functions when warranted. Payouts cover the whole Canopy.
-/

abbrev Slip := CrossRead × (Zs→ℂ) × (Zs→ℂ)
def called (Y:P.Test→ℂ): Slip:=
 (Matrix.of fun z w=>Y ((α z)*(β w)),fun z=>Y (α z),fun z=>Y (β z))
def Bale: Prop:=∀z w,P.DuoNotice x t D (C z) z.2 (l z) F N (E w) w.2 (m w) G
-- #check @called : P F G C E t ; Bale P x D N F G C E l m t
variable {P x D N F G C E l m t}
namespace Bale
variable (b:P.Bale x D N F G C E l m t)
include b
local notation "μ"=> P.called F G C E t
local notation "Y"=> P.Test→ℂ
local notation "η"=> P.paperSplit t x
lemma limit (v:ℕ→P.Test→ℂ) (h:∀g,P.asked_at t g Φ→Tendsto (fun i=>v i g) atTop (𝓝 (ν g))):
 Tendsto (fun i=> μ (v i)) atTop (𝓝 (μ ν)):=by
 have hj:Tendsto (fun i=> (μ (v i)).1) atTop (𝓝 (μ ν).1):=
   tendsto_pi_nhds.mpr fun z=>tendsto_pi_nhds.mpr fun w=>h _ (b z w).lights.2.2
 have hf:Tendsto (fun i=> (μ (v i)).2.1) atTop (𝓝 (μ ν).2.1):=tendsto_pi_nhds.mpr fun z=>h _ (b z z).lights.1
 have hg:Tendsto (fun i=> (μ (v i)).2.2) atTop (𝓝 (μ ν).2.2):=tendsto_pi_nhds.mpr fun z=>h _ (b z z).lights.2.1
 exact hj.prodMk_nhds (hf.prodMk_nhds hg)
lemma threshold {Gain:Set Slip}(y:Gain∈𝓝 (μ ν)): ∃δ>0,∀Y':Y,P.Patina 3 t x Φ δ Y' → μ Y'∈Gain:=
 Patina.good (Pass:=fun Y'=> μ Y'∈Gain) fun v h=> (b.limit v h).eventually y

lemma mute (f:Y)(p:∀{V g c}, V ⊆Φ → P.Payout x t V g c→ f g=0): μ f=0:=by
 apply Prod.ext ?_ (Prod.ext ?_ ?_)
 · ext1 z w;exact p (b z w).hangs.2.2 (b z w).prices
 · funext z;exact p (b z z).hangs.1 (b z z).first.prices
 funext z;exact p (b z z).hangs.2.1 (b z z).second.prices
lemma paper : μ η=0:=b.mute η (fun _ h=>h.compare)
variable {k:ℤ}{w n a:ℕ}{Z X Y':Finset Cover}{δ:ℝ}{g:P.Test} {i j:ℕ} {d:ℝ}
variable (p:P.FloorService 3 t x (D.canopy N) k w Z n δ a g X Y' d)
variable (e:P.Flight 3 t x k w Z n δ a g X Y' i j)
include p
lemma primer : μ e.primer=0:=b.mute _ (fun u h=> (p.impartial e u h).1)
end Bale
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
