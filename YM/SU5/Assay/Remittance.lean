import SatinFixedContrastNovember4
import YM.SU5.Assay.Slip
import YM.SU5.Assay.Audit
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
open Aria Set OS.Semigroup Ballad Six
variable (P:Spine)(R:P.Register)(x:P.Spectrum0 3)
local notation "Zs"=>Ballad.Lead.Clan
local notation "κ"=>P.coffee 3 x
local notation "σ"=>P.rawSlot 3 x
local notation "β"=>P.base 3 x
local notation "Ω"=>P.heaven 3 x
local notation "O"=>(P.ManyF 3 x).Op
local notation "⟪" T "⟫"=> inner ℂ Ω ((T:O) Ω)
local notation "L"=>P.LagOp 3 x
variable (A : Lead.Clan → ℕ→P.Apron)(l:Lead.Clan→ℕ→P.Folio)(T:Lead.Clan→P.LagOp 3 x)
variable (B : Lead.Clan → ℕ→P.Apron)(m:Lead.Clan→ℕ→P.Folio)(U:Lead.Clan→P.LagOp 3 x)
/-!
 Receipt scopes, using chronological orientation (earlier pose,
 later pose). Joint/single height fees, fixed-width and thin-width
 achievements, as slabs actually paid. `calling` and new `remit`
 chronological, equal old spirit formulas, with vacuum enrollments via
 Assay. Mirror orientation if using `P.starboard,P.fore`.
-/
abbrev stacked {Y:Type*}(v:Zs→ℕ→Y) (i:ℕ) := fun z=>v z i
variable (F G:SampleDose)(a b c:ℝ)
local notation "λ'"=>P.called F G
local notation "ν" t:max =>P.singleState 3 t x
def remit : Slip:=(P.seatPair x a b c F G T U,fun z=>⟪κ (T z) a b F⟫,fun z=>⟪κ (U z) b c G⟫)
-- param order P x T U F G a b c
abbrev remitStage (i j:ℕ) := P.remit x (fun z=> β (A z i)) (fun z=>β (B z j)) F G a b c
abbrev calling (i j t:ℕ):=λ' (stacked A i) (stacked B j) t (ν t)
lemma calling_spirits (i j t:ℕ):P.calling x A B F G i j t=(P.seatGrid R x F G A B i j t,
 fun z=>P.spiritOne R x t (A z i) F,fun z=>P.spiritOne R x t (B z j) G):=by
 apply Prod.ext ?_ (Prod.ext ?_ ?_)
 · ext1 z w;exact (P.spirit_pair ..).symm
 · funext z;exact (P.spirit_single ..).symm
 funext z;exact (P.spirit_single ..).symm
variable {P x R T U F G A B l m a b c}
private lemma pack_slips {v:ℕ→ℕ→ℕ→Slip} {r:ℕ→ℕ→Slip} {u:Slip}
 (h:Duet (fun i j k=>(v i j k).1) (fun i j=>(r i j).1) u.1)
 (q:Duet (fun i j k=>(v i j k).2.1) (fun i j=>(r i j).2.1) u.2.1)
 (p:Duet (fun i j k=>(v i j k).2.2) (fun i j=>(r i j).2.2) u.2.2):Duet v r u:= h.pack (q.pack p)
lemma Irons.docket (p:P.Irons x A l T)(q:P.Irons x B m U)
 (u:Walled 3 F a b 0)(v:Walled 3 G b c 0):
  Duet (P.calling x A B F G) (P.remitStage x A B F G a b c) (P.remit x T U F G a b c):=by
 refine pack_slips (Duet.pi fun z=>Duet.pi fun w=>fun f g e t=> (p.tour q u v f g z w e t).traces) ?_ ?_
 · exact Duet.pi fun z=>fun f g e _=> (p.display u f z e).traces.raise (Eventually.of_forall fun _=>le_max_left ..)
 exact Duet.pi fun z=>fun f g _ t=> (q.display v g z t).traces.raise (Eventually.of_forall fun _=>le_max_right ..)

-- Original. Introduce short names for original chronological stock cards.
abbrev reverseR (P:Spine)(s n:ℕ):= fun z=>P.RTest z s n
abbrev obverseF (P:Spine)(s n:ℕ):= fun z=>P.FTest z s n
abbrev obverseCard (P:Spine)(n:ℕ):= fun z=>P.bookPair z n
abbrev reverseCard (P:Spine)(n:ℕ):= fun z=>(P.bookPair z n).transcribe (P.reflectTest 3)

def frescoLimit (P:Spine)(x:P.Spectrum0 3)(s n:ℕ)(b:ℝ)(F G:SampleDose):Slip:= (P.arrayReading x s n b F G,0,0)
namespace Fresco
variable {s n:ℕ}{D N:Doorway}{o:Orders}
variable (h:P.Fresco R x s n D N o F G)
local notation "L₀"=>P.reverseR s n
local notation "R₀"=>P.obverseF s n
include h
lemma stock_bale (t:ℕ)(p:s≤t):P.Bale x D N F G L₀ R₀ (P.reverseCard n) (P.obverseCard n) t := fun z w=> h.sold z w t p
lemma stock_call (t:ℕ)(p:s≤t):λ' L₀ R₀ t (ν t)=(P.arrayFine x s n t F G,0,0):= by
 apply Prod.ext ?_ (Prod.ext ?_ ?_)
 · rfl
 · funext z; exact (h.paid.centered _ p z).1
 funext z;exact (h.paid.centered _ p z).2
lemma stock_remit:Tendsto (fun t=> λ' L₀ R₀ t (ν t)) atTop (𝓝 (P.frescoLimit x s n (D.turnCut N) F G)):=
  (h.paid.steady.prodMk_nhds tendsto_const_nhds).congr' ((eventually_ge_atTop s).mono fun i u=>(h.stock_call i u).symm)
end Fresco
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
