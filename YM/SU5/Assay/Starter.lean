import SatinFixedContrastNovember4
import YM.SU5.Assay.Audit
import YM.SU5.Assay.Gold
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
open Glaze
/-!
 Repeat **front** with the reviewed n at every finer height, paying
 coeval prices on a new host while preserving normalization & keeping
 the same stock clearance rule. Every label. Try also repeating the
 entire old centered formula (unamplified); loses all its prices even
 at positive lag here, not retaining the old rank. This purchase *does*
 retain all entry discrepancies (noncentered contact only so far) for
 the front itself. A quantitative coat test for paid owners too.
-/
variable (n:ℕ)(M:P.Menagerie)
-- Literal stock bodies
def refront (Z:Zs):= serial (fun _=> P.coin Z n)
abbrev togetherBook (P:Spine)(n:ℕ)(Z:Lead.Clan)(_:ℕ):=P.stockFolio (P.flash n) Z
-- unchanged old pole formula at every finer height
abbrev replayBody (P:Spine)(n:ℕ)(Z:Lead.Clan)(s:ℕ):=P.experimentBody Z s n
abbrev replayBook (P:Spine)(n:ℕ)(Z:Lead.Clan)(_:ℕ):=P.bookPair Z n
-- A carrier dressed with the same literal stock normalization
def firstCard: ℕ→ P.Folio:= fun _=>[(1,1)]
local notation "ρ"=>P.breathes
lemma firstCarrier (s:ℕ): P.Wove none ((ρ) s).S ((ρ) s).F (P.firstCard s):= Wove.tuft Yarn.unit'
lemma breath_clutch : P.Clutch Set.univ (ρ):=by
 have v:= P.breath_small
 refine ⟨v,fun a q=>⟨1,zero_le_one, (v.early q).mono fun s h i _=>?_⟩⟩
 rw [P.unit_rawBase _ _ _ rfl _ _ h h]
 exact wax_pay ..
abbrev borne (P:Spine)(M:P.Menagerie)(Z:Lead.Clan):=serial (P.inlay P.breathes M Set.univ Z)
abbrev borneBook (P:Spine)(M:P.Menagerie)(Z:Lead.Clan):= P.inlayBook P.breathes M Set.univ Z P.firstCard

-- force of either refront or borne, **fixed** company price, not divided out
def visor (Z:Lead.Clan):L:=P.electro M Z •P.unitLag 3 x
variable {M}
local notation "τ"=>P.visor x M
include R
lemma obtains_visor {Q:ℕ→P.Apron}{Z:Lead.Clan}
 (u:P.RawNormal 3 x Q (fun _=>0) 0 (P.electro M Z • P.rawUnit 3 x)):P.Kiln 3 x Q (τ Z):=by
 have z:=u.kiln R
 rw [P.respool_scale,P.respool_unit] at z;exact z
variable {n}
lemma Company.refront {a:ℝ}(h:P.Company n M a): P.Irons x (P.refront n) (P.togetherBook n) τ:=by
 have l:∀Z,P.calibration.ℓ<n∧(M Z).n=n:=fun Z=>⟨(h.clock Z).symm ▸ (M Z).gap,h.clock Z⟩
 exact ⟨fun _ _=>rfl,fun Z s=> P.coin_first _ n s (l Z).1,fun Z=>P.obtains_visor R x (h.coin_ms P x Z n)⟩

variable (M)
lemma how_borne : P.Irons x (P.borne M) (P.borneBook M) τ:=
 ⟨fun _ _=>rfl, fun Z s=> P.inlay_first _ _ _ Z P.firstCarrier s,
   fun Z=>P.obtains_visor R x (P.breath_clutch.inlay_pole M Z (Set.mem_univ _) (P.breath_raw 3 x))⟩
lemma wane (g:Tasting.Paid P.par)(h:P.calibration.ℓ<n):P.Irons x (P.replayBody n) (P.replayBook n) 0:=by
 refine ⟨fun _ _=>rfl,fun Z s=> P.experiment_first Z n s h,fun Z=>?_⟩
 have z: (0:P.RawLag 3 x)=(0:ℂ)•P.rawUnit 3 x:=by simp
 have y:=(P.experiment_wash x Z n g h).kiln R
 have v:P.respool 3 x 0 0=(0:L):=by rw [z,P.respool_scale,zero_smul]
 rw [v] at y;exact y
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
