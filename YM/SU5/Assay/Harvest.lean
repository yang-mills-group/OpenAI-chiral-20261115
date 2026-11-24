import SatinFixedContrastNovember4
import YM.SU5.Assay.OldBrew
import YM.SU5.Assay.Azimuth
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
 Bills and representations of a kiln arsenal of paired stances.
 `A Z s` is the PROPOSED charged stencil itself, engraved at height `s`;
 not a preselection or representative in a quotient. The comparison is
 on exactly those proposals and their whole poses, by the `Fresco`'s
 normalization and rules. Here `l Z s` even gives an alternative pre-pose
 component bill. All supports priced inclusively and uniformly for these
 heights and every implementing posing grid, `t = s` included.
-/
structure Irons :Prop where
 native: ∀ Z s,(A Z s).s=s
 wire: ∀Z s,P.FirstDress (A Z s) Z.2 (l Z s)
 heat: ∀Z,P.Kiln 3 x (A Z) (T Z)

abbrev fore (P:Spine)(A:Lead.Clan → ℕ→P.Apron):= fun Z s=>(A Z s).kiss P 3
abbrev foreword (P:Spine)(l:Lead.Clan→ℕ→P.Folio):=fun Z s=>(l Z s).transcribe (P.reflectTest 3)
abbrev starboard (P:Spine)(x:P.Spectrum0 3)(T:Lead.Clan→P.LagOp 3 x):=fun Z=>P.otherLag 3 x (T Z)

variable {A l T B m U P R x}
lemma Irons.opposed (g:P.Irons x A l T): P.Irons x (P.fore A) (P.foreword l) (P.starboard x T):=
 ⟨g.native,fun _ _=>(g.wire _ _).kiss 3,fun Z=>(g.heat Z).kiss⟩

def Slimmer (P:Spine)(D C:P.Apron):Prop:=∀j,D.realWidth P j<C.realWidth P j
section
variable {D C:P.Apron}
lemma Fades.slim {A':ℕ→P.Apron}(t:P.Fades A')(C:P.Apron):∀ᶠ a in atTop,P.Slimmer (A' a) C:= eventually_all.mpr fun j=>t.one (C.real_width_pos P j) j
namespace Slimmer
variable (h:P.Slimmer D C)
include h
lemma sticker (y:Vantage):P.Aperture D y⊆P.Aperture C y:=fun _ p i=> (p i).trans (h i).le
lemma space (F:SampleDose):P.spacePrice D F⊆P.spacePrice C F:= Set.iUnion₂_mono (fun _ _=>h.sticker _)
-- Strict width pricing at center transferred from any wall; also calipers
variable {F:SampleDose}{a b:ℝ}{j:Axis}
lemma wall (q:Walled j F a b (C.realWidth P j)):Walled j F a b (D.realWidth P j):=q.currency (h j).le
lemma curtain {t:ℕ}{k:ℤ}{w:ℕ}(p:P.FrameFace j t (P.spacePrice C F) a b k w):P.FrameFace j t (P.spacePrice D F) a b k w:= p.covers (h.space _)
end Slimmer
end

namespace Irons
variable (p:P.Irons x A l T)(q:P.Irons x B m U)
variable {F G:SampleDose}{s n:ℕ}{D N:Doorway}{o:Orders}(f:P.Fresco R x s n D N o F G)
local notation "a"=>D.lower 3
local notation "b"=>D.turnCut N
local notation "c"=>N.upper 3
include p
lemma near (F:SampleDose){e:ℝ}(h:0<e):∀ᶠ k in atTop,∀Z,(∀i,(A Z k).realWidth P i<e)∧ P.spacePrice (A Z k) F⊆{y|∃j∈tsupport F.val,∀i,|y i-j i|<e}:=
 eventually_all.mpr fun Z=> (p.heat Z).normal.fades |>.all h |>.and ((p.heat Z).normal.fades.stamp F h)
lemma housed (R:P.Register)(h:tsupport F.val⊆D.spare.invites):∀ᶠ k in atTop,∀Z t,k≤t→ P.Notice x t D (A Z k) Z.2 (l Z k) F:=by
 obtain ⟨u,w⟩:=eventually_atTop.mp (Tickets.late P D)
 refine eventually_all.mpr fun Z=>(((p.heat Z).normal.fades.shelter D).and (eventually_ge_atTop u)).mono fun k v t r=>
    (p.wire Z k).sell x R (by rw [p.native];exact r) h v.1 (w _ (v.2.trans r))
include f q
lemma harvest : ∀ᶠ i:ℕ×ℕ in atTop, s ≤ i.1 ∧ s≤ i.2 ∧∀Z W:Zs,P.Slimmer (A Z i.1) (P.RTest Z s n) ∧ P.Slimmer (B W i.2) (P.FTest W s n)∧
 ∀ t≥max i.1 i.2,P.DuoNotice x t D (A Z i.1) Z.2 (l Z i.1) F N (B W i.2) W.2 (m W i.2) G:=by
 rw [←prod_atTop_atTop_eq]
 have j:=eventually_ge_atTop s
 have y:∀ᶠk in atTop,∀Z,P.Slimmer (A Z k) (P.RTest Z s n):= eventually_all.mpr fun _=> (p.heat _).normal.fades.slim _
 have z:∀ᶠk in atTop,∀W,P.Slimmer (B W k) (P.FTest W s n):= eventually_all.mpr fun _=> (q.heat _).normal.fades.slim _
 filter_upwards [tendsto_fst.eventually ((j.and y).and (p.housed R f.fixed1)),tendsto_snd.eventually ((j.and z).and (q.housed R f.fixed2))] with i l r
 refine ⟨l.1.1,r.1.1,fun Z W=>⟨l.1.2 Z,r.1.2 W,?_⟩⟩
 exact fun t u=>(l.2 Z t (le_of_max_le_left u)).beside R (r.2 W t (le_of_max_le_right u)) f.taps.sep
end Irons
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
