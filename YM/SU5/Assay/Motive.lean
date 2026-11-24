import SatinFixedContrastNovember4
import YM.SU5.Assay.Paintings
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
-- PRE argument order for future
open DoseTravel TopologicalSpace
variable {P R x A B l m T U}{D N:Doorway}{s n:ℕ}{o:Orders}
variable {F G:SampleDose}{f g:ℕ→SampleDose}{i j t:ℕ→ℕ}
variable (p:P.Assay R x s n D N o F G A B l m T U)
local notation "a"=> D.lower 3
local notation "b"=> D.turnCut N
local notation "c"=> N.upper 3
local notation "R1"=>litRow 3 a b 0
local notation "R2"=>litRow 3 b c 0
/-! Account on any qualifying heights. -/
local notation "γ"=>P.seatGrid R x
local notation "V"=>P.seatStage x (a) (b) (c)
local notation "ξ"=>P.seatPair x (a) (b) (c)
structure Motive (P:Spine)(s n:ℕ)(A B:Lead.Clan→ℕ→P.Apron)(i j:ℕ):Prop where
 high:s ≤ min i j
 thin : ∀Z,P.Slimmer (A Z i) (P.RTest Z s n)
 fine : ∀Z,P.Slimmer (B Z j) (P.FTest Z s n)
namespace Assay
include p
local notation "ν"=>P.Motive s n A B
lemma qualifies (hi:Tendsto i atTop atTop)(hj:Tendsto j atTop atTop):∀ᶠk in atTop,ν (i k) (j k):=by
 have q:Tendsto (fun k=>(i k,j k)) atTop atTop:=by rw [←prod_atTop_atTop_eq];exact hi.prodMk hj
 filter_upwards [q.eventually (p.early.harvest p.late p.old)] with k u
 exact ⟨le_min u.1 u.2.1,fun Z=>(u.2.2 Z Z).1,fun Z=>(u.2.2 Z Z).2.1⟩
variable {i' j':ℕ}
variable (q:P.Motive s n A B i' j')
include q
local notation "I" Z:max => (A Z i')
local notation "L'" Z:max => (B Z j')
lemma repeats (Z W:Zs)(t:ℕ)(v:max i' j'≤t):P.DuoNotice x t D (I Z) Z.2 (l Z i') F N (L' W) W.2 (m W j') G:=by
 have h:= p.old.taps
 have ht:s≤t:= (le_of_le_min_left q.high).trans (le_of_max_le_left v)
 have h₁:D.Stash ((I Z).realWidth P):=fun i=> (q.thin Z i).le.trans (h.left i)
 have h₂:N.Stash ((L' W).realWidth P):=fun i=> (q.fine W i).le.trans (h.right i)
 have i:= (p.early.wire Z i').sell x R (t:=t) (by rw [p.early.native]; exact le_of_max_le_left v) p.old.fixed1 h₁ (h.bills _ ht).1
 have j:= (p.late.wire W j').sell x R (t:=t) (by rw [p.late.native]; exact le_of_max_le_right v) p.old.fixed2 h₂ (h.bills _ ht).2
 exact i.beside R j h.sep
local notation "vac"=>P.colorZero 3 x
lemma exposed (Z W:Zs)(t:ℕ)(v:max i' j'≤t):(γ F G A B i' j' t) Z W=
 inner ℂ (vac) ((σ t (I Z) (a) (b) F * σ t (L' W) (b) (c) G) (vac)):=by
 change P.spiritBoth R x t (I Z) F (L' W) G = _
 rw [P.spirit_pair]
 exact ((p.repeats q Z W t v).stance 3 (a) (b) (c) x ((q.thin Z).wall p.old.old_walls.1) ((q.fine W).wall p.old.old_walls.2)).price.symm
lemma proceeds:Tendsto (γ F G A B i' j') atTop (𝓝 (V F G A B i' j')):=by
 have w:=P.grid_base _ _ (P.metered 3 x R)
 exact tendsto_pi_nhds.mpr fun Z=>tendsto_pi_nhds.mpr fun W=>
 (((w (I Z) (a) (b) F).mul (w (L' W) (b) (c) G)).price.congr'
 ((eventually_ge_atTop (max i' j')).mono fun t v=>(p.exposed q Z W t v).symm))
lemma paints {Gain:Set CrossRead}(u:ξ F G T U∈Gain)(v:V F G A B i' j' ∈ Gain)
 (h:∀t≥max i' j',γ F G A B i' j' t∈ Gain): P.Audit R x A l T B m U F G s n D N Gain i' j':=by
 refine ⟨q.high,u,fun _ _=>⟨q.thin _,q.fine _⟩,fun _ v _ _=>p.repeats q _ _ _ v,p.proceeds q,v,?_⟩
 intro t y; refine ⟨h t y,?_,?_⟩
 · ext1 Z W;exact (p.repeats q Z W t y).prior
 intro X hx;ext1 Z W; exact (p.repeats q Z W t y).rejects X hx.1 hx.2
end Assay
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
