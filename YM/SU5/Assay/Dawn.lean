import SatinFixedContrastNovember4
import YM.SU5.Assay.EntranceFee
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
variable (s n:ℕ)(D N:Doorway)(o:Orders)(F G:SampleDose)(M:P.Menagerie)
local notation "ƛ"=> P.visor x M
local notation "ψ"=> P.starboard x ƛ
local notation "a"=>D.lower 3
local notation "b"=>D.turnCut N
local notation "c"=>N.upper 3
local notation "Ψ"=> P.seatPair x a b c F G
local notation "V"=> Ψ ψ ƛ
/-!
 `Dawn`. First estimates using the contact test. Margin on the RAW
 comparison common to the user and review commitments. This response
 hasn't retained the verified connected purchase; it's rank at most
 one, all prices of the limiting operators shown here are as for
 multiples of the unit insertion. Not yet solving the thin fields
 objective. Even pricing in the new arms reuses **independent**
 intrinsic width removals; contact purchase is made with literal
 original front coefficients and housing rules (possible resizes of
 plank budgets are explicit).
-/
abbrev Bearings
 (B:Lead.Clan→ℕ→P.Apron) (m:Zs→ℕ→P.Folio)(U:Zs→P.LagOp 3 x):Prop:=
 P.Assay R x s n D N o F G (P.fore B) B (P.foreword m) m (P.starboard x U) U
def Blooms (B:Zs→ℕ→P.Apron)(m:Zs→ℕ→P.Folio): Prop:=
 P.Bearings R x s n D N o F G B m ƛ ∧ ∀ᶠi:ℕ×ℕ in atTop,
  P.Audit R x (P.fore B) (P.foreword m) ψ B m ƛ F G s n D N lobby i.1 i.2
abbrev Sunset :Prop:= P.Bearings R x s n D N o F G (P.replayBody n) (P.replayBook n) 0
-- Note **before** choosing the particular portals, at this particular
-- height s,n of the strategy all Dawn claims hold; even the medals
-- themselves (with n by the successful launch) can be preselected.
structure Dawn :Prop extends P.Fresco R x s n D N o F G where
 flock : P.Company n M (1/2)
 rise:P.Blooms R x s n D N o F G M (P.refront n) (P.togetherBook n)
 carrier:P.Blooms R x s n D N o F G M (P.borne M) (P.borneBook M)
 desk : V=P.fee M
 fades:P.Sunset R x s n D N o F G
 lost: Ψ (P.starboard x 0) 0=0

variable {P R x F G s n D N o M}
lemma null_brew {d e:ℝ}(h:Walled 3 F d e 0):κ 0 d e F=0:=by
 have u:=coffee_scale (P.unit_credits 3 x) h 0
 simpa only [zero_smul] using u
lemma null_starboard : P.starboard x 0=0:=by
 funext;exact star_zero _

lemma Fresco.dawn (g:P.Fresco R x s n D N o F G)(h:Tasting.Paid P.par)(p:P.Company n M (1/2)): P.Dawn R x s n D N o F G M:=by
 obtain ⟨q,t⟩: Walled 3 F a b 0 ∧ Walled 3 G b c 0:=
    ⟨Doorway.first D.noBill g.fixed1 g.taps.sep,Doorway.second N.noBill g.fixed2 g.taps.sep⟩
 have e:V=P.fee M:=P.fee_value _ _ q t g.oil g.water
 have l:lobby∈𝓝 V:= by rw [e];exact lobby_open.mem_nhds p.fee_entry
 have H:∀{B m},P.Irons x B m ƛ→ P.Blooms R x s n D N o F G M B m:=by
    intro X k E;let v:P.Bearings R x s n D N o F G X k ƛ:=⟨g,E.opposed,E⟩
    exact ⟨v,(Assay.earnest v l)⟩
 have v:=P.wane R x h g.taps.extent
 refine ⟨g,p,H (p.refront P R x),H (P.how_borne R x M),e,⟨g,v.opposed,v⟩,?_⟩
 rw [null_starboard];ext1 Z W;change inner ℂ Ω ((κ 0 _ _ _ * κ 0 _ _ _) Ω)=0
 rw [null_brew q,zero_mul];change inner ℂ Ω 0=0;simp

variable {i j t:ℕ}
namespace Dawn
variable (g:P.Dawn R x s n D N o F G M)
local notation "B₀"=>P.refront n
local notation "A₀"=>P.fore B₀
local notation "M₀"=>P.seatGrid R x F G A₀ B₀
local notation "ζ"=>P.seatStage x a b c F G A₀ B₀
local notation "π"=>P.seatPredict F G A₀ B₀
include g
lemma hits : Duet M₀ ζ (P.fee M):= by rw [←g.desk];exact g.rise.1.price
lemma overtakes : ∀ᶠ i:ℕ×ℕ in atTop,∀t≥max i.1 i.2, M₀ i.1 i.2 t∈lobby ∧ M₀ i.1 i.2 t - π i.1 i.2 t (P.paperSplit t x) ∈lobby:=by
 filter_upwards [g.rise.2] with i I t h; exact ⟨(I.already t h).1,(I.against _ h _ (P.canonical ..)).1⟩
end Dawn
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
