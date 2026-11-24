import SatinFixedContrastNovember4
import YM.SU5.Assay.PairSeat
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
/-! Enrollment with one commitment to old F,G on old x,n,s. No presumed
 joint pricing after narrowing nor use of a positive discrepancy as input.
-/
variable {F G:SampleDose}{s n:ℕ}{D N:Doorway}{w:Orders}
local notation "K"=>P.calibration
local notation "X₀"=>P.Test→ₗ[ℂ]ℂ
def Warder (X:X₀):Prop:=Factors K X ∧ (MatterWard K X ∨ GaugeWard K X)
/-- Canonical product of the **actual** pure marginals on the measurement host. -/
lemma canonical (t:ℕ): P.Warder (P.paperSplit t x):=⟨(P.paper_law t x).1.factors,Or.inl (P.paper_law t x).2.2.2⟩
def seatPredict (F G:SampleDose)(A B:Lead.Clan→ℕ→P.Apron)(i j t:ℕ)(X:P.Test→ₗ[ℂ]ℂ):CrossRead:=Matrix.of fun Z W=>
 X (P.markPair (A Z i) (B W j) t F.val G.val)
def seatPrior (F G:SampleDose)(A B:Zs→ℕ→P.Apron)(l m:Zs→ℕ→P.Folio)(i j t:ℕ):CrossRead:=Matrix.of fun Z W=>
 P.PriorBoth x t (A Z i) (B W j) F G (l Z i) (m W j)
structure Assay (s n:ℕ) (D N:Doorway)(w:Orders)(F G:SampleDose)
 (A B:Zs→ℕ→P.Apron)(l m:Zs→ℕ→P.Folio)(T U:Lead.Clan→P.LagOp 3 x):Prop where
 old:P.Fresco R x s n D N w F G
 early:P.Irons x A l T
 late:P.Irons x B m U
variable (D N w s n F G)
-- curried proposition, **conditional on chosen s,F,G etc**, not existential
local notation "b"=>D.turnCut N
local notation "a"=>D.lower 3
local notation "c"=>N.upper 3
local notation "V"=>P.seatPair x (a) (b) (c) F G T U
local notation "W'"=>P.seatStage x (a) (b) (c) F G A B
local notation "γ"=>P.seatGrid R x F G A B
local notation "μ"=>P.seatPredict F G A B
local notation "β'"=>P.seatPrior x F G A B l m
-- Enrolled even when reclaiming actual price discrepancy, late widths
-- (t needn't be any higher than maximum engraving). The whole old
-- experiment may use this posing grid at once or be posed independently.
structure Audit (Gains:Set CrossRead)(i j:ℕ):Prop where
 claims:s≤ min i j
 terminal : V ∈ Gains
 thinner: ∀Z W,P.Slimmer (A Z i) (P.RTest Z s n)∧P.Slimmer (B W j) (P.FTest W s n)
 booked:∀t≥max i j,∀Z W,P.DuoNotice x t D (A Z i) Z.2 (l Z i) F N (B W j) W.2 (m W j) G
 onward:Tendsto (γ i j) atTop (𝓝 (W' i j))
 moving:W' i j ∈ Gains
 already : ∀t≥max i j, γ i j t∈Gains ∧ β' i j t=0 ∧ ∀X:X₀,P.Warder X→μ i j t X=0
-- Audit param auto order P R x A l T B m U F G s n D N ? w **unused**
variable {P R x A B l m T U D N w s n F G}
namespace Assay
variable (p:P.Assay R x s n D N w F G A B l m T U)
include p
lemma walls : Walled 3 F (a) (b) 0 ∧ Walled 3 G (b) (c) 0:=
 ⟨Doorway.first D.noBill p.old.fixed1 p.old.taps.sep,Doorway.second N.noBill p.old.fixed2 p.old.taps.sep⟩
lemma price : Duet γ (W') (V) :=p.early.audition R p.late p.walls.1 p.walls.2
local notation "audit"=> P.Audit R x A l T B m U F G s n D N
lemma earnest {s':Set CrossRead}(y:s'∈𝓝 (V)):∀ᶠi:ℕ×ℕ in atTop,(audit) s' i.1 i.2:= by
 filter_upwards [p.price.earnest y,p.early.harvest p.late p.old] with i h f
 refine ⟨le_min f.1 f.2.1,mem_of_mem_nhds y, fun Z W=>⟨(f.2.2 Z W).1,(f.2.2 Z W).2.1⟩,
   fun _ h _ _=> (f.2.2 _ _).2.2 _ h,h.1,h.2.1,?_⟩
 intro t v
 have h':= fun Z W=>(f.2.2 Z W).2.2 t v
 refine ⟨h.2.2 _ v,?_,?_⟩
 · ext1 Z W; exact (h' Z W).prior
 intro X hx;ext1 Z W; exact (h' Z W).rejects X hx.1 hx.2
lemma opposes (X:ℕ→ℕ→ℕ→P.Test→ₗ[ℂ]ℂ)(c':∀i j t,P.Warder (X i j t)):
 Duet (fun i j t=>γ i j t - μ i j t (X i j t)) (W') (V) ∧ Duet (fun i j t=>γ i j t - β' i j t) (W') (V):=
 let t:=p.earnest univ_mem
 ⟨p.price.congr' (t.mono fun i r=> ⟨rfl,fun t e=>by rw [(r.already t e).2.2 _ (c' ..),sub_zero]⟩),
 p.price.congr' (t.mono fun i r=> ⟨rfl,fun t e=>by rw [(r.already t e).2.1,sub_zero]⟩)⟩
end Assay
namespace Audit
variable {y:Set CrossRead}{i j:ℕ}(p:P.Audit R x A l T B m U F G s n D N y i j)
include p
lemma against (t:ℕ)(v:max i j≤t) (X:X₀)(u:P.Warder X): γ i j t - μ i j t X∈y ∧ γ i j t - β' i j t∈y:= by
 obtain ⟨f,r,g⟩:=p.already t v
 rw [g X u,r,sub_zero];exact ⟨f,f⟩
end Audit
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
