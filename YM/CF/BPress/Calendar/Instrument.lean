import YM.CF.BPress.Calendar.Muse
import YM.CF.BPress.Homes.Industry
/-! Construction of actual marks on ONE V/H stop. All Props except Recipe, Edition and Extends.
 Pay any choice of Calyx extension meeting eq:B-Ms. This record makes the observables from
 the actual fields, no dummy replacements of regulator or comparator. Production uniform in budget
 x prechoices, V, fuel h. In this file x denotes y still.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Calendar
open Function NormedSpace Metric Finset MeasureTheory Filter Lattice RG Precision Pressure
open Cube Py Vale Vale.Grace Paige Scree Skye Fixed Dial Spire SU Wilson
open Net Hazel Chrono Sugar Sugar.Crew Lilac Grid Mount Recital Habitat Driver Meadow Meadow.Tent Meadow.Frame Meadow.Stamps Locale
open Wealth Weave Port Honey Before Between Recipe RG.PathData Branch LocalH Next.SectorChange Peel Spine Mosaic Huon Spin Manna
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace YM.CF.BPress.Habitat.Driver YM.CF.BPress.Vesper
attribute [local instance] Gauge.frobInner
variable {m s B:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K R L} {d x h p c:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} {J:Robes Mstar V W}
variable {P:Before V p}{X:P.Between d J.n} {f: Angel X}{E:Earning X}{D:Day E}
open Around Day Currencies Fock -- tune.
variable {A:Bands (More (mid m B)) (era X x)} {T: GramM (mid m B)} {Z:Loom (mid m B)}
variable (M:Mantle (x:=x) V J h m T Z)(hT:Time D.curb D.gain x)(v: D.Appear x A)
abbrev Cue := Currencies.crew V A v.grid' v.angle hT.stamp.high.pace.age M -- order
abbrev atPhase (_M:Time D.curb D.gain x)(v:D.Appear x A):= exhibit X v.grid
open Sugar.Stage
local notation "S"=> Stage.Stamp -- ugly
lemma rented_t : Rented (Appear.Q D v) (Cue M hT v) (atPhase hT v) (launch X T).d J.k J.n (sbo D.angel x):= hT.stamp.high.pace.night M v.grid v.grid' v.angle (Appear.age D v)
structure Instrument where
 gas:Recipe (A:=A) T
 pen: gas.M = D.angel.r x
 caps:gas.C = K.top.paths
 horizon : Budgeting (Cue M hT v) gas (D.angel.a x) (D.angel.k x) D.angel.η D.angel.ζ D.angel.Jr D.angel.Jc
 stamp : S A (Appear.Q D v) (atPhase hT v) (launch X T)
 bond : Wish (launch X T) P.H (First V) (Second V)
 spin : Edition (launch X T)
 stage : Passports (launch X T) T (drama U T) bond spin (value E) (p/2) E.t (g x) (limit E x) (Between.stipend E x)
 chills : Calyx spin (ΓStage (rented_t M hT v) stamp)
 /-- Borel version of the cancellations on full Pose pricing domain. -/
 extension : Homes.Sealbook (ΓStage (rented_t M hT v) stamp) chills
-- instantiate. T.Beta might use Xi.Is.
lemma instrument (z:d ≤ P.dcap)(t:p ≤ W.pearl.q)(c:Between.height E ≤h)(s:T.p.B=radiusB x)(f:T.p.supportExponent=1): Nonempty (Instrument M hT v):=by
 let α:=hT.stamp.high.pace.age; obtain ⟨g,k,a,b⟩:= α.recipe V A M v.grid' v.angle; let n: X.n ≤ (mid m B).val:= (le_max_left ..).trans v.size; let L:=post z M n; let S':= exhibit X v.grid; let Q:=Appear.Q D v; let Y:= launch X T; have ht: Stamp A Q S' Y:= stamps z A Q v.grid t n L; obtain ⟨T₁,S_⟩:= horoscope E M L hT.stamp.high.road c f s -- tune shadow
 obtain ⟨u,p⟩:= Homes.portfolio (ΓStage (rented_t M hT v) ht) S_; exact ⟨⟨g,a,b,k,ht,L,T₁,S_,u,p⟩⟩
namespace Instrument
variable {M hT v}
variable (P0:Instrument M hT v)
abbrev wreath := formula P0.gas (Cue M hT v) (design (rented_t M hT v) P0.stamp P0.chills)
def pencil (i:A.Index) : Fixed.Test (mid m B):= Net.showM A (Cue M hT v).Z i (P0.wreath i) -- tuning
abbrev Score (p:List A.Index) := Net.shows A (Cue M hT v).Z p P0.wreath
lemma marks (i:A.Index): YM.CF.BPress.Extends (Cue M hT v).Z A i (P0.wreath i) (cashmark P0.gas (D.angel.k x) (value E) (Between.stipend E x) i):= Honey.marks P0.horizon P0.chills P0.stage (rate_pos E x).le i
lemma shapes (i:A.Index): IsMark (A.band i) (P0.pencil i) (Real.exp (D.gain*x^2*((More (mid m B)).val:ℝ)^3)):=
 let h':= (Cue M hT v).Z.show_mark A i _ (P0.marks i) hT.stamp.high.pace.age.plenty.plenty.coast
 h'.weaken le_rfl (hT.o _ _ A T i _ M.cash P0.caps M.hill)
-- signature Pin f includes DATA.Value;
variable (t:p≤W.pearl.q)
variable (℘: List A.Index)(q: ℘.Nodup)(b:∀ i,i∈℘)
include t q b
lemma pinD : Pin P0.chills ℘ (rescaleOffset U T Z) (T:=T) (ε:=g x):=by
 let L':= Cue M hT v; let Y:= launch X T; refine ⟨Law.powerP (Law.fixedP (Complex.exp (-T.v))) (M.registered V J h), q,b,?_⟩; exact Crew.event U T X.R X.ε (rented_t M hT v) P0.stamp W.pearl (payPe (P:=P) t) V.note P.ν.above M.rest P0.stage P0.chills M.fund (g_pos hT.stamp.high.pace.age.yPos) ℘ q b -- tune namespace and signs

lemma lower : Real.exp (-(D.gain*x^2)*((More (mid m B)).val:ℝ)^4) ≤ ‖ (Cue M hT v).Z.lantern A ℘ P0.wreath (rescaleOffset U T Z)‖:=by
 let X':=atPhase hT v; let H':= hT.stamp.high.pace; let α:= H'.age; let F:=rented_t M hT v; let T':= Cue M hT v; let Q:=Appear.Q D v; let j:= born_t A Q v.grid (sb_pos α).le α.plenty.weight F.dusk P0.stamp; have bO:=hT.stamp.currencies M v.grid v.grid' v.angle (Appear.age D v) P0.bond ((le_max_right ..).trans v.size) j _ P0.caps P0.pen; -- tune
 let z':=(More (mid m B)).val; have h:= Manna.Budget.output P0.stage P0.horizon bO P0.chills ℘ (rescaleOffset U T Z) (pinD P0 t ℘ q b); refine le_trans (Real.exp_monotone ?_) h; rw [M.cash,P0.caps]; exact mul_le_mul_of_nonneg_right (neg_le_neg hT.u) (by positivity)
end Instrument
end YM.CF.BPress.Calendar
