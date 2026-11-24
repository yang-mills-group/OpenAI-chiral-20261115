import Merino.Plume.Glue
import Merino.Plume.Ivory
import Merino.Plume.Shell
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Plume
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered Buffered.Lifted StressExchange Dial
variable {m:ℕ}


variable {B:BudgetPoint}{a b d τ:ℝ}{W:Scree.Loom n}{o:Seat n}{X:SOp n}
variable (r:Skylit B d W)(ha:0≤a)(h:Trunk o X (B.B/10) a b d)
def fitted (m:ℕ)(o:Seat n)(B:BudgetPoint):Prop:=
   m+1<n.val ∧ casing B o ⊆ purse m 0
variable (g:fitted m o B)
include r ha h g
lemma cut:LocalOn (purse m (0:Seat n)) (traceCost W B o X):= by
 exact fun _ _ t=>congrArg Matrix.trace (mask_local r ha h _ _ (agrees_mono t g.2))

structure Still (m:ℕ)(τ b d:ℝ)(F:LinksC→ℂ):Prop extends Swan (Lattice.box m) b F where
  sport (x y) :quiz m τ x=quiz m τ y→dist (F x) (F y)≤ cable m b d * dist (echoC m x) (echoC m y)
lemma closed_dark(p:B.threshold=τ):Still m τ b d (takeDark W B o X m):=by
 refine ⟨⟨?_,local_dark (cut r ha h g) g.1,
     sang_dark (cut r ha h g) g.1 ?_,fun _=>mask_trace r ha h _⟩,fun x y=> joins_trace r ha h p⟩
 · have t: Continuous (Matrix.trace:Op I→ℂ):=by fun_prop
   exact t.measurable.comp ((mask_meas r h.pay).comp darkC.measurable)
 intro k x
 unfold traceCost
 rw [mask_gauge r ha h,trace_twist]
lemma cut_period(x:Pane n): takeDark W B o X m (onC n x)=traceCost W B o X x:=
 periodic (cut r ha h g) x


omit r ha h g

variable {S:Finset Cover}{F:ℕ→LinksC→ℂ}{f:LinksC→ℂ}
def Plump (S:Finset Cover)(b:ℝ)(F:ℕ→LinksC→ℂ)(f:LinksC→ℂ):Prop:=
 (∀ j,Swan S b (F j)) ∧ spray F f
lemma fat (t:Plump S b F f):Swan S b f:=by
 have l:=t.2.rise
 refine ⟨measurable_of_tendsto_metrizable (f:=F) (fun n=>(t.1 n).reads) (tendsto_pi_nhds.mpr l),
   fun X Y h=>?_,fun g x=>?_,fun V=>le_of_tendsto' (l V).norm (fun i=>(t.1 i).bound V)⟩
 · exact tendsto_nhds_unique (l X)
    ((l Y).congr fun i=> ((t.1 i).region X Y h).symm)
 exact tendsto_nhds_unique (l (gauge g x)) ((l x).congr fun i=> ((t.1 i).sang g x).symm)
lemma bauble (t:∀ j,Still m τ b d (F j)):
    ∃ (r:ℕ→ℕ)(g:LinksC→ℂ),StrictMono r ∧ Plump (Lattice.box m) b (F∘r) g:=by
 obtain ⟨r,g,v,z⟩:= feather (q:=quiz m τ) (echoC_bounded m) (cable_pos m (t 0).nonneg d)
   (fun j=>(t j).sport) b (fun j=>(t j).bound)
 exact ⟨r,g,v,fun i=>(t _).toSwan,z⟩
end YM.CF.Merino.Plume

