import Organdy.Banquet
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra

open _root_.Zephyr.Chern
open Vale Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Yoke Yoke.Bazaar
open Optic Larva -- remove

namespace Royal
open Buffered.Afterglow Satin Journey Tower

/- moving planes limiting horn -/

section
variable {K:Calibration}
abbrev shadow (K:Calibration)(d:ℕ)(u:ℝ)(F:Buffered.Family K):=
  let T:=(u:ℂ) • F
  Tower.mirror K timeAxis (-(d:ℤ)) T*T
abbrev haloS (d:ℕ)(S:Finset Cover):=reflectedBox timeAxis (-(d:ℤ)) S∪ S
lemma penny {n:Side}(L:Scree.Loom n)(q:BudgetPoint)(z:SOp n)(u:ℝ):
 (u:ℂ) • haloMark L q z=plateM (scint L q z) u:=by
 funext U; exact (smul_smul (u:ℂ) _ _)
end

variable {I:Type}{l:Filter I}{P:Spine}{s:ℕ}{c:Cuts}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
 (p:Parade l P c d s i k X F x)
local notation "Y" => (guineas P s)
local notation "H"=> P.calibration
local notation "S" => station P s
abbrev raw (P:Spine)(s:ℕ)(i k:I→ℕ) (X:Suits P s i) (v:I):=
 scint (tie P s (i v)) (fast P s (i v) (k v)) (X v).X

local notation "W" =>raw P s i k X
include p
lemma Parade.policy (v:I):Policy P.run (gleamδ c.γ) s (i v) (k v) (W v):=
 ((p.vintage v).fil.classic _ _ _ _ (p.slot v).toSquid.toKit).2


lemma Parade.plated (q:ℕ)(u:ℝ):
 Gallon l P s i (haloS q S) (fun v=>planeM (W v) u q)
    (fun v=>shadow H q u (F .horn v)) (shadow H q u (x .horn)):=by
 let b:=(p.pins .horn).1.scale (u:ℂ)
 have b':= (b.revolve timeAxis (-(q:ℤ))).product b
 refine ⟨b'.queue,fun r=>?_⟩
 let t:= tie P s (i r)
 let g:= fast P s (i r) (k r)
 let H0:= (u:ℂ) • haloMark t g (X r).X
 refine Eq.trans (b := reflMark timeAxis (-(q:ℤ)) H0 * H0) (b'.sees r) ?_
 unfold H0; rw [penny]; exact rfl

lemma Parade.blow (q:ℕ)(u:ℝ):
 InTest H true (haloS q S) false (shadow H q u (x .horn))∧
 Tendsto (fun v=>Journey.compass P.run (i v) (k v) s (planeM (W v) u q)) l (𝓝 (P.E s (shadow H q u (x .horn)))):=
 ⟨(p.plated q u).queue.toBe,(p.plated q u).pays p.rate⟩

def haloPrice (P:Spine)(s:ℕ)(γ:ℝ)(f:Buffered.Family P.calibration):Prop:=
 ∀ q,reach (guineas P s) q→∀ u β:ℝ,guineas P s/2≤β→ gleamδ γ*(u/(β*(distanceP q)^4))^2≤
    (P.E s (shadow P.calibration q u f)).re

theorem Parade.crowning [l.NeBot]:
 haloPrice P s c.γ (x .horn):=fun q h u β a=>
 ge_of_tendsto ((Complex.continuous_re.tendsto _).comp (p.blow q u).2)
 (Eventually.of_forall fun r=>(p.policy r).plan q h u β a)


abbrev untreated (P:Spine)(c:Cuts)(s:ℕ)(i k:I→ℕ)(X:Suits P s i) :=
  fun z=>Yc (tie P s (i z)) (fast P s (i z) (k z)) 0 (X z).J (X z).X c.m

lemma Parade.netted (u:ℂ):
 Gallon l P s i S (u • untreated P c s i k X)
     (u • yStart F) (u • yFin x):=
 (Royal.netted (fun j=>(p.pins j).1)).scale u

lemma Parade.yBill(u:ℂ):
 Tendsto (fun z=>Journey.compass P.run (i z) (k z) s (u • untreated P c s i k X z)) l (𝓝 (P.E s (u • yFin x))):=
 (p.netted u).pays p.rate
#print axioms Parade.crowning
#print axioms Parade.yBill
