import Organdy.Armet
import Organdy.Intercept
import YM.SU5.Aria.Footpath

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell

open Hive Levier Urn


-- OS views at aligned planes of our sale
open SlabMark
variable (P:Spine)(s:ℕ)
local notation "H" => P.calibration
local notation "σ"=>P.shifts timeAxis
local notation "S"=>station P s

def Aligned(P:Spine)(r q:ℕ):Prop:=(r:ℤ)=ruler (P.calibration.B)*(q:ℤ)
abbrev turned(P:Spine)(r:ℕ)(f:P.Test):= aureole P.calibration timeAxis (-(r:ℤ)) f

variable {r q:ℕ}
lemma switchback (h:Aligned P r q)(f:P.Test):
   P.reflectTest timeAxis (σ q f)= σ q (turned P r f):=by
   let D:=(-(2*(q:ℤ)))
   have e:gaugeT H D= -(r:ℤ):=by
      unfold Aligned ruler at h
      rw [h];unfold gaugeT Heat.gaugeShift D;ring
   rw [P.meetOwn]
   apply Subtype.ext
   change relocate H timeAxis (-(q:ℤ)) (mirror H timeAxis 0 f.val)=relocate H timeAxis (q:ℤ) (mirror H timeAxis (-(r:ℤ)) f.val)
   symm
   let a:= (marque H).mp f.property
   rw [←e, mirror_cancel H timeAxis D 0 a,relocate_sums H timeAxis _ _ (reflect_ok H timeAxis _ a),
      gaugeT_zero]
   rw [show (q:ℤ)+(D - 0)= -(q:ℤ) by unfold D;ring]


def Stamped(P:Spine)(s r q:ℕ)(f:P.Test):Prop:=
 ∃ p:P.birthF timeAxis s (P.shifts timeAxis q f),∀ u:P.Spectrum0 timeAxis,
 (P.singleState timeAxis s u (turned P r f * f)).re =
    ‖P.viewF timeAxis u s p‖^2 ∧
 P.singleState timeAxis s u f =
    inner ℂ (P.colorZero timeAxis u) (P.viewF timeAxis u s p)

lemma cashesView 
  (h:Aligned P r q) (b:Tower.region timeAxis (-(r:ℤ)) P.calibration.ℓ (station P s))
  (f:P.Test)(y:f∈ bay H S true)(x:f∈ enclave H): Stamped P s r q f:=by
 have g:Tower.region timeAxis 0 (H).ℓ (plow H timeAxis q S):=by
   intro k v
   obtain ⟨w,t,rfl⟩:= plow_stays H timeAxis _ _ v
   rw [moves,if_pos rfl,←show (r:ℤ)=_ from h]
   have : -(r:ℤ)+(H).ℓ≤ w timeAxis:=b _ t
   omega
 let p:=P.criteria timeAxis s (P.shifts_support timeAxis q S y) g (P.shifts_keep timeAxis q x)
 refine ⟨p,fun u=>⟨?_,?_⟩⟩
 · rw [←P.slide_single timeAxis u s q, map_mul,←switchback P h, ← P.released_gram _ _ _ p p,
        inner_self_eq_norm_sq_to_K]
   change (((‖P.viewF timeAxis u s p‖ :ℝ):ℂ)^2).re=_
   rw [←Complex.ofReal_pow,Complex.ofReal_re]
 rw [P.view_scalar,P.slide_single]

-- apply
variable {P s}
 {c:Cuts}{I:Type}{l:Filter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
variable (p:Parade l P c d s i k X F x)

abbrev room(P:Spine)(s:ℕ):=bay P.calibration (station P s) true ⊓ enclave P.calibration

lemma labeledInside(j):
 labeled p j∈ room P s:=
 ⟨(p.pins j).1.queue.toBe,(enclave_spec _).mpr (fun m=> ((p.pins j).2.2 m).2)⟩
lemma corsetInside:
 corset p∈ room P s:=
 let T:=room P s
 T.add_mem (labeledInside p _) (T.sum_mem fun j _=>T.sub_mem
    (labeledInside p (.plus j)) (labeledInside p (.minus j)))

/-- Prices interpret as squared OS view norms, including the means for centering.
On aligned planes use this with LoneBeacon and Orchid. -/
theorem paidViews
 (m:Grand P c s)
 (o:reach (guineas P s) r)(n:Aligned P r q)
 (a:ℂ):
 Stamped P s r q (a • vivid p) ∧ Stamped P s r q (a • corset p):=
 let g:= inRegion r (m.path r o).2.2
 let h:=(room P s).smul_mem (labeledInside p .horn) a
 let y:=(room P s).smul_mem (corsetInside p) a
 ⟨cashesView P s n g _ h.1 h.2, cashesView P s n g _ y.1 y.2⟩

#print axioms paidViews
