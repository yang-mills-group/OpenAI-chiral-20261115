import Lucent.Sensor
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition

open Spine Preparation.Yoke Lucent EmberWind
variable (P:Spine)
local notation "Ξ" => household (P.calibration)
local notation "φ" => P.groundZero 3
local notation "Kₚ" => P.calibration

universe v0
variable {I:Type}[Fintype I]
variable {β:ℕ→ℝ}{R:ℕ→ℝ}{r:ℕ→ℕ}
variable {W:ℕ→I→Staff} {S:Stencil I} {m a:ℕ}{b:ℕ→ℕ}{d:FieldPlan I}
local notation:max "gong" => soundOf P β R W b S m a
local notation "mu" => P.pillars 3

open Preparation.Yoke.Lucent.Arity
namespace Banner
variable {P}
variable (h:Banner I P)(z: Window.Family)

open Carillon Ballad
local notation:max "R@" => h.R
abbrev thermo(P:Spine)(s:ℕ):=Pressure.temp (Vale.hat P.par.R.L P.par.x s)
abbrev myCost(β:ℕ→ℝ)(s:ℕ):=Jewel.κFix β s
def extent(h:Banner I P)(s:ℕ)(i:I):=(h.W s i).skyRent (h.b s)
def bilateral(h:Banner I P)(s:ℕ):=h.extent s h.u ∪ h.extent s h.v
variable (β)(s:ℕ)

structure EnvelopeS(h:Banner I P)(β:ℕ→ℝ)(s:ℕ):Prop where
  permit :∀i,∃w,(h.W s i).Pays (h.b s) w
  v_stock: ∀i, InTest P.calibration true (h.extent s i) false (h.tintC β i s).val
  v_price: ∀i,(h.tintC β i s).val=maxZoom (h.R s) 1 1 •Ξ ((h.W s i).rungWeave (myCost β s) (h.b s) (thermo P s))
  d_stock: ∀z, InTest Kₚ true (h.extent s h.k) false (h.axialC β z s).val
  d_price: ∀z,(h.axialC β z s).val=maxZoom (h.R s) 0 1 •Ξ (SitSpin.raw (h.W s h.k).u z (h.W s h.k).spin.1 (h.W s h.k).spin.2)
  g_cap: ∃x, Coeff true (h.bilateral s) x ∧ (h.shearC β s).val=scalar Kₚ x

abbrev ker (S:Stencil I)(m a:ℕ):=Ξ (soundOf P β h.R h.W h.b S m a s)
#check @lodgeD
#check @ker
#check @lodgeG
lemma envelopes : ∀ᶠ s:ℕ in atTop,h.EnvelopeS β s:=by
 obtain ⟨B,l,q⟩:=h.bill
 have f:∀ᶠ s in atTop,∀i,(h.tintC β i s).val = Ξ (soundOf P β h.R h.W h.b (Arity.V i) 1 1 s):= Filter.eventually_all.mpr fun i=> (h.tintB β i).matched
 have g:∀ᶠ s in atTop,∀z,(h.axialC β z s).val = Ξ (soundOf P β h.R h.W h.b (Arity.D z h.k) 0 1 s):=Filter.eventually_all.mpr fun z=>(h.axialB β z).matched
 filter_upwards [q,f,g,(h.shearB β).matched] with s p v d r
 let u:=myCost β s; let t:=thermo P s
 have ht(i):= lodgeV (h.b s) u t (h.extent s i) Kₚ (h.R s) (h.W s) _ i (p.paid i) Subset.rfl
 have hx(z):= lodgeD (h.b s) u t (h.extent s h.k) Kₚ (h.R s) (h.W s) _ z (pav_mono (show h.b s ≤ h.b s+8 by omega) ((p.paid h.k).node _))
 constructor
 · exact fun _=>⟨_,p.paid _⟩
 · intro i; rw [v]; exact (ht i).2
 · intro i; rw [v]; exact (ht i).1
 · intro z;rw [d];exact (hx z).2
 · intro z;rw [d];exact (hx z).1

 rw [r]
 exact lodgeG (h.b s) u t (h.bilateral s) Kₚ (h.R s) (h.W s) _ h.u h.v (p.paid h.u) (p.paid h.v) subset_union_left subset_union_right

lemma EnvelopeS.gauge (e:h.EnvelopeS β s): Six.PureGauge Kₚ (h.shearC β s)∧InTest Kₚ true (h.bilateral s) false (h.shearC β s).val:= by obtain ⟨x,k,u⟩:=e.g_cap; exact ⟨⟨_,_,k,u⟩,u.symm ▸ (show InTest Kₚ true _ false _ from InTest.seed k)⟩
lemma EnvelopeS.axial (e:h.EnvelopeS β s): Six.PureMatter Kₚ (h.axialC β z s):=by
 unfold Six.PureMatter; rw [e.d_price]; exact fun _ _ _=> rfl
