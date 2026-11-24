import Organdy.Flags

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

variable {P:Spine}{c:Cuts}{s:ℕ}
local notation "Y'" => guineas P s
local notation "R✽" => shaft P s
local notation "H" => P.calibration
local notation "w✤" => walkF Y'
local notation "ε'" => yieldt Y'

abbrev firelight (P:Spine)(s v:ℕ):=
  (2*Real.exp 3*pinpr P.par.R.L (guineas P s)/(1+(shaft P s:ℝ))^v)^2

lemma curtains(v:ℕ)(t:0<prismPan P.par.R v Y'):
    Real.exp (bauble P s v)= firelight P s v:=by
 rw [bauble,two_mul,Real.exp_add,Real.exp_add,Real.exp_log (div_pos two_pos t)]
 unfold firelight prismPan
 change (2 / ((1+(shaft P s:ℝ))^v * (pinpr P.par.R.L Y')⁻¹))*_ *Real.exp 6=_
 rw [show (6:ℝ)=3+3 by norm_num,Real.exp_add]
 simp only [div_eq_mul_inv,mul_inv_rev, inv_inv]
 ring


abbrev hue(P:Spine)(s:ℕ):=hueW P.par.R.L (guineas P s)
abbrev sparkle(P:Spine)(s:ℕ)(x:Lot P):= ((hue P s:ℝ):ℂ) • yFin x 
abbrev Orchid(P:Spine)(s v:ℕ)(z:P.Test):Prop:=
 ∀r:ℕ,reach (guineas P s) r→∀j,∀h:P.Spectrum0 j,
  ‖P.singleState j s h ((aureole P.calibration timeAxis (-(r:ℤ)) z)*z)‖ ≤ firelight P s v

variable {I:Type}{l:Filter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
local notation "hue'" => (hue P s:ℂ)
variable (p: Parade l P c d s i k X F x)
include p
lemma bought (z:P.Test)(e:z.val=sparkle P s x):
 Bought l P c s i k
   (hue' • untreated P c s i k X) (hue' • yStart F) z:=by
 constructor
 · rw [e]; exact p.netted _
 apply Eventually.of_forall
 intro r
 let N:=tunnel P s i r
 let f:=fast P s (i r) (k r)
 let S:= Porch f (0:Site N)
 let o:=node (0:Site N)
 let y:=Coral P.par.R.L Y' (tie P s (i r)) f 0 (X r).J (X r).X c.m
 let a:Blush N:=⟨0,y,S,o⟩

 refine ⟨a, ⟨halo_subset _ _ (mem_singleton_self _), _, _, Boarding.home (p.slot r)⟩,?_,rfl⟩
 have u: f.B=R✽:=(p.vintage r).reef.clearing.radius
 intro x b
 obtain ⟨w,g,j⟩:=halo_spec.mp b
 have d:separation 0 w≤1:=by
    rw [mem_singleton.mp g, home0]
    exact sep1
 apply (separation_triangle 0 w x).trans ((add_le_add d j).trans _)
 change 1+2*f.B≤4*R✽+6
 omega

theorem flashbang
  (Z:P.Register)
  [l.NeBot] (m: AmberMood P c s)(t:ε'≤1)(h:1≤d.M):

  ∃ z:P.Test, z.val=sparkle P s x ∧ Orchid P s d.v z:=by

 let z:P.Test:=⟨_,broadCompile _ _ (p.netted hue').queue.toBe⟩
 refine ⟨z,rfl,?_⟩
 intro r j b g
 obtain ⟨u⟩:= nonempty_of_neBot l
 rw [←curtains _ (two_pos.trans_le (p.vintage u).reef.crystal.width)]
 have a:=bought p z rfl
 exact controlled p.vintage p.rate a a (accessible m j).1 (accessible m j).2 m t h Z g
#print axioms flashbang
