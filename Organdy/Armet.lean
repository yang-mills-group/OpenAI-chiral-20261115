import Organdy.Cornet

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



variable {P:Spine}{c:Cuts}{s:ℕ}
 {I:Type}{l:Filter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
local notation "Hp"=> P.calibration
local notation "B"=> shaft P s
local notation "Hₛ"=>station P s
variable (p:Parade l P c d s i k X F x)



/-- All terms raw. -/
abbrev tenor(a:Axis):=labeled p (.axis a)
abbrev cadet:=labeled p .stone
abbrev vivid:= labeled p .horn
def corset:P.Test:=
 cadet p + ∑ j:Axis,(labeled p (.plus j)-labeled p (.minus j))

lemma corsetVal: (corset p).val=yFin x :=by
 let r:Dome Hp →ₐ[ℂ] Buffered.Family Hp:=(screenHall Hp).val
 change r (corset p)=_
 rw [corset,map_add,map_sum]
 unfold yFin
 simp only [map_sub];rfl

variable [l.NeBot]
lemma corsetPaid (w:0≤c.a):
  corset p=cadet p + ventilate Hp c.m (tenor p):=by
 unfold corset ventilate
 change _=cadet p+ ∑ j:Axis, twoSide Hp (gstride c.m j) (labeled p (.axis j))
 congr 1
 refine sum_congr rfl fun j _=>?_
 rw [twoSide,LinearMap.sub_apply, (doubleReach p w j).1, (doubleReach p w j).2]

lemma ode(w:0≤c.a)(z:ℂ):
 pauldron Hp (z • corset p)= z • vivid p + ventilate Hp c.m (z • hatAxis (tenor p)):=by
 rw [corsetPaid p w,map_smul,map_add,show pauldron Hp (cadet p)= vivid p from paidStar p,
    voiced,smul_add,map_smul]

#print axioms ode
#print axioms clampAccess
