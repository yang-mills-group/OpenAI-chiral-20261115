import Velour.Organza.Nursery
import Mathlib.Analysis.InnerProductSpace.LinearPMap
/-! Mathlib-closability -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight

local notation "E" => S.E
local notation "G" => S.heatL

local notation "U" => S.unit.translation
local notation "M" => S.liftL


def animal (X:Module.End ℂ D) : H.space →ₗ.[ℂ] H.space where
 domain:=D
 toFun:=S.muslin.subtype.comp X


lemma dense_animal (X:Module.End ℂ D) :
 Dense ((S.animal X).domain:Set H.space):= S.muslin_dense

variable {S}
variable {X Y:Module.End ℂ S.muslin}
lemma Faces.formal (h:S.Faces X Y) :
 (S.animal X).IsFormalAdjoint (S.animal Y):= h

lemma Faces.cocoon (h:S.Faces X Y): (S.animal X).IsClosable:=
 (LinearPMap.adjoint_isClosed (S.dense_animal Y)).isClosable.leIsClosable
     (h.symm.formal.le_adjoint (S.dense_animal _))

lemma pocket_closed_up {κ:Type} {J:κ→ℝ≥0→H.Op}{T:κ→S.Detector}
 (h:S.Fray J T)(O:Set E4)(e:X∈pocket T O):
 (S.animal X).IsClosable:=
 let q:=(pocket_faces h O e).2
 q.choose_spec.2.cocoon

#print axioms pocket_closed_up

