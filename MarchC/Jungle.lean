import MarchC.Back
import Crape.Creature
import Preen.Fitted
import SatinLocalChron
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
open Calico
variable(P:Spine)(F:ℕ)
local notation "K"=>P.calibration
local notation "Lx"=>P.par.R.L
local notation "R"=>ruler P.par.block
-- centers positive and negative.Neat. explicit. uses rooted measured nodes
noncomputable abbrev rifle(s:ℕ)(o:Cover)(i:Axis):ℤ:= -((nodeC o i - (minB P s:ℤ))/R)
noncomputable abbrev sit(s:ℕ)(o:Cover):= metro P (rifle P s o) o
noncomputable abbrev downR(s:ℕ)(o:Cover)(i:Axis):ℤ:= ( (-nodeC o i - (minB P s:ℤ))/R)
noncomputable abbrev bow(s:ℕ)(o:Cover):= metro P (downR P s o) o
lemma ride(s:ℕ)(o:Cover)(i:Axis): (minB P s:ℤ) ≤nodeC (sit P s o) i ∧ nodeC (sit P s o) i ≤ reachQ P s:=by
 rw [sit,metro_cal,pages]; let t:ℤ:=minB P s; let x:=nodeC o i; have e:=Int.emod_add_mul_ediv (x-t) (R); have u:=ruler_gene P.par.block
 change t ≤ x + (R)*(-((x-t)/R)) ∧ _ ≤t+R; rw [mul_neg]; have w:= Int.emod_lt_of_pos (x-t) u; have p:=Int.emod_nonneg (x-t) u.ne'; omega
lemma tilt(s:ℕ)(o:Cover)(i:Axis): (minB P s:ℤ) ≤ -nodeC (bow P s o) i ∧ -nodeC (bow P s o) i ≤ reachQ P s:=by
 rw [bow,metro_cal,pages]; let t:ℤ:=minB P s; let x:= -(nodeC o i); have e:=Int.emod_add_mul_ediv (x-t) (R); have u:=ruler_gene P.par.block
 unfold downR; change t ≤ -(nodeC o i+R*((x-t)/R)) ∧ _ ≤t+R; have w:= Int.emod_lt_of_pos (x-t) u; have p:=Int.emod_nonneg (x-t) u.ne'; dsimp only [x,t] at *; omega
-- generic cover projection shift between generations & exact gridmarket
lemma swingZ(s j:ℕ)(o y:Cover): orbitB Lx (metro P y o) (s-j)= metro P (fun i=>(Lx).val^(s-j)*(y i)) (orbitB Lx o (s-j)) := by
 apply node_dC; ext i
 rw [dutyT _ _ P.par.R.odd_side,metro_cal,dutyT _ _ P.par.R.odd_side]
 simp only [Pi.smul_apply,nsmul_eq_mul]; rw [metro_cal]; push_cast; ring
lemma hingeZ (o y z:Cover): metro P (z-y) (metro P y o)=metro P z o:=by
 apply node_dC; ext i; rw [metro_cal,metro_cal,metro_cal]; simp only [Pi.sub_apply]; ring
noncomputable abbrev zap(a:Axis)(o:Cover):Cover:= (plane a 0).flee o
lemma zap_node (a i:Axis)(o:Cover): nodeC (zap a o) i= if i=a then -nodeC o i else nodeC o i:=by
 unfold zap nodeC; simp only [Pi.add_apply,Pi.smul_apply,flee_pos]; by_cases h:a=i <;> simp [h,nsmul_eq_mul,eq_comm] <;> try ring
lemma zap_gen(a:Axis)(s:ℕ)(o:Cover): zap a (orbitB Lx o s) = orbitB Lx (zap a o) s:=by
 apply node_dC; ext i; rw [zap_node,dutyT _ _ P.par.R.odd_side,dutyT _ _ P.par.R.odd_side]; simp only [Pi.smul_apply,nsmul_eq_mul]; rw [zap_node]; split_ifs <;> ring
noncomputable abbrev difft(a:Axis)(i:Axis)(t:ℤ):ℤ:=if i=a then -t else t
lemma zap_metro (a:Axis)(y o:Cover): zap a (metro P y o)=metro P (fun i=>difft a i (y i)) (zap a o):=by
 apply node_dC; ext i; rw [zap_node,metro_cal,metro_cal,zap_node]; unfold difft; split_ifs <;> ring
lemma twice_zap(a:Axis)(o:Cover): zap a (zap a o)=o:=by
 apply node_dC; ext i; rw [zap_node,zap_node]; split_ifs <;> ring
lemma wp_zap(a:Axis)(s:ℕ)(o:Cover): (P.reflectTest a) (wp P s o)= wp P s (zap a o):=Subtype.ext (ace ..)
noncomputable abbrev rider(s:ℕ):= sit P s (subject P F s)
noncomputable abbrev saddle(s:ℕ):= bow P s (zap 3 (subject P F s))
noncomputable abbrev lever(s:ℕ)(a:Axis):Cover:= zap a (saddle P F s)
lemma riderV(s:ℕ)(a:Axis): (minB P s:ℤ) ≤ nodeC (rider P F s) a:= (ride P s _ _).1
lemma leverV(s:ℕ)(a:Axis): (minB P s:ℤ) ≤ nodeC (lever P F s a) a:= (tilt P s _ _).1.trans_eq (by rw [lever,zap_node,if_pos rfl])
lemma riderA(s:ℕ)(i:Axis): |nodeC (rider P F s) i|≤(reachQ P s:ℤ):=by rw [abs_of_nonneg (by linarith only [riderV P F s i,(show 0 ≤ (minB P s:ℤ) from Nat.cast_nonneg _ )])]; exact (ride P s _ _).2
lemma saddleA(s:ℕ)(i:Axis): |nodeC (saddle P F s) i|≤(reachQ P s:ℤ):=by rw [←abs_neg,abs_of_nonneg (show 0 ≤ - _ from Nat.cast_nonneg (minB P s)|>.trans (tilt P s _ _).1)]; exact (tilt P s _ _).2
lemma leverA(s:ℕ)(a i:Axis): |nodeC (lever P F s a) i|≤(reachQ P s:ℤ):=by rw [lever,zap_node]; split_ifs <;> (try simp only [abs_neg]) <;> exact saddleA P F s i
/- aircraft {
 roles 0 right, 1 left. root source o_k(s) in each axis RP positive by design. -/
noncomputable def tablet(s:ℕ)(a:Axis)(b:Bool):Cover:=Bool.rec (rider P F s) (lever P F s a) b
noncomputable def sap(s:ℕ)(a:Axis)(b:Bool):Cover:=Bool.rec (rifle P s (subject P F s)) (fun i:Axis=>difft a i (downR P s (zap 3 (subject P F s)) i)) b
-- source establishment relate successive resolutions.A
lemma stands(s j:ℕ)(h:F ≤ j)(u:j ≤ s)(b:Bool)(a:Axis):
 let y:Cover:= (fun i=>(P.par.R.L.val:ℤ)^(s-j)*sap P F j a b i); let z:= sap P F s a b
 orbitB Lx (tablet P F j a b) (s-j)=metro P (y-z) (tablet P F s a b):=by
 intro y z
 cases b
 · change orbitB _ (rider P F j) _=metro _ _ (rider P F s)
   rw [rider,rider,sit,sit,swingZ, upwards P F s h u]; exact (hingeZ P (subject P F s) (rifle P s (subject P F s)) y).symm
 · change orbitB _ (zap _ (metro P _ _)) _=metro _ _ (zap _ (metro P _ _))
   rw [zap_metro,zap_metro,swingZ,←zap_gen,←zap_gen,upwards P F s h u]; exact (hingeZ P (zap a (zap 3 (subject P F s))) z y).symm
lemma tablet_paid(s:ℕ)(a:Axis)(b:Bool): (minB P s:ℤ)≤ nodeC (tablet P F s a b) a:=by cases b; exact riderV ..; exact leverV ..
lemma tablet_born(s:ℕ)(a:Axis)(b:Bool): (P.calibration.ℓ:ℤ)+22 ≤ nodeC (tablet P F s a b) a:= (tablet_paid P F s a b).trans' (by unfold minB; norm_cast; exact add_le_add_right (Nat.le_add_right ..) _)
lemma tablet_abs(s:ℕ)(a:Axis)(b:Bool)(i:Axis): |nodeC (tablet P F s a b) i| ≤(reachQ P s:ℤ):=by cases b; exact riderA ..; exact leverA ..
#print axioms stands
#print axioms tablet_born
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
