import Velour.Tassel.Plan
set_option autoImplicit false

set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set

open Py.Rate.LocalLimit.Papal (Weaver household meanF)
variable (P:Spine)(Z:Lead.Clan)(n:ℕ)
local notation "e₃"=> YM.basis (3:Axis)
local notation "ℓ"=> P.calibration.ℓ

variable {s b:ℕ}{u v:ℝ} (G:P.Apron)
local notation "C"=>timeMesh P.par
local notation "j"=> (3:Axis)
variable (x:P.Spectrum0 3)
-- x directly eigen 3 (can apply at P.advocate..)
local notation "W"=>P.ColorHil j x
local notation "ℋ"=>P.physicalEnergy j x
local notation "𝐸" => (ℋ).E
local notation "Q"=>P.shifts j
local notation "δ"=> G.zoom P s 3
local notation "d"=> G.realWidth P 3
local notation "V"=> P.fusionFare G s
local notation "S"=> P.stitchApron Z G s n
local notation "w"=> (S).u 3
local notation "e"=> (S).realWidth P 3
local notation "lamp"=> P.frontMat Z n
local notation "π'"=> (purePrice Z:ℂ)
local notation "L0"=> P.frontMat Z n-π' • (1:P.Test)
local notation "B"=> bell C s

lemma nozzle {ρ:ℝ}(t:P.FlickTone n b s ρ) :
 ∃ X,P.ThreadOp j x s (b+b) (Q b (L0)) X ∧ ‖X‖≤ρ:=by
 obtain ⟨a,p,h,n'⟩:=t.2 Z j
 have cost:P.voxTest j s a.val∈ enclave P.calibration:=by
    rw [h]
    exact P.shifts_keep _ _ (Subalgebra.sub_mem _ (P.front_real _ _)
      (Subalgebra.smul_mem _ (one_mem _) _))
 obtain ⟨X,g,v⟩:=P.thread_door j x a p cost
 exact ⟨X,g.mono rfl h,v.trans n'⟩


lemma shaft (h:G.s ≤ s) (y:B b ≤ d) 
 {X:(P.ColorHil 3 x).Op}(p:P.ThreadOp j x s (b+b) (Q b (L0)) X):
 ∃Y,P.ThreadOp j x s (w+w) (Q (w) ((Q δ (G.full P s)) * (Q V (L0)))) Y
 ∧ ‖Y‖ ≤ ‖G.engine P 3 x‖ * ‖X‖:=by
 -- compose at seam
 have ph:=G.promoted (x:=x) h
 have a: b≤δ := by exact_mod_cast (bell_le C s _ _).mp (show B b ≤ B δ from y.trans_eq (G.zoom_bell P j s h).symm)
 let k:=δ-b
 let l:=w-(V+b)
 have hx : w=δ+V+P.probeClock n 3:=rfl
 refine ⟨_, ((ph.aft k |>.cat p).pad w l).mono ?_ ?_,?_⟩
 · unfold k l; unfold fusionFare at *; omega
 · rw [P.shifts_sum]
   have F : (↑(δ + δ + k:ℕ):ℤ)+(↑b:ℤ) = ↑V:=by unfold k fusionFare; omega
   rw [F]
 -- norms, each heat ≤ 1

 have t (R:(W).Op)(a:ℝ≥0): ‖R*𝐸 a‖ ≤ ‖R‖:= 
    (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) ((ℋ).shrinks _))
 refine (t _ _).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((ℋ).shrinks _)).trans ?_))
 exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (t _ _) (norm_nonneg _))

lemma doubled_width (h:G.s ≤ s):
  2*d ≤ e:=by
 rw [P.stitch_width j Z n h]
 have z:(P.thinMat Z s n).realWidth P 3= P.probeWidth s n j:= rfl
 rw [←z]
 have x:=G.real_width_pos P j
 linarith [(P.thinMat Z s n).real_width_pos P j]

lemma unstitch (h:G.s ≤ s):
   P.ThreadOp 3 x s (w+w) (Q (w) (Q δ (G.full P s)))
       (G.dye P 3 x (e+d) (e-d)):=by
 rw [P.shifts_sum]
 have t:=P.doubled_width Z n G h
 have pd:=G.real_width_pos P j
 refine G.dyedAbove P j x h _ _ _ ?_ ?_ (by linarith only [pd,t]) (by linarith only [t])
 · rw [bell_add,G.zoom_bell P 3 s h]; rfl
 simp only [Nat.cast_add, bell_add]; change e+e- _ = _; ring
lemma silver (h:G.s ≤ s) (y:B b ≤ d)
 {ρ:ℝ}(t:P.FlickTone n b s ρ):
 ‖(S).engine P j x - π' • G.dye P 3 x (e+d) (e-d)‖ ≤ ‖G.engine P 3 x‖ * ρ:=by
 obtain ⟨X,a₀,rX⟩:=P.nozzle Z n x t
 obtain ⟨Y,p,q⟩:= P.shaft Z n G x h y a₀
 have hx:= (S).sewn (x:=x)
 have hm:=hx.sub ((P.unstitch Z n G x h).smul π')
 refine le_trans ?_ (mul_le_mul_of_nonneg_left rX (norm_nonneg (G.engine P 3 x)))


 rw [hm.unique (show P.ThreadOp _ _ _ _ _ Y from p.mono rfl (by
    rw [←map_smul,←map_sub]
    apply congrArg
    rw [map_sub,map_smul,map_one,mul_sub, Algebra.mul_smul_comm,mul_one]
    rfl))]
 exact q

theorem silvered (h:G.s ≤ s) (y:B b ≤ d)
 {ρ:ℝ} (t:P.FlickTone n b s ρ) (a:e ≤ u) (a':e ≤ v):
 ‖(S).dye P j x u v - π' • G.dye P 3 x (u+d) (v-d)‖ ≤ ‖G.engine P 3 x‖ * ρ:=by
 have width:=P.doubled_width Z n G h
 have d₀:=G.real_width_pos P j
 have g:=G.dye_twice P j x (a:=e+d) (c:=u+d) (b:=e-d) («d»:=v-d) (by linarith only [d₀,width]) (by linarith only [width]) (add_le_add_left a _) (sub_le_sub_right a' _)
 rw [add_sub_add_right_eq_sub, sub_sub_sub_cancel_right] at g
 rw [←g, Apron.dye,←map_smul,←map_sub]
 exact ((ℋ).pad_le ..).trans (P.silver Z n G x h y t)


end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

