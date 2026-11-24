import Bay.Slip
import YM.SU5.FiniteGaugeData.Tower.Roomer

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


namespace Silk
open Buffered Lifted StressExchange

open Buffered.Afterglow
open Tower SlabMark Heat Nacre


variable {N:Side}

lemma tiltTax (t:Cover)(W:Op (Single N)):
 twist (prepU (lagX t) 1 inert N) W=twist (γS (taxiPlus (wrap N t))) W:=by
 let A:=lagX t
 have h:=sigW (n:=N) A false (spinU false A.s) W
 have l:JetS A.s false (detX A.s) 1:=by unfold A lagX; dsimp;rw[det_i];exact calmSX
 rw[poll A false W _ 1 (spinZ ..) l,site_ui] at h -- site_ui lhs too
 exact h.symm

lemma stepTax (t:Cover)(V:Pane N):
 flashA (taxiPlus (wrap N t)) V=Yg (lagX t) V:= by
 exact stir_e (lagX t) false V

variable (t:Cover)
lemma taxJ (W X:Op (Single N)):
 twist (quantU (prepU (lagX t) 1 inert N)) (preJ W X)=
 twist (quantU (γS (taxiPlus (wrap N t)))) (preJ W X):=by
 rw[preMove,preMove,tiltTax,tiltTax]

lemma wipe (t:Cover)(W:Op (Single N)):
  twist (prepU (lagX (-t)) 1 inert N)
     (twist (γS (taxiPlus (wrap N t))) W)=W:=by
  rw [tiltTax,map_neg]
  let U:= wrap N t
  have e:taxiPlus U * taxiPlus (-U)=1:= by
    have y:-U=wrap N (-t):=(map_neg ..).symm
    rw[y]
    change Levier.ray false (lagX t) * Levier.ray false (lagX (-t))=1
    rw[Levier.ray_join]
    unfold lagX joinX
    simp only[neg_add_cancel, Signed.act_one, mul_one, Levier.ray, map_zero]
    rfl
  change ech (taxiPlus (-U)) (ech (taxiPlus U) W)=W
  rw[Sour.paceK,e,beat_x]

variable {i:Axis}{z:ℤ}
lemma outWord (g:Mark N)(h:AtSupport false univ g)(V:Fields N):
 reflMark i z (reflMark i 0 g) V = 
   twist (quantU (prepU (lagX (-(z • step i))) 1 inert N))
    (g (Yg (lagX (z • step i)) V.1,Yg (lagX (z • step i)) V.2)) :=by
 unfold reflMark reflFields
 dsimp only[Prod.map]
 unfold fling
 rw [←kor,←kor,plane_join,sub_zero,
      theta_theta _ _ _ (firm_join i 0 z) (h.allV _|>.sector),zero_sub,neg_smul]

variable {k:ℕ}{p:BudgetPoint}{X:SOp N}{K:Scree.Loom N}{c d:ℝ} (i:Axis)(z:ℤ)
lemma toothChime (x:Site N)(H:Clearance p K k d)(G:BoxPay X (node x) k c d)
 (h:AtSupport false univ (fun v=>toothAt K p x X v.1)):
 reflMark i z (reflMark i 0 (fun v=>toothAt K p x X v.1))=fun v=>
    tooth K p x (x+wrap N (z • step i)) X v.1:=by
 funext v
 rw [outWord _ h,←stepTax]
 dsimp only
 have u:=toothMoves x (x+wrap N (z • step i)) H G v.1
 dsimp only at u
 rw [add_sub_cancel_left] at u
 rw[←u]
 unfold tooth toothAt emMark
 rw [preMove,preMove,wipe,wipe]
end YM.CF.Bay.Silk
