import ZecaTea
import ZecaSnap
import ZecaFount
import SatinThinFusionStitch
import YM.SU5.Cordial.Horizon
import YM.SU5.Cordial.Spritz
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
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
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 8000


variable (P:Spine)
local notation "K" => P.calibration
local notation "tM" => timeMesh P.par
section
variable (A B:P.Apron)
local notation "s!"=>A.s
local notation "δ" => B.zoom P A.s 3
local notation "Q" => volumeAround P.par P.width (A.s-B.s) B.S
local notation "d"=> P.fusionFare B A.s
def teatip : P.Apron where
 s:=s!
 u:=fun j=> B.zoom P s! j + d + (A).u j
 pos:= fun j=>by have he:= B.zoomP P j s!; omega
 F:= (P.shifts 3 δ (B.full P s!))* (P.shifts 3 d (A).F)
 S:= plow K 3 δ Q ∪ plow K 3 d (A).S
 bay:= (bay K _ true).mul_mem ((tallerBay _ _ _ subset_union_left) (P.shifts_support 3 _ _ ((Tower.proceeds P.run P.large P.history.circuit B.s (s!-B.s) ((Tapestry.locates ..).1 B.bay)).1))) ((tallerBay _ _ _ subset_union_right) (P.shifts_support 3 _ _ (A).bay))
 realM:= Subalgebra.mul_mem _ (P.shifts_keep 3 _ (B.fullColor P s!)) (P.shifts_keep 3 _ (A).realM)
 shelter:= fun j z v=> by
    rcases mem_union.mp v with v|v
    · exact P.stretch_between j (by unfold fusionFare; omega) (P.transport_shelter j 3 _ _ (P.full_shelter j B s!)) z v
    exact P.stretch_between j (by omega) (P.transport_shelter j 3 _ _ ((A).shelter j)) z v
-- the registration width (upper bound for full stencil)
local notation "E"=> P.teatip A B
variable (j:Axis)
lemma teatip_width (p:B.s ≤ s!) : (E).realWidth P j = B.realWidth P j + 3*B.realWidth P 3 + A.realWidth P j:=by
 rw [← B.zoom_bell P 3 s! p,← B.zoom_bell P j s! p]; change bell tM s! (((B.zoom P s! j + (d:ℕ) + _):ℕ):ℤ)= _; simp only [bell,Int.cast_natCast, fusionFare,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat];  change _= _+_+(↑(↑((A).u j):ℤ):ℝ)* _; push_cast; ring
end
variable (D:P.Apron) {e:ℝ}
variable (B:P.Apron) (x:P.Spectrum0 3) (a:ℂ)
local notation "s!"=>B.s
local notation "Φ"=>P.shifts 3
local notation "b"=>bell tM
local notation "w!"=>B.u 3
variable (h1:P.Cash 3 x B.s (2*B.u 3)
       (P.shifts 3 (B.u 3) B.F - a • (1:P.Test)) e)
include h1

local notation "X"=>D.zoom P s! 3
local notation "U"=> P.teatip B D
local notation "d"=> 4*(D.zoom P s! 3) + w!
local notation "g"=> (D.full P s!)
local notation "A"=>‖D.engine P 3 x‖

lemma tapioca_cash
 (q:w!≤ D.zoom P s! 3) (u:D.s ≤ s!):
 let d':= 4*(D.zoom P s! 3)+w!
 P.Cash 3 x s! (2*d')
      (P.shifts 3 d' ((U).F)
             - a • P.shifts 3 ((d'+D.zoom P s! 3:ℕ):ℤ) (D.full P s!))
       (‖D.engine P 3 x‖*e):=by
 intro k
 let m:=D.zoom P s! 3
 let t:= 2*m+(m-w!)
 let f: P.Test:= Φ w! B.F- a • (1:P.Test)
 have g₁:=D.cash_slice P 3 x u («d»:=(m:ℤ)) (w:=2*m)
     (le_refl _) (show (m:ℤ)+m≤↑(2*m:ℕ) by omega)
 have G : (Φ m (D.full P s!)) * Φ t f=(U).F - a • (Φ m (D.full P s!)):=by
    have hv:(t:ℤ) + w!=(↑(P.fusionFare D s!):ℤ):=by
        change (t:ℤ)+w!=↑(3*m:ℕ)
        change w! ≤ m at q
        unfold t; omega
    unfold f
    rw [map_sub,map_smul,map_one,P.shifts_sum,hv,mul_sub,mul_smul_comm,mul_one]; rfl
 have GK := (g₁.right (m-w!)).mul h1
 rw [G] at GK
 let L:= k-(t+2*w!)
 have h:= (GK.left k).right L
 have he:k+(t+2*w!)+L=2*k:=by
    have hv: k=4*m + w!:=rfl
    unfold L t
    omega
 rw [he,map_sub,map_smul,P.shifts_sum] at h
 rw [Nat.cast_add]; exact h

omit h1 in
lemma tapioca_d: (P.teatip B D).u 3= 4*D.zoom P s! 3+w!:=by
 change D.zoom P s! 3+3*D.zoom P s! 3+w!=_
 omega

local notation "δ"=>D.realWidth P 3
lemma tapioca_pay
 (q:w!≤ D.zoom P s! 3) (u:D.s ≤ s!)
 {c h:ℝ}
 (t₀:(P.teatip B D).realWidth P 3 ≤ c)
 (t₁:(P.teatip B D).realWidth P 3 ≤ h):
 ‖P.ruby 3 x (P.teatip B D) 0 c h -
    a • P.ruby 3 x D 0 (c+δ) (h-δ)‖ ≤ A*e:=by
 let k:=d
 let m:=D.zoom P s! 3
 let y:=(P.teatip B D).realWidth P 3
 have he:d=(U).u 3:= (P.tapioca_d D B).symm
 have hy:b s! k=y:=by unfold k y; rw [he]; rfl
 have hv:b s! m=δ:= D.zoom_bell P 3 s! u
 have hg: δ≤ y-δ:=by
    have ht: δ+δ ≤ y:=by
       rw [←hv,←hy,←bell_add]
       rw [bell_le]
       omega
    linarith only [ht]
 have D1 : P.Snap 3 x s! (2*k)
      (Φ k (U).F)
      (P.ruby 3 x U 0 y y):=by
       have hd:(U).s=s!:=rfl
       apply (U).snap_here P 3 x («d»:=k) _ _ hy _
       · omega
       · omega
       rw [hd,←hy,←bell_add]
       congr 1
       omega
 have D2:P.Snap 3 x s! (2*k)
      (Φ (↑(k+m:ℕ)) g) (P.ruby 3 x D 0 (y+δ) (y-δ)):=by
       apply D.snap P 3 x u
       · omega
       · omega
       · rw [Nat.cast_add,bell_add,hy,hv]
       rw [show y+δ+(y-δ)=y+y from by ring,←hy,←bell_add]
       congr 1
       omega
 have f:=(D1.sub (D2.smul a)).norm_cash (P.tapioca_cash D B x a h1 q u)
 let v:=P.ruby 3 x U 0 y y - a • P.ruby 3 x D 0 (y+δ) (y-δ)
 let t:=(P.buff_pay 3 x (c-y) (h-y) v).trans f
 have hz:δ≤y+δ:=le_add_of_nonneg_left ((U).real_width_pos P 3).le
 unfold v at t
 rw [map_sub,map_smul,
     P.ruby_large 3 x U _ _ (sub_add_cancel c y) (by ring:y+(h-y)=h) (sub_nonneg.mpr t₀) (sub_nonneg.mpr t₁) (le_refl y) (le_refl y),
     P.ruby_large 3 x D _ _ (by ring:c-y+(y+δ)=c+δ) (by ring:y-δ+(h-y)=h-δ) (sub_nonneg.mpr t₀) (sub_nonneg.mpr t₁) hz hg] at t
 exact t
#check bell_add
