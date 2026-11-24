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

variable (P:Spine) (Z:Lead.Clan)(x:P.Spectrum0 3)
local notation "Φ"=>P.shifts 3
local notation "a"=> (purePrice Z:ℂ)
local notation "b"=> bell (timeMesh P.par)
variable {s n w:ℕ} {e:ℝ} (h:w≤w)
local notation "Front"=> P.thinMat Z s n
lemma cash_front (p:P.powderPay s n w e) (h:P.probeClock n 3≤w):
 P.Cash 3 x s (2*w)
      (P.shifts 3 w (P.frontMat Z n) - (purePrice Z:ℂ) • (1:P.Test)) e:=by
 obtain ⟨T,v,_⟩:=
    (Front).snap_here P 3 x
        (show (↑((Front).u 3):ℤ)≤w from Int.ofNat_le.mpr h)
        (w:=2*w) (by change (w:ℤ)+ ↑(P.probeClock n 3)≤_; omega) rfl
        (show b s (↑(2*w:ℕ))=b s w + b s w by unfold bell; push_cast; ring)
 have f:P.Fired 3 x s (2*w) (Φ w (P.frontMat Z n)) T:=v
 let u:= f.sub ((Fired.identity f.pos).smul (a))
 exact ⟨_,u,p Z 3 x _ u⟩
variable (D:P.Apron)
local notation "X"=>D.zoom P s 3
local notation "U"=> P.stitchApron Z D s n
local notation "d"=> 4*(D.zoom P s 3) + P.probeClock n 3
local notation "g"=> (D.full P s)
local notation "A"=>‖D.engine P 3 x‖

lemma sewing_cash (p:P.powderPay s n w e) (r:P.probeClock n 3≤w)
 (q:w≤ D.zoom P s 3) (u:D.s ≤ s):
 let d':= 4*(D.zoom P s 3)+P.probeClock n 3
 P.Cash 3 x s (2*d')
      (P.shifts 3 d' ((U).F)
             - a • P.shifts 3 ((d'+D.zoom P s 3:ℕ):ℤ) (D.full P s))
       (‖D.engine P 3 x‖*e):=by
 intro k
 let m:=D.zoom P s 3
 let t:= 2*m+(m-w)
 let f: P.Test:= Φ w (P.frontMat Z n)- a • (1:P.Test)
 have g₁:=D.cash_slice P 3 x u («d»:=(m:ℤ)) (w:=2*m)
     (le_refl _) (show (m:ℤ)+m≤↑(2*m:ℕ) by omega)
 have G : (Φ m (D.full P s)) * Φ t f=(U).F - a • (Φ m (D.full P s)):=by
    have hv:(t:ℤ) + w=(↑(P.fusionFare D s):ℤ):=by
        change (t:ℤ)+w=↑(3*m:ℕ)
        change w ≤ m at q
        unfold t; omega
    unfold f
    rw [map_sub,map_smul,map_one,P.shifts_sum,hv,mul_sub,mul_smul_comm,mul_one]; rfl
 have GK := (g₁.right (m-w)).mul (P.cash_front Z x p r)
 rw [G] at GK
 let L:= k-(t+2*w)
 have h:= (GK.left k).right L
 have he:k+(t+2*w)+L=2*k:=by
    have hv: k=4*m + P.probeClock n 3:=rfl
    unfold L t
    omega
 rw [he,map_sub,map_smul,P.shifts_sum] at h
 rw [Nat.cast_add]; exact h

lemma sewing_d (s n:ℕ): (P.stitchApron Z D s n).u 3= 4*D.zoom P s 3+P.probeClock n 3:=by
 change D.zoom P s 3+3*D.zoom P s 3+P.probeClock n 3=_
 omega

local notation "δ"=>D.realWidth P 3
lemma sewing_pay (p:P.powderPay s n w e) (r:P.probeClock n 3≤w)
 (q:w≤ D.zoom P s 3) (u:D.s ≤ s)
 {c h:ℝ}
 (t₀:(P.stitchApron Z D s n).realWidth P 3 ≤ c)
 (t₁:(P.stitchApron Z D s n).realWidth P 3 ≤ h):
 ‖P.ruby 3 x (P.stitchApron Z D s n) 0 c h -
    (purePrice Z:ℂ) • P.ruby 3 x D 0 (c+δ) (h-δ)‖ ≤ A*e:=by
 let k:=d
 let m:=D.zoom P s 3
 let y:=(P.stitchApron Z D s n).realWidth P 3
 have he:d=(U).u 3:= (P.sewing_d Z D s n).symm
 have hy:b s k=y:=by unfold k y; rw [he]; rfl
 have hv:b s m=δ:= D.zoom_bell P 3 s u
 have hg: δ≤ y-δ:=by
    have ht: δ+δ ≤ y:=by
       rw [←hv,←hy,←bell_add]
       rw [bell_le]
       omega
    linarith only [ht]
 have D1 : P.Snap 3 x s (2*k)
      (Φ k (U).F)
      (P.ruby 3 x U 0 y y):=by
       have hd:(U).s=s:=rfl
       apply (U).snap_here P 3 x («d»:=k) _ _ hy _
       · omega
       · omega
       rw [hd,←hy,←bell_add]
       congr 1
       omega
 have D2:P.Snap 3 x s (2*k)
      (Φ (↑(k+m:ℕ)) g) (P.ruby 3 x D 0 (y+δ) (y-δ)):=by
       apply D.snap P 3 x u
       · omega
       · omega
       · rw [Nat.cast_add,bell_add,hy,hv]
       rw [show y+δ+(y-δ)=y+y from by ring,←hy,←bell_add]
       congr 1
       omega
 have f:=(D1.sub (D2.smul a)).norm_cash (P.sewing_cash Z x D p r q u)
 let v:=P.ruby 3 x U 0 y y - a • P.ruby 3 x D 0 (y+δ) (y-δ)
 let t:=(P.buff_pay 3 x (c-y) (h-y) v).trans f
 have hz:δ≤y+δ:=le_add_of_nonneg_left ((U).real_width_pos P 3).le
 unfold v at t
 rw [map_sub,map_smul,
     P.ruby_large 3 x U _ _ (sub_add_cancel c y) (by ring:y+(h-y)=h) (sub_nonneg.mpr t₀) (sub_nonneg.mpr t₁) (le_refl y) (le_refl y),
     P.ruby_large 3 x D _ _ (by ring:c-y+(y+δ)=c+δ) (by ring:y-δ+(h-y)=h-δ) (sub_nonneg.mpr t₀) (sub_nonneg.mpr t₁) hz hg] at t
 exact t
#check bell_add
