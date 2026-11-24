import YM.CF.BProof.Mote.Weave
import YM.CF.Bloom.Flux
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive Tap Haro
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye
set_option synthInstance.maxSize 28000
namespace Leg
variable {m n : Type}[LinearOrder m][Fintype m][LinearOrder n][Fintype n]
variable {N P:Side}(G:Ratio N P)(j:ℕ) (Q:SpaceM)(M:Male)
open TripD
variable (i:Axis) (X:Nom N P) (v:Odd G.count.val)
abbrev turns (N:Side):= Fixed.reflectP N i
abbrev rotates {N:Side} (i:Axis): UNI (Single N):= turns i N -- tune turns binder order
abbrev sweepT := pflux (Fixed.reflShape i) G (Fixed.pinSpin i) inert
lemma broadD : Shape.broad G (Fixed.reflShape i)=Fixed.reflShape i:=by change Shape.mk _ (_ • (0:Cover))=_; rw [smul_zero]
local notation "R_"=> sweepT G i
lemma hoodComm :Commute (R_).val (hood G):=by
 have hx: twist R_ (hood G)=hood G:=hoodL G (Fixed.reflShape i) inert (Fixed.pinSpin i); unfold Commute SemiconjBy; nth_rw 2 [←hx]; rw [twist_formula,mul_assoc,(R_).property.1,mul_one]
lemma sweepP (x:Ket (Single N)): coat (patchQ G) (acts (Fixed.reflectP N i).val x) = acts (R_).val (coat (patchQ G) x):=by
 let U:= Fixed.reflectP N i; let R:=R_; let E:=patchQ G; let z:=acts R.val (coat E x); have h:= coat_ret E x; have ht: acts (cutM (lows E)) z=z:= by have ht:= hoodComm G i; rw [lighthouse] at ht; exact shine h ht.symm
 have he: trailK E z=acts U.val x:=by rw [← show acts (summit E (R_).val) x=trailK E z from Fock.summit_rule .., show summit E (R_).val=U.val from ?_]; ext; exact zoom G (Fixed.reflShape i) inert (Fixed.pinSpin i) ..
 change coat E (acts U.val x)=z; rw [←he,stance,ht]
include v
lemma sample : (R_).val= portW (switchG G).symm (Fixed.reflectP P i).val:=by rw [sweepT,puff _ v, broadD]; rfl
lemma songShift (U: Pane P)(b:Bool)(x:Ket (Single N)) : acts (Fixed.reflectP P i).val (songL G j M Q b U x)= songL G j M Q (!b) (Fixed.reflConfig P i U) (acts (Fixed.reflectP N i).val x):=by
 let T:=Fixed.reflShape i; let Y:Nom N P:= (U,1); let Y':=stanza G T inert Y; let W:=Fixed.reflectP N i; let z:= Fixed.reflConfig P i U; let P':= R_
 have he:Y'.1=z:=by change stir _ (Shape.broad G (Fixed.reflShape i)) _=_; rw [broadD]; exact (by rw [← Fixed.flash_reflect i U]; unfold flashA; rw [Fixed.castX_reflect]; rfl -- z not elaborated tune
     : stir inert (Fixed.reflShape i) U=Fixed.reflConfig P i U)
 have hk:twist P' (turret G j M U)= Peaks.cloth j M G (unionP Y'):= clothing G v T inert (Fixed.pinSpin i) (mirrorX i) j M Y
 have ht: Peaks.cloth j M G (unionP Y')= turret G j M z:= (turret_eq G j Y'.1 Y'.2 M).trans (congrArg _ he)
 unfold songL; rw [←adjust,←sample G i v]; change trailK _ _=trailK _ (acts (turret G j M z) _); rw [←ht,←hk,Fock.swivel (R_)]; unfold humP click; rw [←belt_frame,sweepP] -- tune direction
omit v
lemma ok_cast {b:Bool}{x:Ket (Single N)}(p:okSpin b x) : okSpin (!b) (acts (Fixed.reflectP N i).val x):=by
 let U:= Fixed.reflectP N i; have he: twist U (1-tickA N)= tickA N :=by rw [Fixed.tickA_upper,←dim_cut]; exact Fixed.reflectP_upper ..
 have hz: acts (tickA N) (acts U.val x)= acts U.val (acts (1-tickA N) x):=by nth_rw 1 [←he]; exact (Fock.swivel U (1-tickA N) x).symm -- tune swivel type
 change acts _ _=_; rw [hz,act_sub,act_one,show acts (tickA N) x= _ from p]; cases b <;> simp <;> try rfl
abbrev coinP (b:Bool):ℂ:= if b then (-Complex.I) else Complex.I
lemma θport (R:UNI n)(b:Bool)(x:Ket n): theta R (port b x)=coinP b • port (!b) (acts R.val x):=by cases b; exact theta_downV ..; exact theta_upV ..
include v
lemma pro_mir (b:Bool){x:Ket (Single N)}(p:okSpin b x)(u:IsUnit (Peaks.cloth j M G (unionP X)))(k:Phys P): acts (theta (Fixed.reflectP N i) (port b x)) (prog G j M Q X k)=prog G j M Q X (acts (theta (Fixed.reflectP P i) (port b (songL G j M Q b (Fixed.reflConfig P i X.1) x))) k):=by
 rw [θport, θport,songShift G j Q M i v,Fixed.square_reflConfig,act_smul,act_smul, pro_p G j M X Q (!b) (ok_cast i p) v u]; unfold prog scaleZ Dial.fire effectK; rw [carts_s]; simp only [map_smul]; -- smul commute
 -- tune
 rw [smul_comm (coinP _),smul_comm (coinP _)]
end Leg
end YM.CF.BProof.Bide
