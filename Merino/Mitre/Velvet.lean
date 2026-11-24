import Merino.Salon
import Merino.Brooch.Tour
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 620000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Mitre
open Fock Finset Lattice Lat Spire Scroll Cube Branch Skye Tenant RG BProof
open scoped BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Buffered
variable {N:Side}
open Brooch

open Hive Levier Mir.Trip
variable(i:Axis)(a:ℤ)
def flipL (i:Axis)(a:ℤ):Sweep N:= ray false (plane i a)

lemma flipL_i : (flipL i a:Sweep N)⁻¹=flipL i a:=by
   refine inv_eq_of_mul_eq_one_right ?_
   unfold flipL
   rw [ray_join, gaugeSquare]; simp [ray,Nacre.incX]; rfl
lemma hinges {F:Obs N}(h:Bide.plainP F):
  toMark (Bide.move (flipL i a) F) = reflMark i a (toMark F):=by


 funext V
 change teen (flipL i a) (F (flashA (flipL i a)⁻¹ _))=theta _ (F _)
 rw [flipL_i]
 have w:=flipL (N:=N) i a
 have ht : flashA (flipL i a) V.1 = (reflFields i a V).1:= stir_e (plane i a) false V.1
 rw [ht]
 unfold flipL teen
 refine (hono false (plane i a) _ (h _)).trans ?_
 unfold yodel
 have ha:detX (plane i a).s=true :=det_t i
 apply (stag_s false _ _ (Window.pinLift i) _ (h _) (spinZ ..) ?_).trans
 · rw [ha];rfl
 rw [ha];exact mirrorX i


open Thera
lemma push_box(s t:Sweep N)(x):boxA (s*t) x=boxA s (boxA t x):=(stirP ..).symm
lemma fl_box (x:Seat N):boxA (flipL i a) x=(plane i a).anon N x:=stir_wrap x (plane i a).s _ _ (wrap_lift (wrap N (plane i a).t))

-- two mirrors to taxiPlus
open Sour Swell Nacre Urn
lemma fl_prod:(flipL i a:Sweep N)* flipL i 0 = taxiPlus (wrap N (a • step i)):=by
 unfold flipL
 rw [ray_join];simp [ray,joinX,plane,show Signed.mirror i*Signed.mirror i=1 by nth_rw 1 [←Signed.mirror_inv i];exact inv_mul_cancel _]



/- AP-preserving receipt. -/
variable {F : Obs N}
lemma sail(v:Site N)(h:Bide.plainP F) :
 Spool.perches F (Bide.move (taxiPlus v)⁻¹ F) v:=by
 have j:=Bide.dance (taxiPlus v)⁻¹ (taxiPlus v) h
 rw [inv_mul_cancel,Bide.move_e h] at j
 intro V
 let s:=taxiPlus v
 let W:=flashA s V
 have e:=congr_fun j W
 let Q:=Bide.move s⁻¹ F
 change yodel false _ (Q (flashA s⁻¹ (flashA s V))) = _ at e
 rw [lights,mul_inv_cancel,rev1] at e
 unfold yodel at e
 rw [show detX (castX (taxiPlus v)).s = false from det_i] at e
 exact e


-- move orientation all the way
lemma posed(s:Sweep N)(h:Bide.plainP F):
 toMark (Bide.move ((flipL i a)*s)⁻¹ F) =
 reflMark i a (toMark (Bide.move s⁻¹ F)):=by
 rw [← hinges _ _ (Bide.keys _ h),Bide.dance _ _ h, _root_.mul_inv_rev,flipL_i]

end YM.CF.Merino.Mitre
