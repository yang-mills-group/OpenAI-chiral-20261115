import YM.SU5.Assay.BeamRide
import YM.SU5.Assay.SeenBox
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
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
open Aria Set
open Six

variable {P:Spine}{f g:P.Test}{S T D:Finset Cover}{s t:ℕ}{W:Bool}
local notation "K"=> P.calibration
variable {j:Axis}{d w:ℕ}
/-!
# Single joint stencils at one resolution; seams between entire stickers
-/
structure Glaze (P:Spine) where
  w:ℕ
  pos:0<w
  S: Finset Cover
  F:P.Test
  inlet: F∈bay P.calibration S true
  color:F∈enclave P.calibration
  fits:P.BFits w S
namespace Glaze
variable (B C:P.Glaze)(j:Axis)
local notation "σ"=>P.shifts j
local notation "u" => ruler (P.par.block)

def apron (s:ℕ): P.Apron:= ⟨s,(fun _=>B.w),(fun _=>B.pos),B.F,B.S,B.inlet,B.color,B.fits⟩
def tile (s:ℕ): (P.Hil j).Op:= P.meanBox j s (B.w+B.w) (σ B.w B.F)
lemma centers : P.BEntry j (B.w+B.w) (σ B.w B.F):=(B.apron 0).admit j

def swell (p:B.w ≤ d): P.Glaze:= ⟨d,B.pos.trans_le p,B.S,B.F,B.inlet,B.color,B.fits.mono p⟩
def coat (z:ℂ): P.Glaze:=⟨B.w,B.pos,B.S,z•B.F,(bay ..).smul_mem B.inlet z,(enclave K).smul_mem B.color z,B.fits⟩
def bridge: ℕ:= B.w+1+C.w
local notation "b"=>B.bridge C
lemma distancePin (s:ℕ): Disjoint (P.pinFoot s B.S) (P.pinFoot s (plow K j b C.S)):=by
 refine Set.disjoint_left.mpr ?_
 rintro z ⟨x,px,hx⟩ ⟨y,py,hy⟩
 have ux:(x j)+(K).ℓ < y j - (K).ℓ:= by
   have hp: x j+ (K).ℓ ≤ u*B.w:=(B.fits j x px).2
   have hu: u*(b:ℤ)+(-u*C.w)+(K).ℓ ≤ y j:=(Between.relocate _ _ (C.fits j) b y py).1
   have he: 0<u:=ruler_gene _
   unfold bridge at hu; push_cast at hu;-- push_cast touches +ℓ?
   linarith only [hp,hu,he]
 have u₁: precisionAt P.par s*((2:ℝ)•z) j -(x j:ℝ) ≤ (K).ℓ:=(abs_le.mp (hx j)).2
 have u₂: - ((K).ℓ:ℝ) ≤ precisionAt P.par s*((2:ℝ)•z) j -(y j:ℝ):=(abs_le.mp (hy j)).1
 have : (x j:ℝ) + (K).ℓ < y j - (K).ℓ:=by exact_mod_cast ux
 linarith only [u₁,u₂,this]

def clasp : P.Glaze:=
 { w:= b+C.w
   pos:= by unfold bridge; omega
   S:= B.S ∪ plow K j b C.S
   F:= B.F *σ b C.F
   inlet:= Subalgebra.mul_mem _ (tallerBay _ _ true subset_union_left B.inlet)
     (tallerBay _ _ true subset_union_right (P.shifts_support _ _ _ C.inlet))
   color:= (enclave K).mul_mem B.color (P.shifts_keep _ _ C.color)
   fits:= (B.fits.mono (v:= b+C.w) (by unfold bridge; omega)).union (C.fits.relocate _ _ (by omega) (by omega)) }

lemma meanBox_stretch_le (p:P.BEntry j w f)(s n m v:ℕ)(z:ℤ)(h:v=n+w+m)(q:z=n):
    ‖P.meanBox j s v (σ z f)‖ ≤ ‖P.meanBox j s w f‖:= by rw [h,q]; exact meanBox_pad_le s p n m
lemma tile_swell (p:B.w ≤ d)(s:ℕ): ‖(B.swell p).tile j s‖≤ ‖B.tile j s‖:=by
 let n:=d-B.w; have u₀ : n+B.w=d:=Nat.sub_add_cancel p
 have e := meanBox_stretch_le j (B.centers j) s n n (d+d) n (by omega) (by rfl)
 rw [shifts_sum,←Nat.cast_add,u₀] at e; exact e
lemma tile_clasp (s:ℕ):
   ‖(B.clasp C j).tile j s‖ ≤ ‖B.tile j s‖*‖C.tile j s‖:=by
 let R:=b+C.w
 let n:=1+C.w+C.w
 let A:= n+(B.w+B.w)+1
 have hr :n+B.w=R:=by unfold n R bridge; omega
 have hz: A+C.w=R+b:=by unfold A bridge R n; omega
 have h:P.BEntry j A (σ R B.F):=by
    have he:=(B.centers j).pad n 1; rw [shifts_sum,←Nat.cast_add,hr] at he; exact he
 have g:P.BEntry j (C.w+C.w) (σ C.w C.F):=C.centers j
 have ht:= meanBox_stretch_le j (B.centers j) s n 1 A n rfl rfl
 rw [shifts_sum,←Nat.cast_add,hr] at ht
 change ‖P.meanBox j s (R+R) (σ R (B.F* σ b C.F))‖≤_
 rw [show R+R=A+(C.w+C.w) by unfold R A bridge n;omega,map_mul,show σ R (σ b C.F) = σ A (σ C.w C.F) by rw [shifts_sum,shifts_sum,←Nat.cast_add,←hz,Nat.cast_add],meanBox_concat s h g]
 exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
end Glaze
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
