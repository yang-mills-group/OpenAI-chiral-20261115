import YM.SU5.Assay.Glaze
import YM.SU5.Assay.FlashGain
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
# Neumann mixing. Dress an arbitrary colorless stencil by M copies, in-axis, at same
height. The cost beats any exponential eventually when M=1+s²; the physical
support increment itself is going to zero.

The residual tag calibration here uses `Tasting.Paid` in the same physical
purchase; in particular `R.n` below is *not* a macroscopic arm or part of a
further launch. See flashTaste, front_read, etc. for the pedigree of `flash`.
-/
structure Reel (P:Spine)(j:Axis)(Z:Lead.Clan) where
 n:ℕ
 d:ℕ
 a:ℂ
 c:ℝ
 gap:P.calibration.ℓ<n
 paid:P.ResidualTag j (P.defaultR Z n) (P.flash n).patio d a c
variable {Z:Lead.Clan}
namespace Reel
lemma available {R:P.Register}{u v:ℝ}{X:Supplier}(e:uniform P R X u v)(p:Tasting.Paid P.par)(j:Axis)(Z:Lead.Clan):Nonempty (P.Reel j Z):=by
 obtain ⟨n,h,f⟩:=residualFlash Z e p
 obtain ⟨d,a,c,g⟩:=f j
 exact ⟨n,d,a,c,h,g⟩

variable (R:P.Reel j Z)(B:P.Glaze)
local notation "σ"=>P.shifts j
local notation "φ"=>P.defaultR Z R.n
def pressRoll : P.Glaze :=
 { w:= R.d
   S:= (P.flash R.n).patio
   F:= 1-R.a•φ
   pos:= R.paid.1
   inlet:= Subalgebra.sub_mem _ (one_mem _) ((bay ..).smul_mem (P.defaultBay ..) _)
   color:= Subalgebra.sub_mem _ (one_mem _) ((enclave K).smul_mem (P.defaultColor Z R.n) _)
   fits:= R.paid.2.2.2.2.1 }
local notation "Y"=>R.pressRoll
-- shadow:=subtracted piece
-- support paid by successive clasps
def dusk : (M:ℕ) → P.Glaze
 | 0 => B
 | M+1 => (dusk M).clasp Y j
lemma dusk_step (M:ℕ): R.dusk B (M+1)=(R.dusk B M).clasp Y j:=rfl
lemma dusk_span (M:ℕ): (R.dusk B M).w =B.w+M*(R.d+R.d+1):=by
 induction M with
 | zero=> simp [dusk]
 | succ M h=>change (R.dusk B M).w+1+R.d+R.d=_; rw [h,Nat.succ_mul]; omega
lemma dusk_larger (M:ℕ) : B.S⊆ (R.dusk B M).S:=by
 induction M with
 | zero=> exact fun _ h=>h
 | succ M h=> exact h.trans Finset.subset_union_left

def twist (M:ℕ) : P.Glaze where
 w:=(R.dusk B M).w
 pos:= (R.dusk B M).pos
 S:=(R.dusk B M).S
 F:=B.F-(R.dusk B M).F
 fits:=(R.dusk B M).fits
 color:=Subalgebra.sub_mem _ B.color (R.dusk B M).color
 inlet:= Subalgebra.sub_mem _ (tallerBay _ _ _ (R.dusk_larger B M) B.inlet) (R.dusk B M).inlet

def lane (m:ℕ):ℕ:= B.w+m*(R.d+R.d+1)+1+R.d
lemma literal (M:ℕ): (R.twist B M).F=B.F *
    (1-∏i∈Finset.range M, σ (R.lane B i) (1-R.a•φ)):=by
 rw [mul_sub,mul_one]
 suffices h:(R.dusk B M).F=B.F *∏i∈Finset.range M, σ (R.lane B i) (1-R.a•φ) from congrArg (B.F-·) h
 induction M with
 | zero=> simp [dusk]
 | succ M h=>
    let b:=R.lane B M
    change (R.dusk B M).F* σ ((R.dusk B M).w+1+R.d:ℕ) (1-R.a•φ)=_
    rw [h,prod_range_succ,R.dusk_span B M,mul_assoc]; rfl
lemma dressed (s M:ℕ) : ((R.twist B M).apron s).Beams Z.2:=by
 induction M with
 | zero=> change B.F-B.F∈P.Beam s B.S Z.2; rw [sub_self];exact Submodule.zero_mem _
 | succ M h=>
    let V:= R.dusk B M; let b:=V.bridge Y; let S:=plow K j b (Y).S
    change B.F-(V.F*σ b (1-R.a•φ))∈P.Beam s (V.S ∪ S) Z.2
    rw [map_sub,map_one,mul_sub,mul_one]
    let z:= V.F * σ b (R.a•φ)
    rw [show B.F-(V.F-V.F * σ b (R.a•φ)) = (B.F-V.F) + z by unfold z; abel]
    change B.F-V.F∈P.Beam s V.S Z.2 at h
    have u: R.a•φ∈P.Beam s (Y).S Z.2:= Submodule.smul_mem _ _ (Beam.of_sensed (P.sensedDefault s _ _ R.gap))
    refine Submodule.add_mem _ (Beam.mono Finset.subset_union_left h) ?_
    unfold z; rw [mul_comm,Finset.union_comm]
    exact Beam.join (Beam.shift u j b) V.inlet (V.distancePin Y j s).symm

lemma shadow_tile (s M:ℕ)(e:‖(R.pressRoll).tile j s‖ ≤ R.c):
   ‖(R.dusk B M).tile j s‖ ≤ ‖B.tile j s‖*R.c^M:=by
 induction M with
 | zero=> simp [dusk]
 | succ M h=>
    rw [dusk_step,pow_succ,←mul_assoc]
    exact ((R.dusk B M).tile_clasp Y j s).trans (mul_le_mul h e (norm_nonneg _) ((norm_nonneg _).trans h))
theorem history : ∀ᶠ s:ℕ in atTop,∀ G:P.Glaze,∀ M:ℕ,‖(R.dusk G M).tile j s‖ ≤ ‖G.tile j s‖*R.c^M:=
 R.paid.2.2.2.2.2.mono fun s e G M=>shadow_tile R G s M e
end Reel
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
