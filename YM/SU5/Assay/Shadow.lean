import YM.SU5.Assay.Axle
import YM.SU5.Assay.Normal
import YM.SU5.Assay.WrapMix
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-!
# Full BSOT transfer of paid marks (just one axis). Absolute point price,
 also for marks not normal. Holds after removing *all* extra lag, up to
 the physical width of the mixed mark itself. Raw quadrature values at a
 fixed grid not asserted to have this price difference bound.
-/
variable {P j}{T:P.LagOp j x}{a b:ℝ}
local notation "β"=> P.base j x
local notation "τ"=> P.tock

namespace Glaze
def serial (G:ℕ→P.Glaze)(n:ℕ):= (G n).apron n
variable {G:ℕ→P.Glaze}
lemma Tiny.fades (t:Tiny G): P.Fades (serial G):=by
 intro i; exact t.congr (fun s=> ((G s).aperture s i).symm)
lemma Tiny.ofFade (p:P.Fades (serial G)):Tiny G:=by
 exact (p 0).congr (fun s=> (G s).aperture ..)
lemma Tiny.early (t:Tiny G)(h:0<a):∀ᶠ s in atTop,τ s (G s).w ≤ a:=
   (t.fades.one h 0).mono fun _ u=> u.le
lemma base_tile_pay (A:P.Glaze)(s:ℕ)(a b:ℝ): ‖β (A.apron s) a b‖≤ ‖A.tile j s‖:=P.base_cost ..
end Glaze

namespace Reel
variable {Z:Ballad.Lead.Clan}(r:P.Reel j Z)(A:P.Glaze)(s m:ℕ)
local notation "D"=> r.dusk A m
local notation "C"=> r.twist A m
lemma base_splice (u:τ s (D).w≤a)(v:τ s (D).w≤b):
 β ((C).apron s) a b= β (A.apron s) a b- β ((D).apron s) a b:=by
 have l:(A.apron s).u j ≤ (D).w:=by change A.w≤_;rw [dusk_span];omega
 rw [P.base_axle _ _ ((C).apron s), P.base_axle _ _ ((D).apron s)]
 have p: P.Focused j (D).w (D).F:=⟨(D).centers j,(D).color⟩
 exact (axle_sub x s (Focused.widen x l) p _ _).trans
   (congrArg (· - P.axle j x s (D).w (D).F a b) (axle_widen x s rfl l u v))
lemma splice_pay (u:τ s (D).w≤a)(v:τ s (D).w≤b):
 ‖β ((C).apron s) a b- β (A.apron s) a b‖≤ ‖(D).tile j s‖:=by
 let t:= β (A.apron s) a b; let y:=β ((D).apron s) a b
 have ht:t-y-t= -y:=by abel
 rw [r.base_splice x A s m u v, ht, norm_neg]
 exact Glaze.base_tile_pay ..
lemma habitual :∀ᶠ n:ℕ in atTop,∀g:P.Glaze,∀k:ℕ,
  ∀l≥τ n (r.twist g k).w,∀y≥τ n (r.twist g k).w,
  ∀ x:P.Spectrum0 j,‖P.base j x ((r.twist g k).apron n) l y-P.base j x (g.apron n) l y‖≤ ‖g.tile j n‖*r.c^k:=
 r.history.mono fun n e g k _ v _ t x=> (r.splice_pay x g n k v t).trans (e g k)
open Glaze in
lemma refine_normal {G:ℕ→P.Glaze}(h:Glaze.Grows j G)(p:P.Normal j x (serial G) T):
 P.Normal j x (serial (r.wrapMix G)) T:=by
 let t:=r.stays_tiny (Tiny.ofFade p.fades)
 refine p.viaDiff t.fades (r.shadow_vanish h) (fun a u b v=>?_)
 exact ((t.early u).and (t.early v)).mono fun s z=> r.splice_pay x (G s) s (ply s) z.1 z.2
end Reel
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
