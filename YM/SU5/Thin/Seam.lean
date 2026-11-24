import SatinFixedContrastNovember4
import YM.SU5.Thin.Geometry

/-!
# Smeared fields in a single wall experiment -- seam receipts

Field-on-vacuum formalism for testing products in two separated Euclidean
regions. All prices in `ColorHil` (or explicitly coming through spatial
continuum `ManyF` for ordinary center densities). No operator-algebra
limits, no use of sharp-time fields. The later limit here is appropriate for
a *two*-field experiment and its exact split test. This is not enough, for
example, to remove any of the width qualifiers on the algebra as a whole.

Formulate generic apron lemmas (building on library at fixed widths, in
particular generalizing parts of `Six.TransitWall`, `FineRays`; reproduced
some proofs) to make it easy to test alternative birth-supported thin fields.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
section poses
variable (P:Spine) (x:P.Spectrum0 3) (A:P.Apron) (p:P.birthF 3 A.s A.F) (t:ℕ) (k:Cover)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "H'" => P.ColorHil 3 ξ
local notation "H" => P.ManyF 3 ξ
local notation "μ" => P.physicalEnergy 3 ξ
local notation "ν" => P.seasons 3 ξ
local notation "E'" => (μ).E
local notation "E" => (ν).E
local notation "ω" => P.colorZero 3 ξ
local notation "u" => P.meshPose t
local notation "w" => A.realWidth P 3
local notation "G" => P.viewF 3 ξ A.s p

/-- World-grid prepaid point vector. Poses quoted only sufficiently late in
axis 3 (for wall budget). Works for *any* already born-on-positive-side
Apron, not just our width prescription. -/
def wallPoint (v:P.ColorHil 3 (P.otherSpectrum 3 3 x)) : H' :=
  P.truck 3 ξ (P.vtile t k) (E' (u k 3).toNNReal v)

include p
lemma born_entry : A.engine P 3 ξ ω = E' ((w).toNNReal) G:= by
  have he: whenly (timeMesh P.par) A.s (A.u 3)=(w).toNNReal:= by
    change whenly _ _ _=(bell _ _ (A.u 3)).toNNReal
    rw [natural_time]; exact Real.toNNReal_coe.symm
  refine (P.engine_view 3 ξ A).trans ((P.identical_F 3 ξ A.s _
    (P.passesLater 3 A.s (A.u 3) p) (A.card_price P 3)).trans ?_)
  exact (P.releasedLater 3 ξ A.s _ p).trans (congrArg (fun t:ℝ≥0=> E' t G) he)

omit p in
private lemma gains (X:Hilbert) (S:OS.Semigroup X (3:Axis)) (x:X) (a b:ℝ) (h:0≤a) (q:a≤b) :
    S.E ((b-a).toNNReal) (S.E a.toNNReal x) = S.E b.toNNReal x := by
  have ht: b.toNNReal=(b-a).toNNReal+a.toNNReal := by
    ext; simp [h,show 0≤b from h.trans q, sub_nonneg.mpr q]
  rw [ht,S.time]; rfl
lemma born_charter (e:w ≤ u k 3) :
    E' ((u k 3 - w).toNNReal) (P.charter 3 ξ (P.vtile t k) (A.engine P 3 ξ) ω)= P.wallPoint x t k G :=
  let a:=(u k 3 - w).toNNReal
  let Y:= A.engine P 3 ξ ω
  let U:= P.truck 3 ξ (P.vtile t k)
  (congrArg (fun v:H'=> E' a v) (P.raw_aperture 3 ξ (P.vtile t k) A)).trans
    ((P.sixWard_truck_heat 3 ξ (P.vtile t k) a Y).symm.trans
      (congrArg (fun v:H'=> U v) ((congrArg (fun z:H'=> E' a z)
        (P.born_entry x A p)).trans (gains H' (μ) G _ _ (A.real_width_pos P 3).le e))))
omit p in
lemma cruise_from_wall (F:P.Test)(L:List (Trans (3:Axis))) :
    P.cruise (Vacancy.spare 3 L) k F=P.luggage 3 L (fun i=> k (i:Axis)) F := by
  induction L with
  | nil => rfl
  | cons i L ih => rw [show Vacancy.spare 3 (i::L)=i.val::(Vacancy.spare 3 L) from rfl,P.cruise_step, P.ship_started, AlgHom.comp_apply,ih]
lemma bornWall_tick (d:ℕ)(b:k 3=(d:ℤ)) (h:A.s≤t):
    ∃ a:P.birthF 3 t (P.issuing t A k), P.viewF 3 ξ t a=P.wallPoint x t k G := by
  let M:= timeMesh P.par; let a:=whenly M t d; let T:=P.truck 3 ξ (P.vtile t k)
  let F:=A.full P t; let Ht:=P.rig 3 A.s t p h
  let J:=P.passesLater 3 t d Ht
  let L:= look (3:Axis)
  let Y:= P.luggage 3 L (fun i=> k (i:Axis))
  let V:= Y (P.shifts 3 (d:ℤ) F)
  let e: P.birthF 3 t V:= P.certify 3 t L (fun i=> k (i:Axis)) J
  have hx : P.issuing t A k= V:=
    (P.chart_transverse 3 k F).trans
      ((congrArg (fun d':ℤ=>P.shifts 3 d' (P.cruise (Vacancy.spare 3 L) k F)) b).trans
        ((P.cruise_mesh 3 _ (d:ℤ) k F).symm.trans (P.cruise_from_wall k (P.shifts 3 (d:ℤ) F) L)))
  have ht: (u k 3).toNNReal=a:= by change (bell M t (k 3)).toNNReal=_; rw [b, natural_time]; exact Real.toNNReal_coe
  have g:P.viewF 3 ξ t e = T (P.viewF 3 ξ t J) := P.ship_ideal 3 ξ t L _ J
  let u' : P.birthF 3 t (P.issuing t A k):= hx.symm ▸ e
  exact ⟨u',(P.identical_F 3 ξ t _ _ hx).trans (g.trans
    (congrArg (fun v:H'=> T v) ((P.releasedLater 3 ξ t d Ht).trans
      ((congrArg (fun v:H'=> E' a v) (P.view_rig 3 ξ A.s t p h)).trans
        (congrArg (fun t:ℝ≥0=> E' t G) ht.symm)))))⟩
lemma bornWall (b:w < u k 3)(h:A.s≤t):
    ∃ a:P.birthF 3 t (P.issuing t A k), P.viewF 3 ξ t a=P.wallPoint x t k G :=
  let m:= k 3
  have hp : 0≤ m := (bell_le (timeMesh P.par) t 0 m).1 ((show bell (timeMesh P.par) t 0=0 by simp [bell]).trans_le ((A.real_width_pos P 3).le.trans b.le))
  P.bornWall_tick x A p t k m.toNat (Int.toNat_of_nonneg hp).symm h

omit p
variable (F:SampleDose)
def wallSignal (v:H') : H' :=
  ∑ i ∈ P.usedGrid t F, P.activation t F i • P.wallPoint x t i v
def wallRay (v:H') (q:Vantage) : H :=
  (P.cartage 3 ξ q) (P.wealth 3 ξ (E' (q 3).toNNReal v))
/-- Ordinary position-smearing (on the projected sector, result in the original space).
This is at a *fixed* footprint, seam 0. Only applied when `A.F` satisfies `birthF`
and the test fits in the forward domain with feet. -/
def wallContinuum (v:H') : H' := (P.enter 3 ξ) (∫ q:Vantage,(F.val q:ℂ) • P.wallRay x v q)

lemma wallRayContinuous (v:H') : Continuous (P.wallRay x v) :=
  P.caravan 3 ξ id _ continuous_id ((P.wealth 3 ξ).continuous.comp
    (((μ).continuousE v).comp (continuous_real_toNNReal.comp (continuous_apply 3))))

lemma wallRayIntegrable (v:H') : Integrable (fun q => (F.val q:ℂ) • P.wallRay x v q) :=
  weightedMoney F H _ (P.wallRayContinuous x v)

include p
lemma posed_birth (a:P.WallAfter A F 0) (h:A.s≤t) (q:k ∈ P.usedGrid t F) :
    ∃ aM:P.birthF 3 t (P.activation t F k • P.issuing t A k),
    P.viewF 3 ξ t aM= P.activation t F k • P.wallPoint x t k G :=
  let e:=(zero_add w).symm.trans_lt (a (u k) ((P.usedPose t F k).mp q))
  let J:=P.bornWall x A p t k e h
  ⟨P.birthScale t (P.activation t F k) J.choose,
    (P.sixWard_view_scale ξ t (P.activation t F k) J.choose).trans
      (congrArg (fun z:H' => P.activation t F k • z) J.choose_spec)⟩
lemma seam_signal_birth (a:P.WallAfter A F 0) (h:A.s≤t) :
    ∃ aM:P.birthF 3 t (P.prepared t A F), P.viewF 3 ξ t aM= P.wallSignal x t F G :=
  P.birthSum ξ t (P.usedGrid t F) (fun i=> P.activation t F i • P.issuing t A i)
    (fun i=> P.activation t F i • P.wallPoint x t i G)
    (fun i hi=> P.posed_birth x A p t i F a h hi)
omit p

open MacroGrid
-- as in FineRays
private lemma pose_grid (X:Hilbert)(f:Vantage→X)(T:Cover → X.Op):
 MacroGrid.poseApprox X (fun z:Vantage=>(F.val z:ℂ) • f z) T (P.macroStep t) =
   ∑ i∈ P.usedGrid t F, P.activation t F i • T i (f (u i)) := by
 let g:=fun i:Cover=> T i ((F.val (u i):ℂ) • f (u i))
 have he(i:Cover)(x:i∉P.usedGrid t F): g i=0:= by
    have hu : F.val (u i)=0:=by by_contra p; exact x ((P.usedPose t F i).2 (subset_closure p))
    unfold g; rw [hu,Complex.ofReal_zero,zero_smul,map_zero]
 refine (room_price _ (P.macroStep_pos t) g (P.usedGrid t F) he).2.trans ?_
 rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i h
 unfold g
 rw [map_smul,show Fintype.card Axis=4 by rfl, ← Complex.coe_smul ((P.macroStep t)^4), smul_smul]
 push_cast [activation]; rfl

lemma at_seam (J:P.Ellis 3 x) (v:H') :
    Tendsto (fun t=> P.wallSignal x t F v) atTop (𝓝 (P.wallContinuum x F v)) := by
 let g(q:Vantage):H':= (F.val q:ℂ) • E' (q 3).toNNReal v
 let f(q:Vantage):= E' (q 3).toNNReal v
 have he: HasCompactSupport g := F.budget.mono (fun i u' t=> u' ((congrArg (fun b:ℝ=> (b:ℂ) • (f i))
    (show F.val i=0 from t)).trans (zero_smul ℂ _)))
 have ht: Continuous g := (Complex.continuous_ofReal.comp F.smooth.continuous).smul
    (((μ).continuousE v).comp (continuous_real_toNNReal.comp (continuous_apply 3)))
 let Y:=fun p:Vantage=> P.cartage 3 ξ p (P.wealth 3 ξ (g p))
 have hp : P.wallContinuum x F v=P.enter 3 ξ (∫ p,Y p) := by
    refine congrArg (fun v:H=> P.enter 3 ξ v) (integral_congr_ae (Eventually.of_forall fun i=>?_))
    let U:=P.cartage 3 ξ i
    exact ((congrArg (fun v:H=>U v) (map_smul (P.wealth 3 ξ) (F.val i:ℂ) (f i))).trans
      (map_smul U (F.val i:ℂ) _)).symm
 let K:= P.enter 3 ξ (∫ p,Y p)
 have v' : Tendsto (fun t=> P.wallSignal x t F v) atTop (𝓝 K) :=
    (P.macroRiemann x 3 J g he ht).congr fun i => pose_grid P i F H' f (P.truck 3 ξ ∘ P.vtile i)
 exact Eq.mp (congrArg (fun y:H'=> Tendsto (fun t=> P.wallSignal x t F v) atTop (𝓝 y)) hp.symm) v'

end poses

section pairing
lemma flipAgain (F:SampleDose) (j:Axis) : flipDose (flipDose F j) j=F := by
  have aux (A B:SampleDose)(e:A.val=B.val) : A=B := by cases A; cases B; congr
  exact aux _ _ (funext fun x => congrArg F.val (reflectPose_twice j x))
variable (P:Spine) (x:P.Spectrum0 3)(F G:SampleDose) (A B:P.Apron) (t:ℕ)
local notation "ξ" => P.otherSpectrum 3 3 x
local notation "Θ" => P.reflectTest 3
local notation "M" => P.singleState 3 t x
local notation "ω" => P.colorZero 3 ξ

/-- Prepaid grid pairing uses the reflected pose of the earlier smear. -/
def rayEarlier (A:P.Apron) (a:P.birthF 3 A.s A.F) : P.ColorHil 3 ξ :=
  P.wallSignal x t (flipDose F 3) (P.viewF 3 ξ A.s a)
def rayLater (A:P.Apron) (a:P.birthF 3 A.s A.F) : P.ColorHil 3 ξ :=
  P.wallSignal x t F (P.viewF 3 ξ A.s a)

lemma mirrorPayment : P.prepared t (A.kiss P 3) F = Θ (P.prepared t A (flipDose F 3)) := by
  have h:= P.prepared_opposition t A (flipDose F 3) 3
  rw [flipAgain] at h; exact h
-- convert seam qualifications
lemma mirrorFits (h:P.WallBefore (A.kiss P 3) F 0) : P.WallAfter A (flipDose F 3) 0 := by
  intro i p
  let v:=A.realWidth P 3
  rw [flipBudget F 3] at p
  have hp : opposeR 3 i 3 + v < 0 := h (opposeR 3 i) p
  rw [show opposeR 3 i 3= -i 3 from if_pos rfl] at hp; change 0+v < i 3; linarith only [hp]

private lemma assembly_gram (X X' Y:P.Test) (Z W:P.ColorHil 3 ξ)
    (m:X=P.reflectTest 3 X') (h:P.birthF 3 t X') (p:P.viewF 3 ξ t h=Z)
    (k:P.birthF 3 t Y) (q:P.viewF 3 ξ t k=W) :
    M (X*Y)=inner ℂ Z W ∧ M X=star (inner ℂ ω Z) ∧ M Y=inner ℂ ω W :=
  let hX : M X=star (M X'):= (congrArg (fun i=> M i) m).trans ((P.common_reading t x X' 3).2.2.1)
  let hX' : M X'=(inner ℂ ω Z) := (P.single_agrees 3 3 x t X').symm.trans
    ((P.view_scalar 3 ξ t h).symm.trans (congrArg (inner ℂ ω) p))
  let hY : M Y=inner ℂ ω W := (P.single_agrees 3 3 x t Y).symm.trans
    ((P.view_scalar 3 ξ t k).symm.trans (congrArg (inner ℂ ω) q))
  let he : M (X * Y)= P.singleState 3 t ξ ((P.reflectTest 3 X') * Y):=
    (congrArg (fun z:P.Test=> M (z*Y)) m).trans (P.single_agrees 3 3 x t ((P.reflectTest 3 X') * Y)).symm
  ⟨he.trans ((P.released_gram 3 ξ t h k).symm.trans (congrArg₂ (inner ℂ) p q)), hX.trans (congrArg star hX'), hY⟩

lemma seam_gram (a:P.birthF 3 A.s A.F)(b:P.birthF 3 B.s B.F)
    (v:A.s≤ t)(u:B.s≤t)(f:P.WallBefore (A.kiss P 3) F 0) (g:P.WallAfter B G 0) :
    let X:=P.prepared t (A.kiss P 3) F; let Y:=P.prepared t B G
    let Z:=P.rayEarlier x F t A a; let W:=P.rayLater x G t B b
    M (X*Y)=inner ℂ Z W ∧ M X=star (inner ℂ ω Z) ∧ M Y=inner ℂ ω W :=
 let h:= P.seam_signal_birth x A a t (flipDose F 3) (P.mirrorFits F A f) v
 let k:= P.seam_signal_birth x B b t G g u
 assembly_gram P x t _ _ _ _ _ (P.mirrorPayment F A t) h.choose h.choose_spec k.choose k.choose_spec
end pairing
#print axioms bornWall
#print axioms wallRayIntegrable
#print axioms at_seam
#print axioms seam_gram
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
