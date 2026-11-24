import YM.SU5.Reconstruction.FirstWindows.Unwrap
import YM.CF.Lattice.Symbol
import YM.CF.Emu.Pin
/-!
# Chiral prescription on the shared sharp paths

Spend the same UV denominators on ALL local tests. Their advanced realizations
really read overlap-det-line chiral SU gauge-CAR marks, not merely transform
according to a desired group representation. We give also a pointwise conversion
of this theory's sharp integrands to the FiniteGaugeData Grassmann convention (Berezin coefficient
`zap`, matrix `chemical`):

* no inversion of the propagator; even rectangular or singular cases;
* use the true phase on the determinant line from the prescribed Grasp in this conversion;
  never assume frames to be continuous, or suppress the phase;
* `tube` works in common Single frame (same matter matrix for all generations).

This calculation is at any paying top, NOT yet demonstrating the same chirality of
fields after a relativistic reconstruction. Adapt the arbitrary-period Grassmann
identification in `CF/Emu/Pin.artQ` & `CF/Reed/Play` (using our purchases here,
not assuming `Span`) to the *actual election* and check the tests flowing through to
this horizon. Document the exact spin/role convention by `Reed.think, Emu.halfS`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase
  Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra

lemma halfSet_here (n : Side) : Emu.halfS n = Tset n := by
  ext ⟨⟨a,b⟩,c⟩
  rw [Window.mem_Tset]
  simp [Emu.halfS]

-- Pointwise candidate marks across **all** levels. Even syntax includes
-- assemblies from all three pairs of matter reps. Document role of +/-
-- (`creation` and `removal` include winding; `think` basis sign paid for reading).
theorem basis_incidence (n : Side) (a : Site n) (i : SpinIdx) (l : SU.Slot) :
    (((a,i),l) ∈ Tset n ↔ i ∈ plusHalf) ∧
      (Reed.think (Tset n)).term ((a,i),l) = if i∈plusHalf then put ((a,i),l) else -takeF ((a,i),l) := by
  refine ⟨Window.mem_Tset ..,?_⟩; simp [Reed.think,Window.mem_Tset]

theorem writer {N : Side} {S : Support (More N)} {b : Bool} (x : Fields N) (f : Mark N) (p : AtSupport b S f) :
    ∃ g : FC (Single N), Reed.Absorb (modesIn N S) g ∧ f x = (Reed.think (Tset N)).eval g :=
  (p.allV x).writer

variable (m k' : ℕ)
local notation "M" => Journey.side Y m (Y.uv k')
set_option quotPrecheck false
local notation "Lx" => ((Y.voyage m).CapeT (Y.uv k'))
local notation "pB" => Y.meter.a (Y.uv k')
local notation "Gz" => ((Y.voyage m).X (Y.uv k')).gram (Y.uv k')
local notation "η" => Vale.mesh (Y.ir m) Λ.R.L (Y.uv k')

variable (x : Pane (Journey.side Y m (Y.uv k')))
variable (p : RG.flags (Y.meter.a (Y.uv k')).threshold x = ∅)

local notation "A" => Tset (Journey.side Y m (Y.uv k'))
local notation "B" => spar Λ.K.j Vale.babyM x
local notation "D₁" => frame SU.matter (Cube.links x) (anticut (Journey.side Y m (Y.uv k')))

include p

lemma topSafe : Safe (frame SU.matter (links x) (anticut M)).H := by
  have hx := PhaseChoice.guardedTop Y m k' x p
  exact Phase.wiel_ok (anticut (CSide η Λ.block)) Λ.U.baseY hx

lemma band_mask : B = portW (Tulip.helix M).symm (projector (D₁).H) := (Y.equity m k' x p).1

lemma oneSea : Sea B (changeM (m:=η) Λ.U x Vale.babyM) := (Y.equity m k' x p).2

lemma band_frame : ∃ (V : UNI (Single (Journey.side Y m (Y.uv k')))) (T : Finset (Single (Journey.side Y m (Y.uv k')))),
    B=twist V (cutM T) := by
  apply Fock.spot_projection
  rw [band_mask Y m k' x p]
  exact carts_p (helix M).symm (topSafe Y m k' x p).projection

lemma direction_columns : Emu.plantH x * B = cutM (Tset M) * B := by
  rw [band_mask Y m k' x p, ← Spire.touchP]
  let W := love M
  change W (D₁).overlap * W (projector (D₁).H) = W (cutM (upperP M)) * W (projector (D₁).H)
  rw [←map_mul,←map_mul]
  exact congrArg W (Reed.kinetic (PhaseChoice.guardedTop Y m k' x p) Λ.U.baseY (anticut (CSide η Λ.block)))

variable (Vw : UNI (Single (Journey.side Y m (Y.uv k'))))
  (S : Finset (Single (Journey.side Y m (Y.uv k'))))
  (e : spar Λ.K.j Vale.babyM x =twist Vw (cutM S))
local notation "ψ" => changeM (m:=Vale.mesh (Y.ir m) Λ.R.L (Y.uv k')) Λ.U x Vale.babyM

omit p in
noncomputable def phaseInFrame : ℂ :=
  star (inner ℂ (basisKet (Tset (Journey.side Y m (Y.uv k')))) (mateK (Journey.side Y m (Y.uv k')))) *
  inner ℂ (Fock.wedge Vw.val S) (changeM (m:=Vale.mesh (Y.ir m) Λ.R.L (Y.uv k')) Λ.U x Vale.babyM)
local notation "z₀" => phaseInFrame Y m k' x Vw S

include p e

lemma overlap_columns :
    Reed.chemical ((Emu.plantH x)*Vw.val) (Tset (Journey.side Y m (Y.uv k'))) S =
      Reed.chemical Vw.val (Tset (Journey.side Y m (Y.uv k'))) S := by
  have he : B * Vw.val = Vw.val * cutM S := by rw [e]; exact twist_product ..
  let Kc := Emu.plantH x
  have hv : Kc * Vw.val * cutM S = cutM A * Vw.val * cutM S := by
    rw [mul_assoc,mul_assoc,←he,←mul_assoc,←mul_assoc, show Kc*B=cutM A*B from direction_columns Y m k' x p]
  have hk i j (h : i ∈ A) (t : j ∈ S) : (Kc * Vw.val) i j=Vw.val i j := by
    have hh := Matrix.ext_iff.mpr hv i j; rw [cutM,Matrix.mul_diagonal,Matrix.mul_diagonal,if_pos t, mul_one,mul_one,cutM,Matrix.diagonal_mul,if_pos h,one_mul] at hh; exact hh
  unfold Reed.chemical; congr 1; apply sum_congr rfl; intro i h
  congr 1; unfold Reed.tote; refine sum_congr rfl fun t u=>?_; rw [←hk i t h u]

set_option maxHeartbeats 1200000 in
lemma sea_phase_split :
    let a:= inner ℂ (basisKet (Tset M)) (mateK M)
    let b:= inner ℂ (Fock.wedge Vw.val S) ψ
    ‖a‖=1 ∧ ‖b‖=1 ∧ ‖z₀‖=1 ∧ mateK M=a • basisKet (Tset M) ∧ ψ=b • Fock.wedge Vw.val S := by
  intro a b
  have he : Sea (cutM A) (mateK M) := (touchP M) ▸ tickB M
  have hv : Sea (twist Vw (cutM S)) ψ := e ▸ oneSea Y m k' x p
  let u := Fock.wedge Vw.val S
  have hx : ψ = b • u := hv.1.symm.trans (act_twistLine ..)
  have hy : mateK M = a • basisKet A := by
    apply he.1.symm.trans; rw [cutLine,cut_oneAct]; unfold a; rw [basis_inner]
  have hp : ‖a‖=1 := by
    have H := he.2; rw [hy,norm_smul,show ‖basisKet A‖=1 by simp [basisKet],mul_one] at H; exact H
  have ht : ‖b‖=1 := by
    have H := hv.2; rw [hx,norm_smul,show ‖u‖=1 from wedge_norm ..,mul_one] at H; exact H
  exact ⟨hp,ht,(by change ‖star a * b‖=_; rw [norm_mul,norm_star,hp,ht,one_mul]),hy,hx⟩

lemma chiral_cost (X : FC (Single (Journey.side Y m (Y.uv k')))) (t : Reed.Plain X) :
    z₀*Reed.spell (Reed.syms (Tset M)) Vw.val (Tset M) S X =
      inner ℂ (mateK M) (acts ((Reed.think A).eval X) ψ) := by
  have hh := sea_phase_split Y m k' x p Vw S e
  let a := inner ℂ (basisKet (Tset M)) (mateK M)
  let b := inner ℂ (Fock.wedge Vw.val S) ψ
  rw [Reed.moment _ _ _ _ t]; change star a * b * _ = _
  rw [show mateK M = a • basisKet A from hh.2.2.2.1, show ψ = b • Fock.wedge Vw.val S from hh.2.2.2.2,
    map_smul,inner_smul_left,inner_smul_right,mul_assoc]; rfl

-- Actual normalized numerator can use this pointwise identity inside the ONE integral.
-- Although `Vw` choice not used for measurability, left integrand is the actual one.
lemma bare_mark (y : Orbit M) (q : y.1=x) {T : Support (More M)}
    (f : Mark (Journey.side Y m (Y.uv k'))) (g : AtSupport false T f) :
    ∃ P : FC (Single (Journey.side Y m (Y.uv k'))), Reed.Absorb (modesIn M T) P ∧
      f (drawn Lx y) = (Reed.think (Tset M)).eval P ∧
      let K0 := denZ Gz Λ.U Lx y; let B0 := Vale.basicP Λ.K.top.clip x
      inner ℂ (Dial.mateK M) (acts (f (drawn Lx y)) K0) =
        Complex.exp (-(((Gz).beta*B0 : ℝ):ℂ)) * (phaseInFrame Y m k' x Vw S * Reed.spell (Reed.syms (Tset M)) Vw.val (Tset M) S P) := by
  obtain ⟨X,h,P⟩ := writer (drawn Lx y) f g
  refine ⟨X,h,P,?_⟩
  intro K' B'; unfold K'
  rw [P,chiral_cost Y m k' x p Vw S e X (h.packs (Finset.subset_univ _)),Y.whole m k', capP, q, Set.indicator_of_mem (show x∈_ from p),map_smul,inner_smul_right]

omit e p

lemma bare_dark (y : Orbit (Journey.side Y m (Y.uv k'))) (f : Mark (Journey.side Y m (Y.uv k'))) (q : RG.flags (pB).threshold y.1 ≠ ∅) :
    inner ℂ (mateK M) (acts (f (drawn Lx y)) (denZ Gz Λ.U Lx y)) = 0 := by
  rw [Y.whole, capP, Set.indicator_of_notMem (show y.1∉_ from q),map_zero,inner_zero_right]


-- `creation`, `removal`: test generators are gauge-covariant program ingredients
-- (not asserting singlets). The literal sign convention in the source should be
-- unambiguous when referring from an external lattice/Grassmann language. Costs
-- transmit on every monomial in arbitrary order using InTest.mul. Relate both
-- letters to token Eval, no assertion about continuation of odd words alone.
variable (J : Calibration) (n : Side) (c : Cover) (b : SpinIdx) (l' : SU.Slot)

lemma creation_rule (p : b ∈ plusHalf) (v : Fields (J.c n)) :
    creation J c b l' n v = (Lifted.winding (J.c n) c) •
      (Reed.think (Tset (J.c n))).eval (put (Lifted.index (J.c n) c b l')) := by
  rw [Reed.eval_blade]; change create _ = _
  rw [show (Reed.think (Tset (J.c n))).term (Lifted.index (J.c n) c b l') = put (Lifted.index (J.c n) c b l') from if_pos ((Window.mem_Tset ..).2 p), basisC,map_smul, create_put] -- create_put direction

lemma removal_rule (p : b ∉ plusHalf) (v : Fields (J.c n)) :
    removal J c b l' n v = -(star (Lifted.winding (J.c n) c)) •
      (Reed.think (Tset (J.c n))).eval (put (Lifted.index (J.c n) c b l')) := by
  rw [Reed.eval_blade]; change Fock.remove _ = _
  rw [show (Reed.think (Tset (J.c n))).term (Lifted.index (J.c n) c b l') = -takeF (Lifted.index (J.c n) c b l') from if_neg (fun t=>p ((Window.mem_Tset ..).1 t)), basisC, Fock.remove, map_smul, star_smul,create_put,takeF, neg_smul,smul_neg, neg_neg] -- ambiguity

-- Left-handed here at launch means minus grading at free-symbol zero,
-- with the stated pole mask on overlap H across actual links. This doesn't
-- mean the spectrum of excitations already carries a spinor representation
-- or that odd/taste translations identify. Include exact checks used above.
theorem at_origin : projector (BZ.atom 0).H=1-(BZ.atom 0).plus ∧
    (BZ.atom 0).chir * projector (BZ.atom 0).H = -projector (BZ.atom 0).H ∧
    (BZ.atom 0).overlap * projector (BZ.atom 0).H=0 := by
  refine ⟨BZ.origin.1,?_,BZ.origin.2⟩
  rw [BZ.origin.1,mul_sub,mul_one,WilsonFrame.chirPlus,WilsonFrame.plus]; module
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
