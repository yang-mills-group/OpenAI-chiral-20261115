import YM.SU5.Relativistic.OddTrace
import YM.CF.Buffered.Place
/-! Based on Buffered.Place, realizing the phase and testing the same seam. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure Nacre Window Tulip Skye Brace
attribute [local instance] opCStarAlgebra

variable {m B n : Side} {c : Phase.Part m B} {e d a₁ a₂ : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "N" => CSide m B
local notation "Wμ" => wheel m B
local notation "β₀" => Brace.northZ m B

variable (i : Axis) (z : ℤ)

lemma liftOdd (B : Side) (f : Evaluation n) (w : ℕ)
    (h : ∀ x,Sector (modesIn n (Buffered.band n i (gaugeShift B z) w)) true (f x)) :
    ∀ x, Sector (modesIn n (Buffered.band n i 0 w)) true (liftShift i B z f x) := by
  intro x; apply north_sector _ _ _ (h _); apply prep_moves; intro x
  rw [show (gaugeShift B z)=2*(2*(↑B.val:ℤ)*z) from by unfold gaugeShift; ring]; simpa only [coverShift,zero_add] using (band_shift i 0 n (2*(↑B.val:ℤ)*z) w x)

lemma rephasedNorth (f : Evaluation N) (h : Envelope f) (w : LocalOn (Buffered.band N i (gaugeShift B z) 0 : Set _) f)
    (u : ∀ x, Sector (modesIn N (Buffered.band N i (gaugeShift B z) 0)) true (f x)) : HalfOdd i (rephased i z f) := by
  refine ⟨Girt.pole_w _ (toSeam m B i) ((breeze _).comp (cxC _)) (Env.along (liftShift_env i z B f h) measurable_fst),
    fun x=> toSeam_forward i (north_modes_eq i ▸ liftOdd i z B f 0 u x.1) rfl,?_⟩
  intro x y k; unfold rephased; apply congrArg; apply liftShift_local _ z B f 0 w; rw [band_zero]; exact k.gaugeS
lemma rephasedPair (f g : Evaluation N) (h : ∀ x,Sector (modesIn N (Buffered.band N i (gaugeShift B z) 0)) true (f x)) :
    rephased i z (Buffered.refl i (gaugeShift B z) f * g)=testProduct i (rephased i z f) (rephased i z g) := by
  funext x; unfold rephased testProduct; rw [liftShift_prod,Pi.mul_apply,toSeam_prod,liftShift_refl _ z B f _ _ h]
  unfold Buffered.refl; rw [carR_zero,fling_zero, toSeam_turn i (north_modes_eq i ▸ liftOdd i z B f 0 h _)]
  rfl

lemma rephasedScale (d:ℂ) (f:Evaluation N) : rephased i z (d • f) = d • rephased i z f:=by funext x; unfold rephased liftShift; rw [Pi.smul_apply, twist_scalar,toSeam_scalar]; rfl
variable (p : Pinning m B)(W : Scroll m B c)(clip : Clip)(β t u : ℝ)

section plt
variable (b : Budget B e d) (H : ScaleK a₁ a₂ W)
include H b
local notation "S" => Buffered.band N i (gaugeShift B z) 0
-- whole translated statement, pinning as in Manuscript
theorem top_Fermi (hu : 0 ≤ u) (f : Evaluation N) (h : Envelope f) (w : LocalOn (S:Set _) f)
    (w₀ : ∀ x,Sector (modesIn N S) true (f x)) :
    0 ≤ heatNum p W clip β t e u β₀ (insertTop (Complex.I • (Buffered.refl i (gaugeShift B z) f * f))) := by
  rw [rephased_eq i z p W,rephasedScale,rephasedPair _ z f f w₀]
  exact two_Fermi p W clip β t _ b H i β₀ hu _ (rephasedNorth i z f h w w₀)
end plt
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.top_Fermi
