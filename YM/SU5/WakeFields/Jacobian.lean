import YM.SU5.WakeFields.CrossMoment
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.CrossMoment
open Filter Metric Function MeasureTheory Finset
open Lat Cube Lattice Wilson Fock Satin Py Rate LocalLimit Preparation Yoke
open Jewel.Program Ballad EmberWind
open Hiro (ColorL)
open Onyx (riseX)
open YM.Stationary (Gaia)
open Regis.Circuit Regis.Head.Brecht
open EmberWind.MixedCards MixedCards.Receipt Twah
open Emu -- maybe use SpinTable qualify
open SpinTable (rentBoth rentOne total total2 entry spinPlane body2 body4)
open Window (colors family)
open YM.WakeFields
open scoped Topology BigOperators Matrix MatrixOrder Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

local notation "Ω" => SU.group.ColorIndex
local notation "ϰ" => SU.Slot
local notation "Holo" => Lead.Clan
-- four-point collinear slanted spacelike example. axis3 time. all axes separated.
local notation "Site₄" => Fin 4
def factorT : Site₄ → ℝ := ![-5/2,-3/2,3/2,5/2]
def spot4 (x:Site₄) : Gaia := factorT x • incline
lemma spots(i j:Site₄) : spot4 i-spot4 j=(factorT i-factorT j) • incline:= by unfold spot4; rw [sub_smul]
lemma spot_non (i j:Site₄) (h:i≠j) : spot4 i ≠ spot4 j:=by
  intro v; have ht := sub_eq_zero.mpr v; rw [spots] at ht; rcases smul_eq_zero.mp ht with t | t
  · fin_cases i <;> fin_cases j <;> first | exact h rfl| norm_num [factorT] at t
  exact inclined t
lemma allSpots : Injective spot4:= injective_iff_pairwise_ne.mpr (fun i j v=> spot_non i j v)
abbrev trajectory : Fin 4 → PlaqAxes:= fun _=> primary
abbrev polarization : (Fin 4 → DirSpin) := fun _=> Spine.pairMood
lemma core_t : orbit trajectory spot4 0 1≠0:=by
 open Regis.Circuit in
 intro H; apply (norm_pos_iff.mp claim_pos); unfold orbit trajectory at H
 rw [spots] at H; have hξ: factorT 0 - factorT 1= -1:= by norm_num [factorT]
 rw [hξ,neg_one_smul] at H
 unfold claim shot lower speckleV acePower; rw [zero_sub,H]; ring
abbrev PPrice (x:Gaia) := (8:ℂ)*Cordial.kP20 x
lemma kP_cost (x:Gaia) (w:ℝ) : PPrice (w • x)=(w:ℂ)⁻¹^3*PPrice x:=by
 unfold PPrice Cordial.kP20 Onyx.pencil; rw [norm_smul]; simp_rw [Matrix.smul_apply,Cordial.quaternion,PiLp.smul_apply]; simp only [smul_eq_mul,Complex.real_smul] -- oops smul_eq_mul after
 by_cases h:w=0
 · subst w; norm_num
 rw [mul_pow, mul_comm (Real.pi^2) (‖w‖^4*_),mul_assoc (‖w‖^4),mul_inv_rev,Real.norm_eq_abs, ←abs_pow,abs_of_nonneg (by positivity : 0 ≤ w^4)]; -- try tune
 by_cases v:x=0; · subst x; simp
 have hx:‖x‖≠0:=(norm_pos_iff.mpr v).ne'; have hw:Real.pi≠0:=Real.pi_pos.ne'
 push_cast; field_simp
lemma penAxis (i j:Site₄) : pen polarization spot4 i j = (PPrice incline)/(factorT i-factorT j:ℝ)^3:=by
 change PPrice (spot4 i-spot4 j)=_; rw [spots,kP_cost,div_eq_mul_inv, mul_comm,inv_pow]
lemma halo_spin : PPrice incline≠0:=by
 intro e; have h:= (norm_pos_iff.mp claim_pos);
 apply h; let v:= Cordial.kP20 incline; have he : v=0:= (mul_eq_zero.mp e).resolve_left (by norm_num : (8:ℂ)≠0)
 unfold claim shot lower Hiro.shotR; rw [zero_sub,neg_neg]; change 2^6*(-60*_*v)*_=0; rw [he]; ring
abbrev wakeForceBill := interference trajectory polarization spot4 spot4 0 1 2 3
lemma count_spin : Emu.SpinTable.realPlane (pen polarization spot4) 0 1 2 3= -(PPrice incline)^4 / 9600 := by
 unfold Emu.SpinTable.realPlane; simp_rw [penAxis]
 norm_num [show factorT 2=3/2 from rfl,show factorT 3=5/2 from rfl,show factorT 1=-3/2 from rfl,show factorT 0=-5/2 from rfl]; ring
lemma opening : 0 < ‖wakeForceBill‖:=by
 apply norm_pos_iff.mpr; unfold wakeForceBill interference; rw [count_spin]
 exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr core_t) (by norm_num)) (mul_ne_zero (by norm_num) (by exact_mod_cast units_pos.ne'))) (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ halo_spin)) (by norm_num))
-- cells and diagram.
open Tapestry
open Reconstruction
def rowX (d u v:ℝ) : Set RSpace:= {x| ∀ i, d*u*incline i-d/8 ≤ x i ∧ x i ≤ d*v* incline i+d/8 }
-- small, all positions neighborhoods. For progression shadow use apartment.
lemma shadow_spot (i:Site₄) (d:ℝ): cellAt (spot4 i) d (1/8) ⊆ rowX d (factorT i) (factorT i):=by
 intro x h j; have hv := abs_lt.mp (h j); rcases hv with ⟨p,u⟩
 unfold spot4 at p u; change -_ < x j-d* (factorT i* incline j) at p; change x j-d*(factorT i*incline j)< _ at u; constructor <;> linarith
lemma factor_pos (i:Axis) : 1 ≤ incline i:=by rw [incline_eq]; split<;> norm_num
lemma enlargeRow (d u v w z:ℝ)(t:0<d)(h:u≤v)(r:w≤z): rowX d v w ⊆ rowX d u z:=by
 intro x px i; have hi:= zero_le_one.trans (factor_pos i); constructor; · exact le_trans (by gcongr) (px i).1
 exact (px i).2.trans (by gcongr)
lemma slantRows (u v w z d:ℝ)(h:0<d)(t:v+1≤ w)(g: z-u ≤ (w-v)*6-2): Slant (d/2) (rowX d u v) (rowX d w z):=by
 intro x xv y yv; have he (i:Axis): x i + d/2 < y i:=by
    obtain ⟨a,b⟩:=xv i; obtain ⟨p,g⟩:= yv i; have he: d*v*incline i+d≤d*w*incline i:=by
       rw [←sub_nonneg]; have t:1≤w-v:= (by linarith only [t]); nlinarith only [mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le t (factor_pos i)) h.le]
    linarith only [he,b,p,h]
 refine ⟨he,?_⟩
 have hi₂ : incline 2=6:= by simp [incline_eq];
 have hi₃: incline 3=1:=by rw [incline_eq,if_neg (by decide)]
 obtain ⟨x₃,b⟩:=xv 3; obtain ⟨a,y₃⟩:=yv 3; have x₂: x 2 ≤ _ := (xv 2).2; have y₂:= (yv 2).1
 rw [abs_of_neg (by linarith only [he 3,h]: x 3-y 3<0)]
 rw [hi₂] at x₂ y₂; rw [hi₃] at x₃ y₃
 -- t condition g chosen equality? gap <= 6gap-1. y-x time ≤ +.25, spatial≥ -.25. slant δ=.5 -> if equality may ≤, not strict. strengthen g
 have hx:= mul_le_mul_of_nonneg_left g h.le; linarith only [hx,h,x₃,y₃,x₂,y₂]

abbrev region_ (d:ℝ)(i j:Site₄):=rowX d (factorT i) (factorT j)
lemma diagram (d:ℝ)(h:0<d) : Slant (d/2) (region_ d 0 1) (region_ d 2 3) ∧
     Slant (d/2) (region_ d 0 0) (region_ d 1 1) ∧ Slant (d/2) (region_ d 2 2) (region_ d 3 3):=by
 refine ⟨slantRows _ _ _ _ d h ?_ ?_,slantRows _ _ _ _ d h ?_ ?_,slantRows _ _ _ _ d h ?_ ?_⟩; all_goals norm_num [show factorT 2=3/2 from rfl,show factorT 3=5/2 from rfl,show factorT 1=-3/2 from rfl,show factorT 0=-5/2 from rfl]
lemma past (d:ℝ)(v:0<d) : ∀ x∈ region_ d 0 1,x (3:Axis) ≤ -d:=by
 intro x h; have he:= (h 3).2; rw [show factorT 1= -3/2 from rfl,show incline 3=1 from rfl,mul_one] at he; linarith
lemma future (d:ℝ)(v:0<d) : ∀ x∈ region_ d 2 3,d ≤ x (3:Axis) :=by
 intro x h; have he:= (h 3).1; rw [show factorT 2= 3/2 from rfl,show incline 3=1 from rfl,mul_one] at he; linarith
#print axioms allSpots
#print axioms opening
#print axioms diagram
#print axioms past
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.CrossMoment
