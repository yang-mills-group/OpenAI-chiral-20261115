import Organdy.Album
import Organdy.Mansard
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset

open Regis Head Lattice Precision Wilson Pressure Work.F03 Exterior
open Larva (Chip Tint dot blush stains decree wet_iff)
variable {n N:Side}
local notation "G" => SU.group

open RG Gleam ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {M:Bed}{Z:PathData G}{q: Clip}{ρ θ v a η C:ℝ}



open Larva (dust Sky Spool) -- ?? capitalize
open Tempest Worth Pays BProof
open scoped Topology
open Next.Rank.Spindle

lemma dusted{a:ℝ}(c:ℝ)(h:0<a):
  ∀ᶠ x in atTop,c*Real.exp (-a*((radiusB x/10:ℕ):ℝ)) ≤ stow x:=by
   have p:=leap (Pays.scale (|c| *Real.exp a) (damp (a/10) (by positivity) (-3) 0 0))
        (w:=-2) (p:=0) (q:=0) (by norm_num [Earlier])
   filter_upwards [p] with x y
   refine le_trans (mul_le_mul_of_nonneg_right (le_abs_self c) (Real.exp_pos ..).le) (y.trans' ?_)
   rw [mul_assoc,←Real.exp_add]
   apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
   apply Real.exp_monotone
   have u: radiusB x ≤ (radiusB x /10)*10 + 10:= by omega
   have g: (radiusB x:ℝ) ≤ ((radiusB x / 10*10+10:ℕ):ℝ):=Nat.cast_le.mpr u
   push_cast at g
   linarith only [mul_le_mul_of_nonneg_left g h.le]

open Larva
lemma skyline{r a D d:ℝ}(R:Rules G)
    (h:Spool d r)(t:∀u,dust r u ≤ D*Real.exp (a*u))(p:0≤D):
  ∀ᶠ x:ℝ in atTop,∀ n:Side,4*(radiusB x/10+2) ≤ n.val →
      Sky n d r a D (temp x) (radiusB x/10) R:=by
 have s:= merit (constant 1) (w:=0) (p:=0) (q:=2) (by norm_num [Earlier])
 have v:=Pays.scale 16 (pot (plus (Pays.scale 2 (plus rising s)) s) 5)
 have c:=limit (times (Pays.right 2 (Pays.right (Fintype.card PlaqAxes:ℝ) v)) priceTemp)
    (by norm_num [Earlier])
 filter_upwards [
   c.eventually (gt_mem_nhds (lt_min R.radius h.1)),eventually_gt_atTop (0:ℝ)] with x b z n a
 have t₁:0≤temp x:=(thresh_eq z).symm ▸ (coin_pos ..).le
 refine ⟨h,by omega,p,t,t₁,?_⟩
 refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right (Payne.stretchMono (Nat.div_le_self (radiusB x) 10)) t₁) ?_
 unfold Payne.stretch
 push_cast
 exact b
