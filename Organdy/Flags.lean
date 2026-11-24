import Organdy.Byzantine
import Organdy.Amberlight
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell

variable {P:Spine}{c:Cuts}{s:ℕ}
local notation "Y'" => guineas P s
local notation "R✽" => shaft P s
local notation "H" => P.calibration
local notation "w✤" => walkF Y'
local notation "ε'" => yieldt Y'

lemma gilded (P:Spine) :∀ᶠ s in atTop, yieldt (guineas P s) ≤ 1:=
 (turnover P.par).eventually
 ((Pays.limit (Pays.whole 0 (-21500) 0)
    (by norm_num [Earlier])).eventually (ge_mem_nhds zero_lt_one))

lemma accessible{r:ℕ}(m:AmberMood P c s)(p:reach Y' r):
 drydock R✽ r ∧ 10*r≤w✤:=by
 obtain ⟨_,y⟩:=planted_plait m r p
 have w:=m.aisle
 have w₀:1≤ webX Y':=le_trans (by norm_num: (1:ℝ)≤8) w.gw
 have v:=w.depth
 have b:R✽≤R✽:=le_rfl
 have j:(0:ℝ)≤R✽:=Nat.cast_nonneg _
 refine ⟨?_,le_trans ?_ (w.yard (l:=0) y (by push_cast;linarith only [w₀]))⟩; swap; omega
 unfold drydock wireG
 apply Nat.cast_le (α:=ℝ)|>.mp
 push_cast

 let z:=webX Y'
 let q:ℝ:=shaft P s
 have h:q≤z:=by linarith only [v]
 have h₁:q^3≤z^3:=pow_le_pow_left₀ j h 3
 have g:=pow_le_pow_right₀ w₀ (show 6≤99 from by decide)

 have g₁:(8:ℝ)^3*z^3 ≤ z^6 :=by rw [←mul_pow,show z^6=(z*z)^3 by ring]; apply pow_le_pow_left₀ (by linarith) (mul_le_mul_of_nonneg_right w.gw (by linarith only [w₀]: (0:ℝ)≤webX Y')) 3
 have g₂:z≤z^3:=by simpa using pow_le_pow_right₀ w₀ (show 1≤3 from by decide) -- change defeq?
 have g₃:=y.1
 push_cast at g₃
 linarith only [j,h,h₁,w₀,g,g₁,g₂,g₃]

variable {d:Stores}{I:Type}{l:Filter I}{i k:I→ℕ}
abbrev placers (P:Spine)(s:ℕ)(i:I→ℕ):=∀ v, Mark (tunnel P s i v)
abbrev limits(P:Spine)(I:Type):=I→ Buffered.Family P.calibration

structure Bought (l:Filter I)(P:Spine)(c:Cuts)(s:ℕ)(i k:I→ℕ)
   (y:placers P s i)(f:limits P I)(g:P.Test):Prop where
  tagged:Gallon l P s i (station P s) y f g.val
  mounts:∀ᶠ v in l,∃ a:Blush (kitGap P s (i v)), Rouge P c s (i v) (k v) a∧ Coast (shaft P s) a.A.S ∧ a.A.x=y v

local notation "W" => walkF Y'
local notation "p₀"=> wireG R✽
variable (z:∀ v, Seating P c d s (i v) (k v))
abbrev company (z:∀ v, Seating P c d s (i v) (k v)): Clubs P s i:=fun v=>drew (z v)

include z

lemma controlled
  {y y':placers P s i}{f f':limits P I}{g g':P.Test}
  [l.NeBot](a: RateNet l P i k)
  (u:Bought l P c s i k y f g)(v: Bought l P c s i k y' f' g')
  {r:ℕ} (q:drydock R✽ r) (b:10*r≤W)
  (m: AmberMood P c s) (t:ε'≤1)
  (cost:1≤d.M)
  (Z:P.Register)
  {j:Axis}(h:P.Spectrum0 j):

  ‖P.singleState j s h ((aureole H timeAxis (-(r:ℤ)) g)*g')‖ ≤Real.exp (bauble P s d.v):=by
 let e:=u.tagged.revolve timeAxis (-(r:ℤ))
 let T:=e.product v.tagged

 have r₀:Rendered l P s i k w✤ p₀ (company z) (bauble P s d.v):=
    ⟨crowning P c s,
      by
       unfold crowning
       exact one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _)),
      Eventually.of_forall fun x=>descending (z x) cost (m.fund.trans t)⟩

 have r₁:∀ᶠ x in l, Profiled j w✤ p₀ (sill r)
    ((company z) x) (reflMark timeAxis (-(r:ℤ)) (y x)*y' x):=by
    have t:∀ᶠ x in l,4*r<(tunnel P s i x).val:=
     a.both (((Papal.count_grows P.run s).eventually_gt_atTop (4*r)).mono fun i d=> Eventually.of_forall fun _=>d)
    filter_upwards [u.mounts,v.mounts,t] with x ⟨A,w,y,e⟩ ⟨B,w',y',e'⟩ d

    rw [←e,←e']
    exact backstage _ (z x) w w' y y' q b d

 exact festival Z a (fabulous a r₀)
    ((aureole H timeAxis (-(r:ℤ)) g)*g') T r₁ (inland _ q b) h

#print axioms controlled
#print axioms gilded
#print axioms accessible
