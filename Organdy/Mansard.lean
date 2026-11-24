import Organdy.Rabbet
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


open Push.Local Next.Rank.Spindle Next.SectorChange
open Scree
open scoped Classical
variable {c:Side}{r:Ratio c n}{L:Support c}
  {α b ζ e k β τ:ℝ}{m l:ℕ}
  {W:Config G n→ℂ}{A:Ink (Chip n)}
  {R: Rules G}
  {F X Y:Larva.Dir n}{U:Config G n}{o:Site n}

variable {x d u y :ℝ}
open Larva (Domaine)
variable {J:Type*}

open Tempest Worth BProof
open Worth.Pays
-- at stage x
abbrev flagon (a x:ℝ) := coin x 0 a 0
abbrev stow (x:ℝ):= coin x (-2) 0 0
abbrev screend:=flagon 2
abbrev rail:=flagon 3
abbrev skim:=flagon (-1800)
abbrev clipper:=flagon 2000
abbrev knock:=flagon (-20000)
abbrev yieldt:=flagon (-21500)
abbrev insure:=flagon (-21100)
abbrev harbor (R:Rules G)(ζ b x:ℝ):=Wicket R ζ b (clipper x) x (stow x) (temp x) (ageC x) (screend x) (rail x) (skim x)
lemma priceTemp:Pays (-1/2) 1 0 temp:=Pays.fix (whole _ _ _) ((eventually_gt_atTop 0).mono fun _ h=>thresh_eq h)
lemma priceSqrt:Pays (1/2) 0 0 Real.sqrt:=by
 apply Pays.fix (whole _ _ _)
 filter_upwards [eventually_gt_atTop (0:ℝ)] with x h
 rw [Real.sqrt_eq_rpow]; nth_rw 2 [←coinY h]
 rw [coin_rpow];norm_num

private lemma dock_f(R:Rules G)(b:ℝ):
 ∀ᶠ x:ℝ in atTop,
 x*(stow x+b*temp x^2) ≤ rail x ∧
 Real.sqrt x*(temp x+faceCutError R (ageC x)) ≤ screend x∧
 x*(stow x+b*(2*ageC x)^3)+ b*((2*screend x)^4/clipper x) ≤ skim x:=by
 have y:=pot priceTemp 2
 have a:=times height (plus (merit (whole (-2) 0 0) (by norm_num [Earlier])) (Pays.scale b y))
 have c:=times priceSqrt (plus priceTemp
     (Pays.scale ((G).colorScale*16+R.C*4) (merit (pot (whole r_age 0 0) 2) (by norm_num [Earlier,r_age]))))
 have k:Pays 0 (-2000) 0 (fun x=>(clipper x)⁻¹):=by
    apply Pays.fix (whole 0 (-2000) 0)
    exact Filter.Eventually.of_forall fun i=> (by rw [clipper,flagon,coin_inv];norm_num)
 have v:=times height
     (plus (merit (whole (-2) 0 0) (by norm_num [Earlier,r_age]))
           (Pays.scale b (pot (Pays.scale 2 (whole r_age 0 0)) 3)))
 have g:=plus (merit v (by norm_num [Earlier,r_age]))
    (Pays.scale b (times (pot (Pays.scale 2 (whole 0 2 0)) 4) k))
 filter_upwards [
   leap (w:=0) (p:=3) (q:=0) a (by norm_num [Earlier]),
   leap (w:=0) (p:=2) (q:=0) c (by norm_num [Earlier]),
   leap (w:=0) (p:=-1800) (q:=0) g (by norm_num [Earlier])]
   with x i j h
 exact ⟨i,j,by rw [div_eq_mul_inv]; exact h⟩

lemma dock_v(R:Rules G)(b:ℝ)(p:0<ζ): ∀ᶠ x:ℝ in atTop,harbor R ζ b x:=by
 have a:=Pays.limit (whole r_age 0 0) (by norm_num [Earlier,r_age])
 filter_upwards [eventually_gt_atTop (0:ℝ), dock_f R b,
   a.eventually (gt_mem_nhds (half_pos p)),a.eventually (ge_mem_nhds R.radius)]
  with x h m c r
 change ageC x < ζ/2 at c
 exact ⟨coin_pos ..,h,coin_pos ..,by linarith only [c],r,m.1,(coin_pos ..).le,m.2.1,m.2.2⟩

lemma slant(q:Clip)(b:ℝ):∀ᶠ x:ℝ in atTop,∀t:ℝ,|t| ≤ knock x →
   |t| * ((rail x)^2+(b*clipper x)^2) ≤4*healthC x ∧
   |t| * (skim x*(2*rail x+skim x)) ≤ yieldt x ∧
   yieldt x + trend*(wager q b (clipper x))^2*t^2 ≤ insure x :=by
 let K:=whole 0 (-20000) 0
 have a:=times K (plus (merit (pot (whole 0 3 0) 2) (by norm_num [Earlier])) (pot (Pays.scale b (whole 0 2000 0)) 2))
 have g:=times K (times (whole 0 (-1800) 0)
   (plus (Pays.scale 2 (whole 0 3 0)) (merit (whole 0 (-1800) 0) (by norm_num [Earlier]))))
 have z:= times (Pays.scale (8*kilnBound q*b^2) (whole 0 2000 0))
    (plus (merit (constant 1) (by norm_num [Earlier])) (whole 0 2000 0))
 have f:=plus (whole 0 (-21500) 0) (merit (times (Pays.scale trend (pot z 2)) (pot K 2)) (by norm_num [Earlier]))
 filter_upwards [
   Pays.leap (w:=0) (p:=1) (q:=0) a (by norm_num [Earlier]),
   Pays.leap (w:=0) (p:=-21500) (q:=0) g (by norm_num [Earlier]),
   Pays.leap (w:=0) (p:=-21100) (q:=0) f (by norm_num [Earlier])]
   with x i j h t y
 have u:0<healthC x:=coin_pos ..

 have t0:0≤trend:=by unfold trend;positivity
 refine ⟨?_,?_,?_⟩
 · refine (mul_le_mul_of_nonneg_right y (by positivity)).trans (i.trans ?_)
   change healthC x≤_
   linarith only [u]
 · exact (mul_le_mul_of_nonneg_right y
     (by have :0≤rail x:=(coin_pos ..).le;have : 0 ≤ skim x:=(coin_pos ..).le;positivity)).trans j
 exact (add_le_add_right (mul_le_mul_of_nonneg_left
   ((sq_abs t).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) y 2))
      (mul_nonneg t0 (sq_nonneg _))) (yieldt x)).trans h
