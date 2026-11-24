import ExactRunning.Step.Progress

/-!
# Thermal finite bound via actual Test

`hiLaw`, `zLaw` are high and joint determinant costs along `lead`
(diagonal: same probe for both backgrounds), with arbitrary coarse
cut radius. **Uncut** (`r := -1`), high is the base's K=1 determinant
formula (`bounty`). The base Haar-chart law (`tribute`) plus gauge and
tangency give the thermal Hessian decomposition (`thermalDecomp`).
`Test.echo_price` instantiates `wave_price`. No new α proposed.
-/


set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree


lemma Latitude.uncut {D : Latitude} (α : Type) [DecidableEq α] [Fintype α]
    (m : Side) (h : D.radius < 0) : D.cut m α = ModeCut.total :=
   ModeCut.ext (approached_inj <| jaunt_eq (D.cut_jaunt m α) (by
      rw [show D.maskM α = fun _ => 1 from funext fun _ => if_pos (lt_of_lt_of_le h (D.mark_nonneg _)),
         ModeCut.total_e, approach_one]
      exact Jaunt.noop))

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} (X : BlockTie E I)

lemma h_uncut : X.bCut (-1) m = ModeCut.total := by
  ext1
  rw [bCut,ModeCut.direct_e, Latitude.uncut _ _ (show (X.back _).radius<0 from neg_one_lt_zero),
    Latitude.uncut _ _ (show (ridge _).radius<0 from neg_one_lt_zero)]
  simp [fromBlocks_one]

lemma h_bounty (b : Joint G m (X.up m)) (v : Config G m) :
    X.hCost (-1) b v =
      bounty (X.S m) E.p E.r X.μ (X.choice m) 1 v b := by
  rw [hCost, X.h_uncut, high_eq, Latitude.uncut _ _ (show (X.back _).radius<0 from neg_one_lt_zero)]
  simp [ModeCut.cutlog,bounty]

def hiLaw (m : Side) (r : ℝ) := fun y => X.hCost r (X.lead m y) (input G m y)
def zLaw (m : Side) (r : ℝ) := fun y => X.zCost r (X.lead m y) (input G m y)
def inLaw (m : Side) := (turnSeries E.r.loop) ∘ uniformM (G:=G) (X.W m)
def billLaw (m : Side) := draft X.q I.r I.p ∘ arm G m 1

variable {X}

namespace Test
variable (T : X.Test m)
def thermalLaw := thermal T.tree (X.choice m) E.p E.r T.shellChart X.form ∘ arm G m 1
include T
lemma uncut : X.HSafe m (-1) := by
  unfold HSafe
  rw [X.h_uncut, Latitude.uncut _ _ (show (X.back _).radius<0 from neg_one_lt_zero),
   ModeCut.total_det,ModeCut.total_det]
  exact ⟨T.high_unit, fund_det (grenade_safe _ X.hμ)⟩
lemma tandem_high :
    Tandem 2 (X.hiLaw m (-1))
      (honorarium T.tree (X.choice m) X.μ E.p E.r T.shellChart) := by
  refine (T.travel (C:=X.hCost (-1)) (X.h_flat T.uncut)).congr .rfl ?_
  filter_upwards [T.stable, X.movers T.thaw T.b01,
    X.movers (camp_thaw T.critical) (by rw [encamp_zero T.critical]; rfl)]
    with z hz hb hv
  let k := salute T.tree (X.W m) z
  rw [X.h_bounty]
  have hx := bounty_carry X.branches (X.choice m) k 1 _ (input G m z) E.paths hv hb X.hμ (by rw [gauge_one]; exact hz.1)
  rw [gauge_one] at hx; exact hx

lemma thermal_smooth : ContDiffAt ℝ ω T.thermalLaw 0 :=
  ContDiffAt.comp _ (by rw [map_zero]; exact T.finite.born _) ((arm G m 1).contDiff.contDiffAt)
lemma bill_smooth : ContDiffAt ℝ ω (X.billLaw m) 0 :=
  ContDiffAt.comp _ (by rw [map_zero]; exact T.finite.classicalResult) ((arm G m 1).contDiff.contDiffAt)

lemma thermalDecomp :
    iteratedFDeriv ℝ 2 T.thermalLaw 0 =
    iteratedFDeriv ℝ 2 (X.inLaw m) 0 + iteratedFDeriv ℝ 2 (X.hiLaw m (-1)) 0 := by
  rw [show iteratedFDeriv ℝ 2 (X.inLaw m) 0 = _
       from (inherited_le T.critical X.branches E.paths (t:=X.choice m) (X.W m) T.guess).symm,
      T.tandem_high.same _ le_rfl, ← iteratedFDeriv_add_apply]
  · exact EventuallyEq.iteratedFDeriv ℝ 
       ((tribute T.critical X.branches E.paths T.gap X.hg X.hμ (X.choice m) X.actual).mono
           fun _ h => h.2)
       2 |>.eq_of_nhds
  · exact (campaign T.critical X.branches E.paths (X.choice m) T.gap X.hg X.hμ X.actual).2.2.analytic.contDiffAt
  exact T.tandem_high.hg.of_le le_top

end Test
end BlockTie

lemma beat_re {ι : Type} [Fintype ι] [DecidableEq ι] (F : Corn ι → ℝ) (u v : Phase ι) :
    (beat F 0 2 ![u,v]).re =
      iteratedFDeriv ℝ 2 F 0 ![realPart u,realPart v] - iteratedFDeriv ℝ 2 F 0 ![imagPart u,imagPart v] := by
  conv_lhs => rw [← parts u, ← parts v]
  have h := left_beat F (realPart u) (imagPart u) (p:=axes (realPart v) + Complex.I • axes (imagPart v))
  have i (x) := right_beat F (axes x) (realPart v) (imagPart v)
  dsimp only at h i
  rw [h,i,i,beat_axes,beat_axes,beat_axes,beat_axes]
  simp [Complex.mul_re,sub_eq_add_neg]

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} (X : BlockTie E I)
def budget (m : Side) := X.toll * Real.exp (-X.rate * m.val)
namespace Test
variable {X} (T : X.Test m)
lemma real_price (a b : Site m) (v w : Phase (Entry G))
    (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1) :
    let u := ![realPart (tune a v),realPart (tune b w)]
    |iteratedFDeriv ℝ 2 T.thermalLaw 0 u - iteratedFDeriv ℝ 2 (X.billLaw m) 0 u| ≤
       cents m * X.budget m := by
  dsimp only
  have he := T.finite.wave_price (X.choice m) a b (Function.curry v) (Function.curry w)
     (fun x y=>hv (x,y)) (fun x y => hw (x,y))
  dsimp only at he
  let L := (arm G m 1).toContinuousLinearMap
  erw [thermalLaw,billLaw,wired L,wired L,map_zero]
  · rw [show (L ∘ ![realPart (tune a v),realPart (tune b w)]) =
        ![wave (G:=G) a (Function.curry v), wave b (Function.curry w)] by funext i; fin_cases i <;> rfl]
    unfold budget
    simpa [cents,mul_assoc] using he
  · rw [map_zero];exact T.finite.classicalResult.analyticAt
  rw [map_zero];exact (T.finite.born _).analyticAt

lemma re_price (a b : Site m) (v w : Phase (Entry G))
    (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1) :
    let u := ![tune a v,tune b w]
    |(beat T.thermalLaw 0 2 u).re - (beat (X.billLaw m) 0 2 u).re| ≤
       cents m * X.budget m * 2 := by
  dsimp only; rw [beat_re,beat_re]
  have hi (a : Site m) (v : Phase (Entry G)) :
       realPart (tune a ((-Complex.I) • v)) = imagPart (tune a v) := by
    rw [tune_smul]; funext; simp [realPart,imagPart]
  have hm : ∀ (x : Phase (Entry G)) i, ‖((-Complex.I) • x) i‖ = ‖x i‖ :=
    by intros; simp
  have hr := T.real_price a b v w hv hw
  have hs := T.real_price a b ((-Complex.I) • v) ((-Complex.I) • w)
    (fun i => by rw [hm]; exact hv _) (fun i => by rw [hm];exact hw _)
  dsimp only at hs hr
  rw [hi,hi] at hs
  rw [abs_le] at hs hr ⊢
  constructor <;> linarith only [hr.1,hr.2,hs.1,hs.2]

end Test
end BlockTie

/-- Intensive Hessian entry. -/
def echo {α : Type} [Fintype α] [DecidableEq α] {m : Side} (f : Corn (Co m α) → ℝ)
    (b : Site m) (i j : α) :=
  ((cents m : ℂ))⁻¹ * beat f 0 2 ![relay (-b) i,relay b j]

lemma Resonance.echo {ι : Type} [Fintype ι] [DecidableEq ι] {m : Side} {D : Latitude}
    {F : Kin ι} {f : Corn (Co m ι) → ℝ} (h : Resonance D F f)
    {b : Site m} {p : Momentum} (hp : rolls (mon b) p) (q : D.quiet p)
    (i j : ι) : echo f b i j = F p i j := by
  unfold ExactRunning.echo
  rw [h.on_relays i j (q.neg.rolls hp.flip_sign.symm) (q.rolls hp.symm) hp,if_pos (neg_add_cancel _),
      inv_mul_cancel_left₀ (by exact_mod_cast cents_pos.ne')]

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}
theorem Test.echo_price (T : X.Test m) (b : Site m) (i j : Entry G) :
    |(echo (X.inLaw m + X.hiLaw m (-1)) b i j).re - (echo (X.billLaw m) b i j).re| ≤ X.budget m * 2 := by
  have hi : ContDiffAt ℝ ω (X.inLaw m) 0 :=
    ContDiffAt.comp _ (f:=uniformM (X.W m))
      (by rw [map_zero]; exact (turns_analytic _ E.paths.width E.paths.two).contDiffAt) (uniformM _).contDiff.contDiffAt
  have he : echo (X.inLaw m + X.hiLaw m (-1)) b i j = echo T.thermalLaw b i j := by
    unfold echo beat
    rw [iteratedFDeriv_add_apply (i:=2) (hi.of_le le_top)
      (T.tandem_high.hf.of_le le_top), T.thermalDecomp]
  rw [he,echo,echo,← Complex.ofReal_inv,Complex.re_ofReal_mul,Complex.re_ofReal_mul,← mul_sub,abs_mul,
     abs_of_pos (inv_pos.mpr cents_pos)]
  have h := T.re_price (-b) b (Pi.single i 1) (Pi.single j 1)
     (fun _ => by simp only [Pi.single_apply]; split <;> simp)
     (fun _ => by simp only [Pi.single_apply]; split <;> simp)
  refine (mul_le_mul_of_nonneg_left h (inv_pos.mpr cents_pos).le).trans_eq ?_
  rw [mul_assoc (cents m),inv_mul_cancel_left₀ cents_pos.ne']
end BlockTie
end ExactRunning
