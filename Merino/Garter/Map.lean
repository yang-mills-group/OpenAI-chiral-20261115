import Merino.Garter.Wiggle
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}

abbrev Tint:=Bool × Bool
open scoped BigOperators 
def dart(b:Bool)(x:ℂ):= if b then star x else x

lemma dart_n(b:Bool)(x:ℂ):‖dart b x‖=‖x‖:=by unfold dart; split <;> simp
lemma dart_bit(b:Bool)(x:ℂ)(y:ℝ):‖dart b x-y‖=‖x-y‖:=by 
 unfold dart; split
 · have := norm_star (x-(y:ℂ)); simpa using this
 rfl
variable (β z:ℝ)
variable (g:Duo n)(c0:Tint)
abbrev polka (f:Config G n→ℂ)(U:Config G n):=
 dart c0.1 ((β:ℂ)*f (g.1.cabin U))*dart c0.2 ((β:ℂ)*f (g.2.cabin U))
abbrev flipper (f:Config G n→ℂ)(U:Config G n):=
  1+(z:ℂ)*polka β g c0 f U
lemma polka_turn (a:StepIn n)(f:Config G n→ℂ)(U:Config G n):
 polka β g c0 f (a.cabin U)=polka β (a.rotate g) c0 f U:=by
    simp [polka,cabin_mul]

/-- A capped real log majorant of |1+x| with no log integrability issue. -/
def logₛ (t:ℝ)(x:ℂ):ℝ:= min (x.re+‖x‖^2/2) t


lemma loggable {x:ℂ}{t:ℝ}(h:‖1+x‖≤Real.exp t):
  ‖1+x‖≤Real.exp (logₛ t x):=by
  unfold logₛ; rcases min_choice (x.re+‖x‖^2/2) t with e|e
  swap; · rwa [e]
  rw [e]
  have a:=Real.add_one_le_exp (2*(x.re+‖x‖^2/2))
  rw [two_mul,Real.exp_add,←pow_two] at a
  have b:‖1+x‖^2=1+2*x.re+‖x‖^2:= by
    simp only [Complex.sq_norm,Complex.normSq_add]; simp; ring
  exact le_of_sq_le_sq (b.trans_le (by linarith only [a])) (Real.exp_pos _).le

lemma logₛ_cash {t:ℝ}(h:0≤t)(x):|logₛ t x|≤1+t:=by
   refine abs_le.mpr ⟨le_min ?_ (by linarith),min_le_of_right_le (by linarith)⟩
   have :=neg_le_of_abs_le (Complex.abs_re_le_norm x)
   nlinarith [sq_nonneg (‖x‖-1)]

variable [Fintype I]
def lorg (m:ℕ)(f:Config G n→ℂ) (j:I→StepIn n)(b:I→Tint)(U:Config G n):=
 ∑ i,logₛ (wiggle m) ((z:ℂ)*polka β ((j i).rotate g) (b i) f U)

lemma lorg_turn (a:StepIn n)(f:Config G n→ℂ) (j:I→StepIn n)(b:I→Tint)(U:Config G n):
 lorg β z g m f j b (a.cabin U)=lorg β z g m f (fun i=>a*j i) b U:=by
 simp [lorg, polka_turn, mul_rotate]


lemma lorg_inv {f:Config G n→ℂ} (j:I→StepIn n)(b:I→Tint)(h:GaugeInvariant f): 
 GaugeInvariant (lorg β z g m f j b):=by
  unfold GaugeInvariant at h; intro x y; simp [lorg,polka,cabin,Push.Local.pull_gauge,h]

lemma dartₘ (b:Bool):Continuous (dart b):=by
  unfold dart; by_cases h:b <;> simp [h] <;> fun_prop
lemma lorg_bill {f:Config G n→ℂ} (j:I→StepIn n)(b:I→Tint)(h:Measurable f):
 Envelope (lorg β z g m f j b):=by
  have t(a:StepIn n): Measurable (a.cabin (G:=G)):= (continuous_pull ..).measurable
  have u(d): Continuous (logₛ d):=by unfold logₛ; fun_prop
  exact Envelope.sum univ _ (fun i=> ⟨
   (u _).measurable.comp (measurable_const.mul <|
     ((dartₘ _).measurable.comp (measurable_const.mul (h.comp (t _)))).mul
       ((dartₘ _).measurable.comp (measurable_const.mul (h.comp (t _))))),
    1+(wiggle m:ℝ),fun x=>by rw [Real.norm_eq_abs]; exact logₛ_cash (Nat.cast_nonneg _) _⟩)

variable {f:Config G n→ℂ} {L:ℝ}


lemma lorg_le {s:ℝ}
   (t:0≤β)(cL:∀x,‖f x‖≤L)
   (r:1+s*(β*L)^2≤Real.exp (wiggle m))(p:|z|≤ s)
   (j:I→StepIn n)(b:I→Tint)(x:Config G n):
   ‖∏ i, flipper β z ((j i).rotate g) (b i) f x‖ ≤ 
     Real.exp (lorg β z g m f j b x):=by
 have w:0≤L:=(norm_nonneg _).trans (cL x)
 have v:0≤ s:=(abs_nonneg _).trans p
 rw [lorg, Real.exp_sum, norm_prod]
 refine prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>loggable ?_)
 apply (norm_add_le ..).trans; apply le_trans _ r
 rw [norm_one]
 unfold polka
 rw [norm_mul, norm_mul, dart_n,dart_n, pow_two (β*L), Complex.norm_real,Real.norm_eq_abs]
 simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg t]
 gcongr <;> apply cL

end YM.CF.Merino.Garter
