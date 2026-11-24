import YM.SU5.Same.PhasePrice
/-!
# All spectral two-point consultations (for the produced positive-side field)
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinEdge.RealSheet
open Function Set Filter Metric Finset MeasureTheory Measure Spectral Analysis Boundary Probe Complex
open OS Semigroup
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators Classical ComplexConjugate
open Multiplier Roy SatinJets
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(X Y:ℝ→ H)

abbrev chords (c:ℂ) : ℝ→ H:=fun t=>X t+c • Y t
local notation "ℒ" => chords X Y
local notation "hν" t => homeMeasure S (chords X Y t)

-- polarization convention. For all phases above the complex axis or paying at the real zero-offset Test4.
private def plait {E:Type*}[AddCommGroup E][Module ℂ E](w:ℂ→ E):E:=
  (1/4:ℂ) • (w 1-w (-1)-Complex.I • (w Complex.I - w (-Complex.I)))
private lemma strands {E E':Type*}[AddCommGroup E] [Module ℂ E] [AddCommGroup E'][Module ℂ E'](w:ℂ→E)(A:E→ₗ[ℂ] E') : A (plait w) = plait (fun i=> A (w i)):=by
 unfold plait; rw [map_smul,map_sub,map_sub,map_smul,map_sub]
lemma separate_twine (b:E4)(t:ℝ): separationPrice S X Y b t= plait (fun w=> separationPrice S (ℒ w) (ℒ w) b t):=by
 unfold separationPrice plait; dsimp only [chords]; let c:=planks S b; simp only [map_add,map_smul, inner_add_left,inner_add_right,inner_smul_left,inner_smul_right, map_one,map_neg, Complex.conj_I, smul_eq_mul]; ring_nf; simp [Complex.I_sq]; ring

def allMoments (b:E4)(t:ℝ):ℂ:= plait fun c=> momentPrice (a:=a) (homeMeasure S (chords X Y c)) b t
lemma boundary_chords(c:ℂ)(vx:TemperedAtEdge H X)(vy:TemperedAtEdge H Y):TemperedAtEdge H (chords X Y c):= vx.addEdge (vy.scaleEdge c) -- fix typ

variable (hX:Positive S X) (hY:Positive S Y)
include hX hY
lemma market_chords(c:ℂ): Positive S (ℒ c):=by
 intro s t p q; unfold chords; rw [hX _ _ p q, hY _ _ p q, map_add,map_smul]
lemma of_all_prices (b:E4)(t:ℝ)(p:0<t): separationPrice S X Y b t=allMoments S X Y b t:=by
 unfold allMoments; rw [separate_twine S X Y]; exact congrArg plait (funext fun c=>separation_price S _ (market_chords S X Y hX hY c) b t p)

variable (vx:TemperedAtEdge H X)(vy:TemperedAtEdge H Y)
def feelCross: Test4→L[ℂ] ℂ:= plait fun c=> feelDiag S (ℒ c) (boundary_chords X Y c vx vy)
omit hX hY in
lemma feelCross_plait (f:Test4): feelCross S X Y vx vy f= plait (fun c=> feelDiag S (ℒ c) (boundary_chords X Y c vx vy) f):= rfl
omit hX hY in
lemma feelCross_eq (f:Test4): feelCross S X Y vx vy f=
    (1/4:ℂ) * ((∫ p,onward f p∂(homeMeasure S (chords X Y 1))) -(∫ p,onward f p∂(homeMeasure S (chords X Y (-1)))) - Complex.I*((∫ p,onward f p∂(homeMeasure S (chords X Y Complex.I)))-(∫ p,onward f p∂(homeMeasure S (chords X Y (-Complex.I)))))):=by rw [feelCross_plait]; rfl
private def look (A B:ℝ→ H)(t:ℝ)(f:Test4)(b:E4):= f b * separationPrice S A B b t
omit hX hY in
lemma feelUnder (t:ℝ)(f:Test4):
    (∫ b, f b * separationPrice S X Y b t) = plait (fun c=>∫ b, f b * separationPrice S (ℒ c) (ℒ c) b t):=by
 let Q(c:ℂ):= look S (ℒ c) (ℒ c) t f
 have h(u:ℂ) : Integrable (Q u):= test_budget S (ℒ u) (ℒ u) t f
 have he(x:E4): (f x * separationPrice S X Y x t)= (1/4:ℂ) * (Q 1 x-Q (-1) x-Complex.I*(Q Complex.I x-Q (-Complex.I) x)):=by
    rw [separate_twine S X Y, plait]; unfold Q look; simp only [smul_eq_mul]; ring
 simp_rw [he]; rw [integral_const_mul, integral_sub (f:=fun x:E4=> Q 1 x-Q (-1) x) (g:=fun x:E4=> Complex.I*(Q Complex.I x - Q (-Complex.I) x)) ((h 1).sub (h (-1))) (((h Complex.I).sub (h (-Complex.I))).const_mul _), integral_const_mul, integral_sub (h 1) (h (-1)), integral_sub (h Complex.I) (h (-Complex.I))]; rfl
-- all 36 and future tolls. relative-time unshifted distribution from both.
lemma feeling (f:Test4):
    Tendsto (fun t:ℝ=>∫ b, f b * separationPrice S X Y b t) (𝓝[>] 0) (𝓝 (feelCross S X Y vx vy f)):=by
 simp_rw [feelUnder S X Y, feelCross_plait]
 have he(c:ℂ):= (progress S (ℒ c) (market_chords S X Y hX hY c) (boundary_chords X Y c vx vy) f)
 unfold plait; exact ((((he 1).sub (he (-1))).sub (((he Complex.I).sub (he (-Complex.I))).const_smul Complex.I)).const_smul (1/4:ℂ)) -- parentheses!

lemma chord_earning (c:ℂ)(f:Test4): awake S (ℒ c) (boundary_chords X Y c vx vy) f= awake S X vx f + c • awake S Y vy f:=by
 refine tendsto_nhds_unique (rise_heat S (ℒ c) (boundary_chords X Y c vx vy) (market_chords S X Y hX hY c) f) (?_); unfold chords; simp_rw [map_add,map_smul]; exact (rise_heat S X vx hX f).add ((rise_heat S Y vy hY f).const_smul c)

omit hX hY
-- Here W^+ as relative-variable distribution really represents the vacuum product *on the real-time test functions*. No assumption about field − orders.
def togetherT(f g:Test4):Test4:=SchwartzMap.smulLeftCLM ℂ (bar (onward f): E4→ℂ) (onward g)
lemma togetherT_at (f g:Test4)(b:E4): togetherT f g b= star (onward f b) * onward g b:=by
 change SchwartzMap.smulLeftCLM ℂ (bar (onward f):E4→ℂ) _ _=_; rw [SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.hasTemperateGrowth _), Probe.bar_at]; rfl
-- convolution convention with rev operator exactly. independent Schwartz guarantees.
def tieAt(f g:Test4):Test4:= SNAG.cut (togetherT f g)
lemma tieAt_on (f g:Test4): onward (tieAt f g)= togetherT f g:= onward_cut _
lemma tieAt_day (f g:Test4)(b:E4):
    tieAt f g b= ∫ z:E4, star (f z)* g (b+z):=by
 let κ := onward f; let V:= onward g
 have he:∀ z:E4, togetherT f g z= bar κ z * V z:=togetherT_at f g
 unfold tieAt; rw [← SNAG.rolled (bar κ) V _ he, ← integral_neg_eq_self (fun z:E4=> star (f z)*g (b+z)) volume]; refine integral_congr_ae (ae_of_all _ fun z=> ?_); unfold V κ; dsimp only; rw [SNAG.reversals,cut_onward,cut_onward,sub_eq_add_neg]
-- integrable in that convention.
lemma tieAt_integrable(f g:Test4)(b:E4): Integrable (fun z:E4=> star (f z)* g (b+z)):= by
 let C:=SchwartzMap.seminorm ℝ 0 0 g; refine (SchwartzMap.integrable f (μ:=volume)|>.norm.mul_const C).mono' (((Probe.bar f).continuous.mul (g.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable (μ:=volume)) (ae_of_all _ (fun p=>?_)); rw [norm_mul,norm_star]; exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ g (b+p)) (norm_nonneg _)
lemma diag_tie(f g:Test4):
    feelDiag S X vx (tieAt f g)= inner ℂ (awake S X vx f) (awake S X vx g):=by
 rw [feelDiag_eq, expense_inner, tieAt_on]; simp_rw [togetherT_at]
include hX hY
lemma tie_prices (f g:Test4):
    feelCross S X Y vx vy (tieAt f g)= inner ℂ (awake S X vx f) (awake S Y vy g):=by
 rw [feelCross_plait]; simp_rw [diag_tie, chord_earning S X Y hX hY vx vy]; unfold plait; simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,map_one,map_neg, Complex.conj_I, smul_eq_mul]; ring_nf; simp [Complex.I_sq]; ring
end YM.SatinEdge.RealSheet
open YM.SatinEdge.RealSheet
#print axioms feeling
#print axioms tie_prices
#print axioms of_all_prices
