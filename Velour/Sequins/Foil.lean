import Velour.Sequins.Shell
import SU5SatinFixedProbesAndBareFlavorNovember6
import Velour.Wadding.Violet
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe

open YM.Velour

variable {H:Hilbert}{j:Axis}(S:OS.Semigroup H j)


local notation "ℒ"=> Lead.Clan
local notation "δ"=> (fun z:ℂ=>(z.im/2).toNNReal)
local notation "U"=> S.unit.translation
/-- dressed pair analytic matrix. -/
def shebang(K L:ℒ→H)(z:ℂ): CrossRead:=
 matchRoles H (fun a=> S.E (δ z) (K a)) (fun b=>U (z.re • basis j) (S.E (δ z) (L b)))

abbrev scint(M:CrossRead):ℂ:=M.det * ∏ i:ℒ,M i i
lemma scint_ne(M:CrossRead): scint M≠0 ↔ ReadsSix M:=by
 rw [scint, mul_ne_zero_iff, Finset.prod_ne_zero_iff]; simp [ReadsSix]
variable (K L:ℒ→H)
lemma shebang_cont: Continuous (scint ∘shebang S K L):=by
 have c(i j':ℒ): Continuous (fun z:ℂ=> shebang S K L z i j'):=by
   have y: Continuous δ:=by fun_prop
   refine Continuous.inner ((S.continuousE _).comp y) (?_:Continuous (fun z:ℂ=> U (z.re • basis j) (S.E (δ z) (L j'))))
   exact S.cont_edge _ _ (S.cont_cross _ _ ((S.continuousE _).comp y)
      ((SEP j).continuous.comp (Complex.continuous_re.smul continuous_const))) (by fun_prop)
 have d: Continuous (shebang S K L):= continuous_pi (fun i=>continuous_pi (fun j=> c i j))
 exact d.matrix_det.mul (continuous_finsetProd _ fun i _=> c i i)

lemma shebang_analytic : AnalyticOnNhd ℂ (scint ∘shebang S K L) {z:ℂ|0<z.im}:=by
 let f(y:H)(t:ℝ):=S.E t.toNNReal y
 have p(y:H):Positive S (f y):=by

    intro a b h t
    have r:b.toNNReal=(b-a).toNNReal+a.toNNReal:=by
       rw [←Real.toNNReal_add (sub_nonneg.mpr t) h.le,sub_add_cancel]
    unfold f; rw [r,S.time]; rfl
 intro z hz
 let M:=shebang S K L
 have a(i k:ℒ): AnalyticAt ℂ (fun q=>M q i k) z:=by
    have h:=shade_holo S _ _ (p (K i)) (p (L k)) 0 z hz
    unfold paintedFrom separationPrice at h; simp only [zero_add] at h; exact h
 change AnalyticAt ℂ (fun q=> (M q).det*∏ i:ℒ,M q i i) z
 refine AnalyticAt.mul ?_ (Finset.analyticAt_fun_prod _ (fun i _=>a i i))
 simp_rw [Matrix.det_apply']
 exact Finset.analyticAt_fun_sum _ fun i _=> analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun _ _=> a _ _))

lemma shebang_edge {r:ℝ}(p:0<r){z:ℂ}(q:0<z.im)
  (h:ReadsSix (shebang S K L z)):
  ∃ t:ℝ, |t| ≤ r ∧ ReadsSix (shebang S K L t):=by
 by_contra v
 have u(y:ℝ)(e: |y|≤r): (scint ∘ shebang S K L) y=0:=by
   by_contra l
   exact v ⟨y,e,(scint_ne _).mp l⟩
 exact (scint_ne _).mpr h (hem_identical (shebang_cont S K L).continuousOn (shebang_analytic S K L) p u z q)


/-- moving-center same slider. -/
abbrev velourSampleBead(a:Vantage)(i:ℕ):SampleDose:=slider a (chosen a i)

lemma bead_ahead(a:Vantage)(i:ℕ)(b:E4):
 sachet_LocalFieldBounds (velourSampleBead (a+foldSpace b) i) = ahead b (sachet_LocalFieldBounds (velourSampleBead a i)):=by
 let t:= foldSpace b
 have h(w:Vantage):chosen (a+t) i w=chosen a i (w-t):=by
   rw [ContDiffBump.apply,ContDiffBump.apply, sub_add_eq_sub_sub_swap]
   rfl
 have e:(∫ w:Vantage, chosen (a+t) i w)=∫w:Vantage,chosen a i w:=by
    simp_rw [h]
    exact integral_sub_right_eq_self _ t
 ext1 p
 rw [ahead_at]
 change Complex.ofReal ((chosen (a+t) i).normed _ (foldSpace p))= Complex.ofReal ((chosen a i).normed _ (foldSpace (p-b)))
 rw [ContDiffBump.normed_def,ContDiffBump.normed_def,e,h,map_sub]

lemma closes(a:Vantage)(b:ℕ→ Vantage)(p:Tendsto b atTop (𝓝 a))
    (L:Set Vantage)(u:L∈𝓝 a): ∀ᶠ i:ℕ in atTop,tsupport (velourSampleBead (b i) i).val ⊆ L:=by
 obtain ⟨ε,e,t⟩:=Metric.mem_nhds_iff.mp u
 filter_upwards [p.eventually (ball_mem_nhds _ (half_pos e)),
     (tendsto_pow_atTop_nhds_zero_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)).eventually (gt_mem_nhds (half_pos e))]
     with i h q 
 rw [velourSampleBead,DoseTravel.supported]

 refine subset_trans ?_ t
 intro y g
 have r: dist y (b i) < ε/2:=lt_of_le_of_lt (mem_closedBall.mp g) q
 exact mem_ball.mpr ((dist_triangle y (b i) a).trans_lt (by linarith only [mem_ball.mp h,r]))

lemma reap(a:Vantage)(b:ℕ→ Vantage)(p:Tendsto b atTop (𝓝 a))(y:Vantage→H)(g:Continuous y):
 Tendsto (fun i=> DoseTravel.beam H (velourSampleBead (b i) i) y) atTop (𝓝 (y a)):=by
 apply Metric.tendsto_nhds.mpr
 intro ε u
 let L:= y ⁻¹' ball (y a) (ε/2)
 filter_upwards [closes a b p L ((g.tendsto a).eventually (ball_mem_nhds _ (half_pos u)))] with i h
 rw [dist_eq_norm]
 exact lt_of_le_of_lt (tol a H y g (velourSampleBead (b i) i) (prescribed ..) (ε/2) (fun w f=>
   (dist_eq_norm (y w) (y a) ▸ (Metric.mem_ball.mp (h f))).le)) (half_lt_self u)



lemma shebang_real(t:ℝ): shebang S K L t = matchRoles H K (fun i=> U (t • basis j) (L i)):= by
 unfold shebang
 simp [S.eZero]
lemma reap_collect(a:Vantage)(y:H):
 Tendsto (fun i=> collect S (sachet_LocalFieldBounds (velourSampleBead a i)) y) atTop (𝓝 (U (foldSpace.symm a) y)):=by
 simp_rw [collect_eq, integral_sachet]
 exact sprinkle a H (fun w=> U (foldSpace.symm w) y) ((S.unit.moves y).comp foldSpace.symm.continuous)

lemma skew_axis (w:Vantage): foldSpace.symm w - (w 3) • basis 3 = polarBase w:=by
 ext i; unfold polarBase
 fin_cases i <;> simp [foldSpace,spacePart,spatial,Cheer.shore,position,basis] <;> rfl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
