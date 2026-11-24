import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open Py.Rate.Pitching.Focus (Morn)
variable (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(M:Morn P.par.K)(p:∀ s,F ≤ s → Accordance P M F s (C s) (D s))(T:RobeRoad P F C D x)
local notation "H"=>P.ColorHil 3 x
local notation "W"=>P.ManyF 3 x
local notation "U"=>P.cartage 3 x
local notation "B"=>P.wealth 3 x
local notation "S"=>P.physicalEnergy 3 x
noncomputable def atom (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(t:ℝ):P.ColorHil 3 x:= limUnder atTop (fun s=>outingP P F C D x t s s)
noncomputable def pointT(P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(q:Vantage):P.ManyF 3 x:=P.cartage 3 x (q-crest P F) (P.wealth 3 x (atom P F C D x (q 3)))
include p T
lemma hail {t:ℝ}(h:0<t): Tendsto (fun s=>outingP P F C D x t s s) atTop (𝓝 (atom P F C D x t)):= by obtain ⟨y,l⟩:= habit P F C D x M p T t h; unfold atom; rwa [l.limUnder_eq]
lemma hailE (j:ℕ)(q:F ≤j)(t:ℝ)(v:tidal P F j<t): Tendsto (fun s=> outingP P F C D x t s j) atTop (𝓝 (atom P F C D x t)):=by
 obtain ⟨y,h,he⟩:= runBorn P F C D x M p T q t v; unfold atom; rwa [he.limUnder_eq]
def hull (A:SampleDose):Prop:= ∃ t> (0:ℝ),∀q∈tsupport A.val,t < q 3
omit T p
private lemma ceiling {s j:ℕ}(A:SampleDose)(E':ℝ)(h:‖recoup P F C D x s j‖≤E')(q:Vantage): ‖plays P F C D x A s j q‖≤ |A.val q| *E':=by
 unfold plays outingP; rw [norm_smul, Complex.norm_real,Real.norm_eq_abs, P.cart_norm]; refine mul_le_mul_of_nonneg_left ((P.bank_cost ..).trans ?_) (abs_nonneg _)
 let t:=(q 3-tidal P F j).toNNReal; let r':= recoup P F C D x s j
 exact (( (S).E t).le_opNorm r').trans ((mul_le_of_le_one_left (norm_nonneg _) ((S).shrinks t)).trans h)
include T p
noncomputable def actualThinR (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(A:SampleDose):Vantage→P.ManyF 3 x:= fun q=>((A.val q:ℝ):ℂ) • pointT P F C D x q
lemma meteor (A:SampleDose)(a:hull A) : Tendsto (fun s:ℕ=> ∫ q:Vantage,plays P F C D x A s s q) atTop (𝓝 (∫ q:Vantage, actualThinR P F C D x A q)) ∧ Integrable (actualThinR P F C D x A):=by
 obtain ⟨d,t,u⟩:=a; obtain ⟨j,h,l⟩:= ((eventually_ge_atTop F).and ((recessVanish P F).eventually (gt_mem_nhds t))).exists
 obtain ⟨y,hz⟩:= cauchySeq_tendsto_of_complete (advances P F C D x M p T h)
 let E':= ‖y‖+1
 have hy: ∀ᶠ s:ℕ in atTop,‖recoup P F C D x s j‖≤ E':=hz.norm.eventually (ge_mem_nhds (lt_add_of_pos_right _ zero_lt_one))
 let f:= plays P F C D x A
 let k(q:Vantage):= |A.val q| *E'
 let L:= actualThinR P F C D x A
 have hg(s:ℕ):AEStronglyMeasurable (f s s):= (weighted A (s:=s)).aestronglyMeasurable -- add helper below. RHS.`
 have hk :Integrable k:= (((A.smooth.continuous).integrable_of_hasCompactSupport A.budget).abs).mul_const _ -- Abs helper
 have hr(q:Vantage):Tendsto (fun s=>f s s q) atTop (𝓝 (actualThinR P F C D x A q)):=by
    by_cases b:A.val q=0
    · simpa [f,L,actualThinR,plays,b] using (show Tendsto (fun _:ℕ=> (0:(P.ManyF 3 x).space)) atTop (𝓝 0) from tendsto_const_nhds)
    let g:=hail P F C D x M p T (t.trans (u q (subset_closure b)))
    have hw : Tendsto (fun s=>B (outingP P F C D x (q 3) s s)) atTop (𝓝 (B (atom P F C D x (q 3)))):= (B).continuous.continuousAt.tendsto.comp g
    let Vt:= U (q-crest P F)
    exact tendsto_const_nhds.smul (Vt.continuous.continuousAt.tendsto.comp hw)
 have H':∀ᶠ n in atTop,∀ q:Vantage,‖f n n q‖ ≤ k q:=by
    filter_upwards [hy,eventually_ge_atTop j,(recessVanish P F).eventually (ge_mem_nhds (tide_price P F j))] with n b e y' q
    by_cases y:A.val q=0; · unfold f k plays; rw [y,Complex.ofReal_zero,zero_smul,norm_zero,abs_zero,zero_mul]
    have hl:f n n q=f n j q:=by
       unfold f plays; rw [bless_r P F C D x h (h.trans e) e le_rfl y' (l.trans (u q (subset_closure y))).le]
    rw [hl]; exact ceiling P F C D x A E' b q
 refine ⟨tendsto_integral_filter_of_dominated_convergence k (Eventually.of_forall hg) (H'.mono (fun n e=> Eventually.of_forall e)) hk (Eventually.of_forall hr),?_⟩
 refine hk.mono' (aestronglyMeasurable_of_tendsto_ae _ hg (Eventually.of_forall hr)) (Eventually.of_forall (fun q=>le_of_tendsto (hr q).norm (H'.mono fun n h=> h q))) -- mono' actual k maybe expects ‖F‖≤k not ‖k‖. 
where weighted(A:SampleDose){s:ℕ}: Integrable (plays P F C D x A s s):= (end_cont P F C D x ..).integrable_of_hasCompactSupport (A.budget.mono (fun q h t=>h (by unfold plays; rw [show A.val q =0 from t,Complex.ofReal_zero,zero_smul])))
#check aestronglyMeasurable_of_tendsto_ae
#check Filter.limUnder
#print axioms meteor
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
