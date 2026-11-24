import YM.SU5.FiniteGaugeData.Tower.Bond
import YM.SU5.FiniteGaugeData.Tower.Baggage
import Merino.Plume.Shell
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Tiara
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Afterglow Tower Lifted Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Journey Satin Sound

abbrev Tassels(S:Finset Cover):=Evens S→LinksC→ℂ
variable {S:Finset Cover}(K:Calibration)
def braid (f:Tassels S):Buffered.Family K:=
    ∑ i:Evens S, Sound.note K (f i ∘ Prod.fst) (tagWord S i.val)
def sheenCost(S:Finset Cover)(M:ℝ):= (Fintype.card (Evens S):ℝ)*M+1
lemma sheen_pos {M:ℝ} (h:0≤ M):0<sheenCost S M:=by unfold sheenCost;positivity

structure Willow (C:ℝ)(f:Tassels S):Prop where
 reads (i:Evens S): Measurable (f i)
 region (i):LocalOn S (f i)
 bound (i x):‖f i x‖≤C
 sang:CovCover K (braid K f)

variable {C:ℝ}{f:Tassels S}
lemma threshold (h: Willow K C f):InTest K true S false (braid K f):=by
 refine .sum _ _ fun i _=>?_
 have j:Coeff true S (f i ∘ Prod.fst):=
    ⟨fun _=>by contradiction,⟨(h.reads i).comp measurable_fst, C, fun x=> h.bound i x.1⟩,
      fun _ _ a _=>h.region i _ _ a⟩
 have g:=Sound.note_t K _ j (Satin.brand S i.val)
 rw [i.property] at g
 exact g

private lemma wage (M:ℝ)(h:∀i x,‖f i x‖ ≤ M): pay (braid K f) (Fintype.card (Evens S)*M):=by
 intro n x
 unfold braid
 rw [Finset.sum_apply,Finset.sum_apply,←nsmul_eq_mul,←card_univ,←sum_const]
 refine (norm_sum_le ..).trans (sum_le_sum ?_)
 intro i _
 rw [note_v,norm_smul]
 exact (mul_le_of_le_one_right (norm_nonneg _) (chorus_size ..)).trans (h ..)

lemma garnet(h: Willow K C f):pay (braid K f) (sheenCost S C):=
 fun i x=> (wage K C h.bound i x).trans (le_add_of_nonneg_right zero_le_one)

variable {F:ℕ→Tassels S}(t:∀i:Evens S,Plume.spray (fun n=>F n i) (f i))
include t
lemma accruing (ε:ℝ)(h:0<ε):
    ∀ᶠ j in atTop,pay ((braid K (F j))-braid K f) ε:=by
 let M:ℝ:=(Fintype.card (Evens S):ℝ)+1
 have g:0<M:=add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
 filter_upwards [eventually_all.mpr (fun i=> t i _ (div_pos h g))] with n e
 rw [show braid K (F n) - braid K f = braid K (F n - f) from ?_]
 · refine fun m x=>(wage K (f:= F n-f) (ε/M) (fun i y=> (dist_eq_norm (F n i y) (f i y)) ▸ e i y) m x).trans ?_
   have r:ε/M*M=ε:=div_mul_cancel₀ _ g.ne'
   unfold M at *
   linarith [div_pos h g]
 funext m x
 unfold braid
 simp only [Finset.sum_apply,Pi.sub_apply,note_v,comp_apply,sub_smul]
 rw [sum_sub_distrib]

lemma varnish (u:∀n,Willow K C (F n)):Willow K C f:=by
 have g(m x):Tendsto (fun n=> braid K (F n) m x) atTop (𝓝 (braid K f m x)):= by
    refine Metric.tendsto_nhds.mpr fun ε h =>
      (accruing K t _ (half_pos h)).mono fun n e=>?_
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (e m x) (half_lt_self h)

 refine ⟨fun i=> measurable_of_tendsto_metrizable (f:=fun n=>F n i) (fun n=>(u n).reads i)
    (tendsto_pi_nhds.mpr (t i).rise),fun i x y h=>?_,fun i x=>le_of_tendsto' ((t i).rise x).norm
      (fun n=>(u n).bound _ _),?_⟩
 · exact tendsto_nhds_unique ((t i).rise x) (((t i).rise y).congr fun n=> ((u n).region i _ _ h).symm)
 intro m z r
 refine tendsto_nhds_unique (g m (simultaneous z r)) (((Fock.breeze _).continuousAt.tendsto.comp (g m r)).congr ?_)
 exact fun n=> ((u n).sang m z r).symm

lemma ivy(hC:0≤C)(u:∀n,Willow K C (F n)):
    SlabMark.BQueue S (fun n=>braid K (F n)) (braid K f):=by
 have w:= varnish K t u
 exact ⟨fun n=>threshold K (u _),threshold K w,⟨_,sheen_pos hC,garnet K w,
   Eventually.of_forall fun n=>garnet K (u _)⟩,accruing K t⟩
end YM.CF.Merino.Tiara
