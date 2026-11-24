import YM.CF.Esti.Zen
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){A B:Stores S}{r v:ℕ}
open CF.Jet
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{G:Gauge}{n:ℕ}{K M C D:ℝ}{x:E}{U:E→ Config G f}
variable {a b h:ℝ}
def nearT (S:StepData c f)(i:Bond c):= Finset.univ.filter fun z:Cell f=> ¬Disjoint (beamV S i) (touched z)
lemma charged (U: Config G f)(i:Bond c):ResV S (a:=a) i U ↔∀ j∈nearT S i,toll U j≤a:=by
 constructor
 · intro h x hx; obtain ⟨l,r,t⟩:= Finset.not_disjoint_iff.mp (mem_filter.mp hx).2; by_contra! hp; exact disjoint_left.mp h r ((flags_spec ..).mpr ⟨x,t,hp⟩)
 intro u; apply Finset.disjoint_left.mpr; intro i v p; obtain ⟨k,l,p⟩:=(flags_spec ..).mp p; exact not_lt.mpr (u k (mem_filter.mpr ⟨mem_univ _,fun h=> Finset.disjoint_left.mp h v l⟩)) p
abbrev Dane (G:Gauge) (n:ℕ)(q:Chi)(u:ℝ):=∀ (D:Type)[NormedAddCommGroup D][NormedSpace ℝ D](v:D→ℝ)(x:D)(C:ℝ)(d:ℝ)(b:Bool), Allows n v x C→ Allows n (fun w=>testing q d (v w) b) x (Jet.composeCost n u ((2/d^2)*C)) ∧ Zed n (fun w=>testing q d (v w) b) x -- remove G
abbrev shutters(q:Chi)(d:ℝ)(S:Finset (Cell f))(U:Config G f):=∏ i∈S, q.innerShare d (toll U i)
abbrev dam(G:Gauge)(n:ℕ)(d u C:ℝ):=Jet.composeCost n u ((2/d^2)*Push.Uniform.priceCost G (Push.Uniform.travelCost G n 4 C))
lemma shutter_p(q:Chi)(d:ℝ)(S: Finset (Cell f))(h: Dane G n q M)(p:∀ i, grantB n (fun y=>U y i) x C): Allows n (shutters q d S ∘ U) x ((zest n * dam G n d M C)^S.card)∧Zed n (shutters q d S ∘ U) x:=by
 apply fuel; intro i hp
 let f(v):= G.mat (faceValue (U v) i); have ht: Allows n f x (Push.Uniform.travelCost G n 4 C):= trekP _ U p _ i.1 4 le_rfl
 have hh: Allows n (fun v=> G.price (faceValue (U v) i)) x (Push.Uniform.priceCost G (Push.Uniform.travelCost G n 4 C)):= (fare_a ht).germ (Eventually.of_forall fun i=>fare_h ..); have hy:= h _ _ _ _ d true hh
 unfold Pressure.toll; simp_rw [chooseF]; exact hy
variable (hS:S.patch.Branches S.kernel G)
variable {u s:ℝ}(q:Chi)(k:S.Choices)(j:Bond c)
def abortP (a:ℝ)(U:Config G f) : G.Mat:= (shutters q (a/2) (nearT S j) U) • G.mat (S.prediction U k j)
lemma abort_e (h:0<a)(V:Config G f)(p:ResV S (a:=a/2) j V): abortP S q k j a V=G.mat (S.prediction V k j):=by
 unfold abortP; rw [show shutters q _ _ _=1 from Finset.prod_eq_one fun i hp=> ?_,one_smul]; apply q.to_one; have hx:= Work.E01.base_touched i; have he:0<a/2:=half_pos h; have hp: 0 ≤ toll V i/(a/2):=div_nonneg (G.chord_nonneg _) he.le; exact pow_le_one₀ hp ((div_le_one he).mpr ((charged S V j).mp p i ‹_›))
def choke(G:Gauge)(n:ℕ)(a d s m b C:ℝ)(l:ℕ):ℝ:=zest n* purM G n* ((zest n*dam G n (a/2) m C)^l)*covetM G n C d b -- needs const bilinear scalar norm
private lemma wind_mono {d v:ℝ}{T:E→ℝ}{V:E→G.Mat}(p:Allows n T x d)(h:Allows n V x v):Allows n (fun i=> T i • V i) x (2^n*d*v):=by
 simpa only [mul_one, ContinuousLinearMap.lsmul_apply] using (p.bilinear _ h ContinuousLinearMap.opNorm_lsmul_le) -- tune lemma
abbrev Vim(G:Gauge)(n:ℕ)(S:StepData c f)(u:S.Choices)(i:Bond c)(a b:ℝ)(C M:ℝ): Prop:=∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G f)(x:E), ResV S (G:=G) (a:=a) i (U x) → (∀ j, grantB n (fun v=>U v j) x C)→ S.patch.usesBest S.kernel (S.connector (U x) u.1 i) ∧ (∀ p∈pinPos i, Psalm.uses S p (U x)) ∧ grantB n (fun v=>S.prediction (U v) u i) x M
lemma abort_b{t:ℝ}(h:0<a)(hu:1 ≤ M)(hp:0 ≤ C)(hz: Vim G n S k j a b C D)(T:Dane G n q M)(hv:0≤D) (U:E→ Config G f)(p:∀ i, grantB n (fun v=>U v i) x C): Allows n (abortP S q k j a ∘ U) x ((2:ℝ)^n*((zest n*dam G n (a/2) M C)^(nearT S j).card)*D):=by
 have hh:= (shutter_p (x:=x) q (a/2) (nearT S j) T p).1 -- namespace?
 by_cases hi:ResV S (G:=G) (a:=a) j (U x)
 · exact wind_mono hh ((hz E U x hi p).2.2)
 rw [charged S] at hi; push Not at hi; obtain ⟨i,u,hv'⟩:=hi; apply (allows_const (v:=(0:G.Mat)) x (C:=(2:ℝ)^n*((zest n*dam G n (a/2) M C)^(nearT S j).card)*D) (by have hp:=hh.nonneg; rw [norm_zero]; positivity)).germ
 have hl:ContinuousAt U x:= continuousAt_pi.mpr fun i=>(G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.mpr (p i).smooth.continuousAt
 have hx:Continuous (fun U: Config G f=>toll U i):=by unfold Pressure.toll faceValue; fun_prop
 filter_upwards [(hx.continuousAt.comp hl).eventually (lt_mem_nhds hv')] with y ht; change a<_ at ht; change (0:G.Mat)=_; rw [Function.comp_apply,abortP]; by_cases hw: q.innerShare (a/2) (toll (U y) i)=0
 · unfold shutters; rw [Finset.prod_eq_zero u hw,zero_smul]
 have hx:= q.chosen_lt _ (a/2) (by positivity) hw; change a < toll (U y) i at ht; linarith
end YM.CF.Esti
