import YM.CF.Lich.Stint
import YM.CF.Lich.Prix
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet
section
open AnalyticBridge.RelativeLogdet
open Forge
lemma late_sum {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ E][CompleteSpace F]{f':ℕ→E→F}{b c:ℕ→ℝ}{n:ℕ}{x:E}(hp:∀ᶠ i in 𝓝 x,∀ j,Allows n (f' j) i (b j))(h:Summable b)(u:Summable c)(v:∀ i,Allows n (f' i) x (c i)): Allows n (fun i=>∑' j,f' j i) x (∑' j,c j) :=by
 let μ:= (Measure.count:Measure ℕ)
 obtain ⟨V,hV,g,t⟩:=_root_.mem_nhds_iff.mp hp
 have ht:∀ y∈V,∀ i:ℕ, Allows n (f' i) y (b i):= fun y u=>hV u
 have he: Integrable b μ:=integrable_count_iff.mpr (h.abs)
 have hy(y:E)(p:y∈V):Integrable (fun i=> f' i y) μ:=integrable_count_iff.mpr (Summable.of_norm_bounded h fun i=> by rw [norm_norm]; exact (ht y p i).value)
 have hm:=under (l:=g) (fun j y p=>(ht y p j).smooth) (fun y _=> StronglyMeasurable.of_discrete) he (fun z y p=>ht y p z)
 have hW: (fun i=>∫ j,f' j i∂μ)=ᶠ[𝓝 x] fun i=>∑' j,f' j i:=by
    filter_upwards [g.mem_nhds t] with i p; rw [integral_countable (hy i p)]; simp [μ]
 refine Allows.germ ?_ hW
 refine ⟨hm.germ g t,fun i p=>?_⟩; change ‖iteratedFDeriv ℝ i (Planned.AtomRegular.average μ f') x‖≤ _
 let F'(j):= iteratedFDeriv ℝ i (f' j) x; rw [(hm.less p).differentiate g t]
 have he:Integrable c μ:=integrable_count_iff.mpr u.abs
 calc
   ‖∫ j,F' j ∂μ‖ ≤ ∫ j,‖F' j‖∂μ:= norm_integral_le_integral_norm _
   _ ≤ ∫ j,c j∂μ:= integral_mono (hm.integrate t p).norm he (fun z=> (v z).norm_le i p)
   _ = _:=by rw [integral_countable he]; simp [μ]
lemma compact_p{F E:Type*}[TopologicalSpace E][TopologicalSpace F]{X:Set E}(Y:F→E→Prop)(h:IsCompact X)(o:F)(hp:∀ x∈ X,∀ᶠ p:F×E in 𝓝 (o,x),Y p.1 p.2):∀ᶠ i in 𝓝 o,∀ x∈ X,Y i x:=by
 let W:= {p:F× E|Y p.1 p.2}; have hl: ({o}:Set F) ×ˢ X ⊆ interior W:=fun ⟨x,y⟩ v=>by
    rw [show x=o from Set.mem_singleton_iff.mp v.1]; exact mem_interior_iff_mem_nhds.mpr (hp _ v.2)
 obtain ⟨t,u,g,h,v,hp,ht⟩:=generalized_tube_lemma isCompact_singleton h isOpen_interior hl; exact (show ∀ᶠ x in 𝓝 o,x∈t from g.mem_nhds (v (Set.mem_singleton o))).mono fun z q i w=>(show (z,i)∈ W from interior_subset (ht (Set.mk_mem_prod q (hp w))))
-- openness price W requires heart: continuous A; use trans from St when P=1 or other, or explicit
variable {A E F:Type}[Fintype A][DecidableEq A][NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{Q:E→Matrix A A ℝ}{P:E→ℝ→Matrix A A ℝ}{x:E}{n:ℕ}{a b c d:ℝ}
lemma plume (Y: E→ℝ→F)(r:ℝ)(p: Allows n (fun i=> Y i r) x a)(q:ContDiffAt ℝ (↑n) (Function.uncurry Y) (x,r))(h:a<c):∀ᶠ i:E×ℝ in 𝓝 (x,r), Allows n (fun y=>Y y i.2) i.1 c:=by
 have hp:ContDiffAt ℝ (↑n) (fun i:ℝ×E=> Y i.2 i.1) (r,x):= q.comp (f:=Prod.swap) (r,x) (contDiffAt_snd.prodMk contDiffAt_fst)
 have ht:= Warm.together hp; have hw:Tendsto Prod.swap (𝓝 (x,r)) (𝓝 (r,x)):=continuous_swap.continuousAt -- tune
 have he(j:Fin (n+1)):∀ᶠ i:E×ℝ in 𝓝 (x,r), ‖iteratedFDeriv ℝ (j:ℕ) (fun y=>Y y i.2) i.1‖ ≤ c :=by
    have hj:j.val ≤ n:=Nat.lt_add_one_iff.mp j.isLt
    exact hw.eventually ((ht.light _ hj).norm.eventually (gt_mem_nhds ((p.norm_le j hj).trans_lt h)) |>.mono (fun v p=> LE.le.trans p.le le_rfl))
 filter_upwards [eventually_all.mpr he,hw.eventually ht.lit] with i v w
 exact ⟨w,fun j t=>v ⟨j,Nat.lt_succ_of_le t⟩⟩
lemma sprain (p:PriceW Q P n x a b)(h:a<c)(k:b<d)(hc:ContinuousAt Q x) :∀ᶠ i in 𝓝 x, PriceW Q P n i c d:=by
 have he:=compact_p (fun i t=>ContDiffAt ℝ (↑n) (uncurry P) (i,t) ∧ ContDiffAt ℝ (↑n) (uncurry (keystone Q P)) (i,t)∧ ContDiffAt ℝ (↑n) (fun z:E×ℝ=> tea_r (Q z.1) (P z.1) z.2) (i,t)∧ Protected n (fun y=>keystone Q P y t) i c ∧ Protected n (fun y=>tea_r (Q y) (P y) t) i d ∧ IsUnit (edgeM (Q i) t).det) (show IsCompact Isle from isCompact_Icc) x (fun y v=>?_)
 swap
 · have ht:=p.pre y v; have hp:=p.St y v; have hr:=p.Tag y v
   have hz:= ((show ContinuousAt (fun i:E×ℝ=> (edgeM (Q i.1) i.2).det) (x,y) from by unfold edgeM AnalyticNext.ConnectedActivity.ResolventVolume.graph; fun_prop (disch := aesop)).eventually_ne ((p.heart y v).ne_zero))
   obtain ⟨m,s⟩:=p.paid y v
   filter_upwards [ht.eventually (by simp), hp.eventually (by simp), hr.eventually (by simp),plume (fun i y=> paintO (keystone Q P i y)) y m ((paintO (τ:=A)).contDiff.contDiffAt.comp _ hp) h, plume (fun i t=>paintO (tea_r (Q i) (P i) t)) y s ((paintO (τ:=A)).contDiff.contDiffAt.comp _ hr) k,hz] with i a b c d e g
   exact ⟨a,b,c,d,e,g.isUnit⟩
 filter_upwards [he] with i a; refine ⟨fun j v=>(a j v).1,fun j v=>(a j v).2.1,fun j v=>(a j v).2.2.1,fun j v=>(a j v).2.2.2.2.2,fun j v=>⟨(a j v).2.2.2.1,(a j v).2.2.2.2.1⟩⟩
end
end YM.CF.Fief
