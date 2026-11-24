import YM.CF.Esti.Mur
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
open Push.GridApprox AnalyticBridge.LocalGaussian
variable (G:Gauge)(n:ℕ)
def purM := (2:ℝ)^n* ‖ContinuousLinearMap.mul ℝ G.Mat‖ -- tune Frobenius
variable {G n}
abbrev grantB{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](n:ℕ)(g:E→G.El)(x:E)(p:ℝ):=Allows n (G.mat ∘ g) x p
lemma gall{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{f g:E→G.El}{C B:ℝ}(p:grantB n f x C)(k:grantB n g x B):grantB n (fun i=>f i*g i) x (purM G n*C*B):=by
 refine (p.bilinear k (L:=ContinuousLinearMap.mul ℝ G.Mat) le_rfl).germ ?_ -- tune
 refine Eventually.of_forall fun i=> ?_; exact (G.mat_mul ..).symm
lemma gan{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}(g:G.El):grantB n (fun _:E=>g) x G.colorScale:= Allows.mono (allows_const (v:=G.mat g) x le_rfl) (AnalyticBridge.SectorAffine.mat_paid ..).le
variable {d u a h:ℝ}
def gun (P:Patch):ℕ:= Push.GridApprox.reach P + P.L.val+1
lemma insideP(e:Bond c){x:Site f}(p:x∈ predictorUses S e): separation (S.ratio.embed e.1) x ≤ gun S.patch:=by
 rcases p with p|p
 · obtain ⟨i,j,rfl⟩:=p; exact (Work.E08.separation_box_add _ j).trans (by unfold gun; omega)
 obtain ⟨i,j,rfl⟩:=p; set v:=S.ratio.embed (e.1+step e.2)
 have h: separation (S.ratio.embed e.1) v ≤ S.patch.L.val:=by
    rw [show v=S.ratio.embed _ from rfl, Laic.emptio]; apply (Nat.mul_le_mul_left _ (Work.E01.sep_step_le ..)).trans; rw [Nat.mul_one]; rfl
 exact (separation_triangle _ v _).trans ((Nat.add_le_add h (Work.E08.separation_box_add v j)).trans (by unfold gun; omega))
def beamV(e:Bond c):Support f:= (pinPos e).biUnion fun i=> halo (gun S.patch + 1) {S.ratio.embed i} -- need symmetric
abbrev ResV(e:Bond c):= Healthy (G:=G) a (beamV S e)
structure Gson (G:Gauge)(n:ℕ)(a b:ℝ):Prop where
 plog(u:G.El)(h:G.chord u<a):G.lieExp (G.plog (G.mat u))=u ∧ ‖G.plog (G.mat u)‖ < b
lemma curtain(G:Gauge)(n:ℕ)(s:ℝ)(p:0<s):∃ a M:ℝ,0<a∧1≤M∧ Gson G n a s∧∀ g:G.El,G.chord g < a → Allows n G.plog (G.mat g) M:=by
 obtain ⟨K,δ,h⟩:= Push.Uniform.log_receipt G; have hp:=h.1; have hδ:=h.2.1; obtain ⟨b,hb,H⟩:= Metric.nhds_basis_closedBall.eventually_iff.1 (G.plog_diff.eventually (by simp)); obtain ⟨C,hC,hX⟩:=Push.Uniform.exists_allows (f:=G.plog) (isCompact_closedBall (1:G.Mat) b) (fun u hx=>H hx) n
 let a:= min δ (min (b/G.colorScale) (s/K)); have ht:0<a:=lt_min hδ (lt_min (div_pos hb G.colorScale_pos) (div_pos p hp)); refine ⟨a,max 1 C,ht,le_max_left ..,⟨?_⟩,?_⟩ -- tune
 · intro u hx; obtain ⟨k,t⟩:=h.2.2 u (hx.le.trans (min_le_left ..)); have he:G.chord u < s/K:=hx.trans_le ((min_le_right ..).trans (min_le_right ..)); exact ⟨k,t.trans_lt ((mul_comm _ _).trans_lt ((lt_div_iff₀ hp).mp he))⟩
 intro u hx; have hh:=hX (G.mat u) (mem_closedBall.mpr (by rw [dist_eq_norm,←chord_dist]; exact (mul_comm _ _).trans_le ((le_div_iff₀ G.colorScale_pos).mp (hx.le.trans ((min_le_right ..).trans (min_le_left ..)))))); exact ⟨hh.1.of_le le_top,fun i t=>(hh.2 i t).trans (le_max_right ..)⟩
-- vector parameter at ANY cvol, small axis patch through local halo has uses & receipts. Cost polynomial in link jets
abbrev dressM(G: Gauge)(n:ℕ)(x:ℝ):= purM G n* (purM G n*G.colorScale*x)*G.colorScale
abbrev covetM(G:Gauge)(n:ℕ)(C M b:ℝ):=dressM G n (Jet.composeCost n b (Jet.composeCost n M (dressM G n C)))
lemma bindsM (G:Gauge)(n:ℕ)(s d:ℝ)(h:0<s)(hp:1≤ d)(P:Patch):∃ a M:ℝ,0<a∧1≤ M∧∀{c f:Side}(S:StepData c f), S.patch=P → 2*(gun P+1) < f.val →∀(u:S.Choices)(i:Bond c), Opium G n S s d → S.patch.Branches S.kernel G→∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G f)(x:E)(C:ℝ), 1 ≤ C → ResV S (a:=a) i (U x) → (∀ j, grantB n (fun v=>U v j) x C)→ S.patch.usesBest S.kernel (S.connector (U x) u.1 i) ∧ (∀ p∈pinPos i, Psalm.uses S p (U x)) ∧ grantB n (fun v=>S.prediction (U v) u i) x (covetM G n C M d):=by
 let R:=gun P+1; let T:ℝ:= 16*(2*(R:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ); obtain ⟨t,M,hT,hM,hκ,H⟩:= curtain G n (s/2) (half_pos h); let a:=t/(2*(max 1 T)); have h':0<a:= div_pos hT (mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_left ..)))
 refine ⟨a,M,h',hM,@fun c f S he hu u i o q E _ _ U x C hC ht hU=>?_⟩
 let z:=S.ratio.embed i.1; obtain ⟨g,hg⟩:=Work.E08.axial_patch z (U x) (gun P) R (Nat.le_refl _) hu a h'.le (fun k l b=> by
    by_contra! V; have hp: k∈beamV S i:=by unfold beamV; rw [he]; exact mem_biUnion.mpr ⟨_,mem_insert_self i.1 _,halo_spec.mpr ⟨_,mem_singleton_self _,l⟩ ⟩
    exact disjoint_left.mp ht hp ((flags_spec ..).mpr ⟨(k,b),Work.E01.base_touched _,V⟩))
 let X(v):= Lattice.gauge g (U v); let Z(e:Bond f):Prop:= e.1 ∈ sideP S i; have he'(e:Bond f)(v:Z e):G.chord (X x e) < t:=by
    apply (hg e (he ▸ insideP S i v)).trans_lt; change T*a<_; apply (mul_le_mul_of_nonneg_right (le_max_right ..) h'.le).trans_lt; unfold a; have hx:0 < max 1 T:=zero_lt_one.trans_le (le_max_left ..); rw [mul_comm,div_mul_eq_mul_div]; rw [div_lt_iff₀ (by positivity)]; nlinarith
 let f(v:E): Directions G _ :=fun j=> if Z j then G.plog (G.mat (X v j)) else 0
 have hG(j:Bond _):grantB n (fun v=>X v j) x (dressM G n C):=gall (gall (gan _) (hU _)) (gan _) -- tune
 let m:=Jet.composeCost n M (dressM G n C); have hm:0 ≤ m:=by unfold m Jet.composeCost dressM purM; have hx:=G.colorScale_pos; positivity
 have h': Allows n f x m:=by
    refine allows_pi hm fun j=> ?_; unfold f; split; next p=> exact (H _ (he' j p)).comp (f:=fun v=>G.mat (X v j)) (hG j)
    exact allows_const x (by rw [norm_zero]; exact hm)
 have he:∀ᶠ v in 𝓝 x,Agrees (sideP S i) (X v) (increment 1 (f v)):=by
    have ht(j:Bond _)(p:Z j):∀ᶠ v in 𝓝 x,X v j=increment 1 (f v) j:=by
       let W(v):= X v j; have ht:ContinuousAt W x:= (G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.mpr (hG j).smooth.continuousAt; filter_upwards [(G.continuous_chord.continuousAt.comp ht).eventually (gt_mem_nhds (he' j p))] with v k
       unfold increment; simp only [f, if_pos p,Pi.one_apply,mul_one]; exact (hκ.plog _ k).1.symm
    have hx(j:Bond _): ∀ᶠ v in 𝓝 x,Z j→ X v j=increment 1 (f v) j:=by by_cases q:Z j; exact (ht j q).mono fun _ p _=>p; exact Eventually.of_forall fun x p=>(q p).elim
    filter_upwards [eventually_all.mpr hx] with v hv; exact fun j h _=> hv j h
 have hv : ‖f x‖<s:=by
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (show 0 ≤ s/2 by positivity)).mpr fun i=> ?_) (half_lt_self h); unfold f; split; next p=>exact (hκ.plog _ (he' i p)).2.le
    rw [norm_zero]; positivity
 have ht:= he.mono fun i' p=> connector_p S G q i u _ _ p; obtain ⟨hs,hb,Hb⟩:=o.uses _ hv u i
 refine ⟨bestP S G q g (U x) u i (ht.self_of_nhds.symm ▸ hb),fun i' k=> ?_,?_⟩ -- tune
 · have he' :=(o.uses _ hv u (i',0)).1; exact (Psalm.uses_gauged S g _).1 ((Psalm.uses_same S _ (agrees_mono he.self_of_nhds (Psalm.within_predictor k))).2 he')
 have hG: grantB n (fun v=> S.prediction (X v) u i) x (Jet.composeCost n d m):=by apply (Hb.comp h').germ; filter_upwards [ht] with v k; change _= G.mat _; simp_rw [StepData.prediction,k] -- tune
 let g' := g z; let b:= g (S.ratio.embed (i.1+step i.2)); apply (gall (gall (gan g'⁻¹) hG) (gan b)).germ; filter_upwards [] with v; simp only [Function.comp_apply]; unfold g' b X; rw [gauge_t G _ _ q]; unfold z; group
end YM.CF.Esti
