import YM.CF.Rink.Solo
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rink
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
variable {K:Teller G}
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
open Affine Reine
section
variable (T:Tube G S)(x:ℝ)(M:Monk G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(h:K.Funds S T)(p: FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(hr:0<β)
include p h hm hf hr
lemma burn_t(s:Signed)(b:Site c)(k:ℕ)(i:Bond f): opus T x q d l β k i (clue S s b M)=opus T x q d l β k (diagram s b S i) M:=by
 let N:=clue S s b M; let Y:=diagram s b S; let Q:=fiber s b M.V S; refine congrArg₂ (·+·) (congrArg (-β*·) (av_a s _ _ fun v=>?_)) (shape_h M N i Q Y (Cay.adjust T x q d l β) (Cay.adjust T x q d l β) (funext fun i=>adjust_s T x (rough M i) q d l β h p hm hf hr s b) rfl).symm
 refine Finset.sum_equiv (lawn S (Channels.offset s b v)) ?_ fun j _=> (shape_h M N i Q Y (dense T x q d l β (s*v) _) (dense T x q d l β v j) (funext fun u=> spark_s T x (rough M u) q d l β h p hm hf s v b j) rfl).symm
 intro i; simp only [rush,clue,mem_filter,mem_univ,true_and,dome_map, herZ]
lemma burn_g(g:Site c→ SU.group.El)(k:ℕ)(i:Bond f): opus T x q d l β k i (shiftZ g M)= opus T x q d l β k i M:=by
 let Y:=Equiv.refl (Bond f); let Q:= Gauges.rotating (constantGauge g S.ratio); let N:=shiftZ g M; refine congrArg₂ (·+·) (congrArg (fun b:Signed→ℝ=> -β*averaged b) (funext fun v=>?_)) (shape_h M N i Q Y (Cay.adjust T x q d l β) (Cay.adjust T x q d l β) (funext fun I=>rota_g (β:=β) (M:=rough M I) (q:=q) (l:=l) (d:=d) g h p hm hf hr) rfl).symm
 exact Finset.sum_congr rfl fun j hp=>(shape_h M N i Q Y (dense T x q d l β v j) (dense T x q d l β v j) (funext fun u=>congrFun (Cay.wage (M:=rough M u) (q:=q) (d:=d) (β:=β) (l:=l) g h p hm hf v).1 j) rfl).symm -- tune
include hA hB
lemma burn_e(k:ℕ)(i:Bond f): opus T x q d l β k i (cedar M)= opus T x q d l β k i M:=by
 let Y:=Equiv.refl (Bond f); let Q:= Char.shiftF (Bond f); let N:= cedar M; refine congrArg₂ (·+·) (congrArg (fun b:Signed→ℝ=> -β*averaged b) (funext fun v=>?_)) (shape_h M N i Q Y (Cay.adjust T x q d l β) (Cay.adjust T x q d l β) (funext fun I=>adjust_f T x (rough M I) q d l β h p hm hf hA hr) rfl).symm
 exact Finset.sum_congr rfl fun j hp=>(shape_h M N i Q Y (dense T x q d l β v j) (dense T x q d l β v j) (funext fun u=>spark_e T x (rough M u) q d l β h p hm hf hA hB v j) rfl).symm
-- use directly in wish. no smoothness
lemma heat_f(s:Signed)(j:Along S): shotB (dense T x q d l β s j) M= shotB (dense T x q d l β s j) (cedar M):= shine_p M (cedar M) (Char.shiftF _) (Equiv.refl _) _ _ (funext fun u=> spark_e T x (rough M u) q d l β h p hm hf hA hB s j) rfl
omit hA hB hr
lemma heat_s(s v:Signed)(b:Site c)(j:Along S): shotB (dense T x q d l β v j) (clue S s b M)=shotB (dense T x q d l β (s*v) (lawn S (Channels.offset s b v) j)) M:= (shine_p M (clue S s b M) (fiber s b M.V S) (diagram s b S) (dense T x q d l β (s*v) (lawn S (Channels.offset s b v) j)) (dense T x q d l β v j) (funext fun u=> spark_s T x (rough M u) q d l β h p hm hf s v b j) rfl).symm
lemma heat_g(s:Signed)(g:Site c→ SU.group.El)(j:Along S): shotB (dense T x q d l β s j) (shiftZ g M)=shotB (dense T x q d l β s j) M:= (shine_p M (shiftZ g M) (Gauges.rotating (constantGauge g S.ratio)) (Equiv.refl _) (dense T x q d l β s j) (dense T x q d l β s j) (funext fun u=>congrFun (Cay.wage (M:=rough M u) (q:=q) (d:=d) (β:=β) (l:=l) g h p hm hf s).1 j) rfl).symm
end
end YM.CF.Rink
