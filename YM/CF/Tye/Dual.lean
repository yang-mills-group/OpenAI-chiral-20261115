import YM.CF.Rink.Paid
import YM.CF.Rink.Noise
import YM.CF.Corne.Pink
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tye
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
open Corne Rink Primitives.HaarLogJets.Guard
variable (T:Tube G S)(M: Monk G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(A:Stores S)(h: K.Funds S T) (hu: Reef.Rare T.up)(hd:Reef.Rare T.down)(hm:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(ht:120 ≤ radiusB x)(hz:0 < m)(R:ChartRatio SU.group)(v:ℝ)(p:LocalRatio R)(hg:0<v)(hx:4*v<R.radius)
local notation "Q"=> calendar x M.key M.park
variable (s:Signed)(b:Site c)(g:Site c→SU.group.El)
lemma ansP(i: Site c)(t:Bond f): ansC (S:=S) (affine s b i) (diagram s b S t)=ansC (S:=S) i t:=by
 let u:= diagram s b S t; let X:= StepData.sendSites s b; have he:grove S u=(grove S t).map X.toEmbedding:=by
    apply Finset.coe_injective; rw [coe_map,grove_x]; rw [grove_x]; exact Tensor.moves_points ..
 change (if X i ∈ grove S u then ((grove S u).card:ℝ)⁻¹ else 0)= _; rw [he]; simp [ansC]
local notation "Y₀"=> clue S s b M
local notation "Y"=> page s b M
local notation "U"=> shiftZ g M
local notation "F"=> cedar M
include h hm ht hz p hg hx
lemma flare_s(i:(Y₀).zoo x): Corne.flare T x q d l β R v Y₀ i=Corne.flare T x q d l β R v M ((Q s b).onKey i):=by
 unfold Corne.flare; let f:=M.fuel x T q d l β; let Z:=tape f; have he : (Y₀).fuel x T q d l β=Orthogonal.move (onBond (page s b M)) (Q s b).onKey f:=space_f T x q d l β s b M h hm hz ht
 have hp:tape ((Y₀).fuel x T q d l β) i=Y i.val.val (Z ((Q s b).onKey i)):=by rw [he]; exact move_tape (onBond (page s b M)) (Q s b).onKey f _
 rw [hp]; change logGuard q R v (Channels.scatter s (S.ratio.embed b) _ i.val.val _) = _; unfold Channels.scatter; split; exact log_extended_turn _ true q hg p hx _; rfl
lemma flare_g(i:(U).zoo x): Corne.flare T x q d l β R v U i=Corne.flare T x q d l β R v M i:=by unfold Corne.flare; rw [buzz g M q x β d h l m hm hz ht,Slate.Pogo,move_tape]; exact log_extended_turn _ false q hg p hx _
include hu
lemma flare_f(i:(F).zoo x): Corne.flare T x q d l β R v F i=Corne.flare T x q d l β R v M i:=by unfold Corne.flare; rw [echo_f T x q d l β M h hm hz ht hu,move_tape]; exact log_p p hg hx _ _
lemma kite_f(i:Site c): Corne.kite T x q d l (cedar M) β R v i=Corne.kite T x q d l M β R v i:= by unfold Corne.kite dua; exact sum_congr rfl fun j _=> congrArg (ansC (S:=S) i j.val.val*·) (flare_f T M x q d l β h hu hm ht hz R v p hg hx _)
omit hu
lemma kite_g(i:Site c): Corne.kite T x q d l U β R v i=Corne.kite T x q d l M β R v i:= by unfold Corne.kite dua; exact sum_congr rfl fun j _=> congrArg (ansC (S:=S) i j.val.val*·) (flare_g T M x q d l β h hm ht hz R v p hg hx g _)
lemma kite_s(i:Site c): Corne.kite T x q d l Y₀ β R v i=Corne.kite T x q d l M β R v (affine s b i):= by
 unfold Corne.kite dua; rw [←Equiv.sum_comp (Q s b).onKey]; exact sum_congr rfl fun j _=> congrArg₂ (·*·) (ansP s b (S:=S) i j.val.val).symm (flare_s T M x q d l β h hm ht hz R v p hg hx s b j)
omit p hg hx
end YM.CF.Tye
