import YM.CF.Rink.Mel
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
variable (T:Tube G S)(x:ℝ)(M:Monk G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(h:K.Funds S T)(p: FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)
lemma coin_f(r:ℕ)(V:Config G c)(U:Config G f)(k:S.Choices)(i:Dill S)(h: S.patch.Branches S.kernel G): Yaught T r (fiery G x S.patch.L) (temp x) (Reef.echo V) (Reef.echo U) k i= Yaught T r (fiery G x S.patch.L) (temp x) V U k i:=by
 let W:=Reef.echo V; let F:=Reef.echo U; let R:= S.prediction F k; let Q:= S.prediction U k; have hp:R=Reef.echo Q:= (Reef.proceeds h U k).1
 have hs {g:Side}(U:Config G g)(i:Cell g): sore G (faceValue (Reef.echo U) i)=sore G (faceValue U i):=by unfold faceValue sore; rw [Reef.echo_t,swing, cold,frolic.norm_map]
 let G₀(i:Twin c):= badge; let G₁(i:Twin f):= badge; let G₂(i:Bond c):= badge; let G₃(i:Co c Gain):= badge; have hh(i): Tube.Z S R W i=G₂ i (Tube.Z S Q V i):=by rw [hp]; exact zvE ..
 have he(i):T.Xf r F i= G₁ i (T.Xf r U i):= plotE ..; have hc(i): T.Xn r W i=G₀ i (T.Xn r V i):= plotE ..
 have hhF(i j z): T.Φ r W i j (G₀ j z)= G₁ i (T.Φ r V i j z):= leapsE ..; have hhI(i j z): T.Φ' r W i j (G₀ j z)=G₂ i (T.Φ' r V i j z):= kickedE ..; have hhN(i j z): T.N r W i j (G₀ j z)=G₃ i (T.N r V i j z):=lane_b T r V i j z
 rcases i with i|i|i|i; all_goals unfold Yaught; simp only [Sum.elim_inl,Sum.elim_inr]
 · rw [hiatus,hiatus]; unfold KissP; rw [hs]; apply congrArg (T.high.direct*sore G (faceValue U i)+ ·); refine sum_congr rfl fun j _=> ?_; unfold RiftF; rw [he,Rink.cog hhF hc,← map_sub,(G₁ (i,j)).norm_map]
 · rw [iham,iham]; unfold KissI tideX; have hv: sore G (W i * (R i)⁻¹) = sore G (V i*(Q i)⁻¹) :=by -- tune incorrect
      rw [hp]; unfold W Reef.echo; rw [←map_inv,←map_mul]; unfold sore; rw [swing,cold,frolic.norm_map]
   rw [hv]; unfold RiftI; rw [hh,Rink.cog hhI hc,←map_sub,(G₂ i).norm_map]
 · rw [inka,inka,zpia,zpia]; unfold KissQ; rw [hs]; apply congrArg (-(T.low.direct*sore G (faceValue V i))+ ·); refine sum_congr rfl fun j _=> ?_; unfold RiftL RiftD lGap dGap; rw [hc, Rink.rein hhF he,Rink.rein hhI hh,Rink.rein hhF (Rink.cog hhF hc),Rink.rein hhI (Rink.cog hhI hc),Rink.rein hhN (Rink.cog hhN hc)] -- tune redex
   simp only [← map_add (G₀ (i,j)), ←map_sub (G₀ (i,j)),LinearIsometryEquiv.inner_map_map]; rfl -- tune newline
 rw [nk,nk]; unfold RiftN; rw [Rink.cog hhN hc,(G₃ i).norm_map]
lemma gplot_f(K:PathData G)(r:Reef.Rare K)(U:Config G f)(k:ℕ)(i:Site f): turF K k (Reef.echo U) i= turF K k U i:=by
 have hp{t:ℕ}(Q:ℕ→ RG.Atom G t)(H:∀ j, Reef.Prist (Q j)): gplot (batch Q k) (Reef.echo U) i=gplot (batch Q k) U i:=by
    refine tsum_congr fun j=>?_ ; unfold batch; split
    next hx=> unfold RG.Atom.unmasked; simp_rw [Reef.tollSlot]; exact H j _
    next q=> simp_rw [dimU]
 exact congrArg₂ (·+·) (hp _ fun i=>(r i).2.1) (hp _ fun i=>(r i).2.2)
include p h hm hf
local notation "U"=> M.sent x T q d l β
lemma spark_s(s v:Signed)(b:Site c)(i:Along S):dense T x q d l β v i (clue S s b M)=dense T x q d l β (s*v) (lawn S (Channels.offset s b v) i) M:=by
 let N:=clue S s b M; let t:=Channels.offset s b v; have he : ballot T x (pull v 0 N.V) (pull v 0 (N.sent x T q d l β)) (choice v N.k) i=ballot T x (pull (s*v) 0 M.V) (pull (s*v) 0 U) (choice (s*v) M.k) (lawn S t i):= by rw [show N.sent x T q d l β= _ from space_s T x q d l β s b M h p hm hf]; exact bloom s v b M.V U M.k i h -- tune i varies
 cases i with
 | inl i=>exact congrArg₂ (·-·) he (glow_s T x M q d l β h p hm hf s v b i)
 | inr i=>exact he
include hA hB
lemma spark_e(v:Signed)(i: Along S):dense T x q d l β v i (cedar M)= dense T x q d l β v i M:=by
 let N:=cedar M; have he: ballot T x (pull v 0 N.V) (pull v 0 (N.sent x T q d l β)) (choice v N.k) i=ballot T x (pull v 0 M.V) (pull v 0 U) (choice v M.k) i:=by
    rw [show N.V=Reef.echo M.V from rfl, show N.sent x T q d l β=_ from echo_s T x q d l β M h p hm hf hA,Reef.echo_p,Reef.echo_p]; rcases i with i|i|i; exact coin_f T x _ _ _ _ i (funds_branch h); exact gplot_f T.up hA _ _ i; exact congrArg Neg.neg (gplot_f T.down hB _ _ i)
 cases i with
 | inl i=>exact congrArg₂ (·-·) he (congrFun (congrArg (Gloss S v) (funext (purs_e T x M q d l β h p hm hf hA))) i)
 | inr i=>exact he
end
end YM.CF.Rink
