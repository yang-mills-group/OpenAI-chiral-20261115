import YM.CF.Rink.Cap
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
variable (T:Tube G S)(x:ℝ)(M:Monk G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(h:K.Funds S T)(p: FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x)
variable (hp:Reef.Rare T.up)
-- on every such pose. no scout or `offset rows actual` for tin
local notation "F₀"=> M.sent x T q d l β
abbrev purse (i:Slots S):ℝ:=media i (wheel M.key M.park T x M.k q d (M.bush x) (M.fuel x T q d l β) M.V)-media i (wheel M.key M.park T x M.k q d (M.bush x) (liftN T x M.V M.k M.key M.park q d (M.bush x) l) M.V)
include h p hm hf
lemma capX(s:Signed)(b:Site c)(i:Slots S):purse T x (clue S s b M) q d l β i=purse T x M q d l β ((calendar x M.key M.park s b).slots i):=by
 obtain ⟨σ,a,H,A⟩:=h.feeds; rw [←h.high] at H
 have he:= Char.turned T M.key M.park x M.V M.k q d (M.bush x) s b H (funds_branch h)
 let N:=clue S s b M; unfold purse; rw [space_f T x q d l β s b M h p hm hf,blank_c T x q d l s b M h,show N.bush x=_ from gen x S s b M]; exact congrArg₂ (·-·) (wheel_p he.test h _ i) (wheel_p he.test h _ i)
open Gauges
lemma purs_g(g:Site c→ SU.group.El)(i:Slots S):purse T x (shiftZ g M) q d l β i=purse T x M q d l β i:=by
 obtain ⟨σ,a,H,A⟩:=h.feeds; rw [←h.high] at H; unfold purse; rw [buzz g M q x β d h l m p hm hf, brag g M q x d h l]
 have he:= gaugeH T M.key M.park x M.V M.k q d (M.bush x) g H (funds_branch h); exact congrArg₂ (·-·) (wheel_p he.test h _ i) (wheel_p he.test h _ i)
include hp
lemma purs_e(i:Slots S):purse T x (cedar M) q d l β i=purse T x M q d l β i:=by
 obtain ⟨σ,a,H,A⟩:=h.feeds; rw [←h.high] at H; unfold purse; rw [echo_f T x q d l β M h p hm hf hp,echo_c T x q d l M h hp]
 have he:=storyE T M.key M.park x M.V M.k q d (M.bush x) (funds_branch h) H hp; exact congrArg₂ (·-·) (wheel_p he.test h _ i) (wheel_p he.test h _ i)
omit hp
lemma glow_s(s v:Signed)(b:Site c)(i:Dill S): Gloss S v (purse T x (clue S s b M) q d l β) i=Gloss S (s*v) (purse T x M q d l β) (stepZ S (Channels.offset s b v) i):= by
 have he(B Q:Slots S →ℝ)(H:∀ i,B i=Q (perChannel s b S i)): Gloss S v B i= Gloss S (s*v) Q (stepZ S (Channels.offset s b v) i):=by
    unfold Gloss; rcases i with i|i|i|i
    · refine sum_congr rfl fun j _=>?_ ; exact H (v,.inl (i,j))
    exact H (v,.inr i); rfl; rfl
 exact he _ _ (capX T x M q d l β h p hm hf s b)
lemma roll_pred (s v:Signed)(b:Site c): S.prediction (pull v 0 ((clue S s b M).sent x T q d l β)) (choice v (clue S s b M).k)=Lattice.translate (Channels.offset s b v) (S.prediction (pull (s*v) 0 F₀) (choice (s*v) M.k)):=by
 let H:= funds_branch h; rw [(carry v H ..).2,(carry (s*v) H ..).2,space_s T x q d l β s b M h p hm hf]; dsimp only [clue,Channels.ticket]; rw [S.prediction_channel H,Equiv.apply_symm_apply,channel_turn] -- tune
lemma fence_s(s v:Signed)(b:Site c)(i:Dill S): fence T x (clue S s b M) q d l β v i=fence T x M q d l β (s*v) (stepZ S (Channels.offset s b v) i):=by
 refine congrArg₂ (·-·) ?_ (glow_s T x M q d l β h p hm hf s v b i); let N:=clue S s b M; change payX T x i (pull v 0 (N.sent x T q d l β)) (S.prediction _ (choice v N.k)) (pull v 0 N.V)=_
 rw [roll_pred T x M q d l β h p hm hf s v b, show N.V=pull s b M.V from rfl, show N.sent x T q d l β=_ from space_s T x q d l β s b M h p hm hf,channel_turn, channel_turn,Channels.offset_fine]; exact score_s ..
lemma fence_g(g:Site c→ SU.group.El)(v: Signed):fence T x (shiftZ g M) q d l β v=fence T x M q d l β v:=by
 funext i; refine congrArg₂ (·-·) ?_ (congrFun (congrArg (Gloss S v) (funext (purs_g T x M q d l β h p hm hf g))) i); let N:=shiftZ g M; change payX T x i (pull v 0 (N.sent x T q d l β)) (S.prediction _ (choice v M.k)) (pull v 0 (Lattice.gauge g M.V))=_
 rw [show N.sent x T q d l β=_ from gauge_s T x q d l β g M h p hm hf, vega g h,Work.F05.pull_gauge_zero,gust_p (funds_branch h)]; exact score_g .. -- tune
include hp
lemma fence_e(v: Signed):fence T x (cedar M) q d l β v=fence T x M q d l β v:=by
 funext i; refine congrArg₂ (·-·) ?_ (congrFun (congrArg (Gloss S v) (funext (purs_e T x M q d l β h p hm hf hp))) i); let N:= cedar M; change payX T x i (pull v 0 (N.sent x T q d l β)) (S.prediction _ (choice v M.k)) (pull v 0 (Reef.echo M.V))=_
 rw [show N.sent x T q d l β=_ from echo_s T x q d l β M h p hm hf hp, Reef.echo_p,Reef.echo_p,(proceeds (funds_branch h) _ _).1]; exact score_f .. -- tune
end
end YM.CF.Rink
