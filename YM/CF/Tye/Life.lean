import YM.CF.Tye.Petal
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
local notation "Y₀"=> clue S s b M
local notation "Y"=> page s b M
local notation "U"=> shiftZ g M
local notation "F"=> cedar M
local notation "t'"=> turnStore
local notation "M'"=>M.sent x T q d l β
variable (t:Signed)(r j:ℕ)(α:ℝ)(B W:BudgetPoint)
local notation "Z"=> Channels.offset s b t
local notation "L"=> S.ratio.embed (Channels.offset s b t)
open Cloak
include h hm hz ht
lemma park_s(i:Site f)(K':ℕ→RG.Atom G n) : park ((clue S s b M).sent x T q d l β) t (clue S s b M).key q B K' i= park M' (s*t) M.key q B K' (i+L):=by
 rw [space_s T x q d l β s b M h hm hz ht]; unfold park; rw [channel_turn,Channels.offset_fine]; exact tsum_congr fun j=> lush_t _ _ _ _ _ (taxes M.key _ _ _) _
omit h hm hz ht in
lemma visit_s(i:Site c)(K':ℕ→RG.Atom G n): visit (clue S s b M).V t (clue S s b M).key W K' i=visit M.V (s*t) M.key W K' (i+Z):=by
 unfold visit clue; dsimp only; rw [channel_turn]; exact tsum_congr fun j=> peer_t _ _ _ _ _ (toured M.key _ _ _) _
local notation "Ξ"=> Equiv.sumCongr (Equiv.addRight L) (Equiv.addRight Z)
lemma oak_s : oak T x (clue S s b M) q d l β B W r (Locations.book s b A)= oak T x M q d l β B W r A:=by
 unfold oak; apply congrArg (-β*·); apply av_a s; intro t; let L':=S.ratio.embed (Channels.offset s b t); refine Finset.sum_equiv (Equiv.sumCongr (Equiv.addRight L') (Equiv.addRight (Channels.offset s b t))) ?_ ?_ -- tune t local scopes
 · intro i; simp only [lyn,mem_filter,mem_univ,true_and,dome_map]; rw [herZ]; rfl -- no goals
 intro i _; cases i with
 | inl i=> exact congrArg₂ (·+·) (park_s T M x q d l β h hm ht hz s b t B _ _) (park_s T M x q d l β h hm ht hz s b t B _ _)
 | inr i=> exact congrArg Neg.neg (congrArg₂ (·+·) (visit_s M s b t W i _) (visit_s M s b t W i _))
lemma heat_s(i:Along S): heatR T ((clue S s b M).sent x T q d l β) (Y₀).V t (Y₀).key q B W x α i=heatR T M' M.V (s*t) M.key q B W x α (lawn S Z i):=by
 rcases i with (i|i|i|i)|i|i; exact rfl; exact rfl; swap; exact rfl
 · apply congrArg (-α * ·); change Esti.king _ _ _ _ _ W.threshold (pull t 0 (pull s b M.V)) _=_; rw [channel_turn]; exact king_t _ _ _ _ _ _ (toured M.key _ _ _) ..
 · exact park_s T M x q d l β h hm ht hz s b t B i _
 exact congrArg Neg.neg (visit_s M s b t W i _)
-- gauge and charge echo
lemma park_g(i:Site f)(K':ℕ→ RG.Atom SU.group n)(p:∀ i,(K' i).Invariant): park ((shiftZ g M).sent x T q d l β) s (U).key q B (batch K' r) i=park M' s M.key q B (batch K' r) i:=by
 rw [gauge_s T x q d l β g M h hm hz ht]; unfold park; rw [Work.F05.pull_gauge_zero]; exact tsum_congr fun j=>lushP i _ _ (gauge_l _ _) _ (batch_g _ i _ j r _ p)
omit h hm hz ht in
lemma visit_g(i:Site c)(K':ℕ→ RG.Atom SU.group n)(p:∀ i,(K' i).Invariant): visit (U).V s (U).key W (batch K' r) i=visit M.V s M.key W (batch K' r) i:=by
 unfold visit; rw [show (U).V= _ from rfl]; change (∑' i',peer_k _ _ _ _ (pull s 0 (Lattice.gauge _ _)))= _; rw [Work.F05.pull_gauge_zero]; exact tsum_congr fun j=>peerP i _ _ (gauge_l _ _) _ (batch_g _ i _ j r _ p)
lemma oak_g: oak T x (U) q d l β B W r A= oak T x M q d l β B W r A:=by
 obtain ⟨σ,c',H,Q'⟩:=h.feeds; unfold oak; apply congrArg (-β*·); apply congrArg averaged; ext s; refine sum_congr rfl fun i _=>?_
 cases i with
 | inl i=> exact congrArg₂ (·+·) (park_g T M x q d l β h hm ht hz s g _ B i _ (fun v=>(H.invariant v).2.1)) (park_g T M x q d l β h hm ht hz s g _ B i _ (fun v=>(H.invariant v).2.2))
 | inr i=> exact congrArg Neg.neg (congrArg₂ (·+·) (visit_g M s g _ W i _ (fun v=>(Q'.invariant v).2.1)) (visit_g M s g _ W i _ (fun v=>(Q'.invariant v).2.2)))
omit h hm ht hz in
lemma via (X Y': Config G f)(V W':Config G c)(o:Stores S)(p:∀ i:Site f, park Y' s o q B (batch T.up.loop (Stores.till x)) i=park X s o q B (batch T.up.loop (Stores.till x)) i)(u:∀ i:Site c,visit W' s o W (batch T.down.loop (Stores.till x/S.patch.L.val)) i=visit V s o W (batch T.down.loop (Stores.till x/S.patch.L.val)) i) (hp:∀ i:Cell c,Esti.king (traceZ (turnStore s o).flags) T.down T.low (Stores.till x) S.patch.L.val W.threshold (pull s 0 W') i= Esti.king (traceZ (turnStore s o).flags) T.down T.low (Stores.till x) S.patch.L.val W.threshold (pull s 0 V) i)(i:Along S): heatR T Y' W' s o q B W x α i=heatR T X V s o q B W x α i:=by
 rcases i with (i|i|i|i)|i|i; exact rfl; exact rfl; exact congrArg (-α * ·) (hp _); exact rfl; exact p _; exact congrArg Neg.neg (u _)
lemma heat_g(i: Along S): heatR T ((shiftZ g M).sent x T q d l β) (U).V s M.key q B W x α i=heatR T M' M.V s M.key q B W x α i:=by
 obtain ⟨v,c',H,Z'⟩:=h.feeds; refine via T x q s α B W M' _ M.V _ M.key (fun i=> park_g T M x q d l β h hm ht hz s g _ B i T.up.loop (fun z=>(H.invariant z).1)) (fun i=>visit_g M s g _ W i _ (fun v=>(Z'.invariant v).1)) ?_ _
 intro i; rw [show (U).V=Lattice.gauge g M.V from rfl,Work.F05.pull_gauge_zero]; exact frame_g ..
include hu hd
lemma park_f(i:Site f)(K':ℕ→RG.Atom SU.group n)(z:∀ i, Prist (K' i)): park ((cedar M).sent x T q d l β) s M.key q B (batch K' r) i=park M' s M.key q B (batch K' r) i:=by rw [echo_s T x q d l β M h hm hz ht hu]; unfold park; rw [Reef.echo_p]; exact tsum_congr fun j=> lushP i _ _ (mint_b _) _ (batch_f _ i j r _ z)
omit h hm hz ht hu hd in
lemma visit_f(i:Site c)(K':ℕ→RG.Atom SU.group n)(z:∀ i, Prist (K' i)): visit (F).V s (F).key W (batch K' r) i=visit M.V s M.key W (batch K' r) i:=by
 unfold visit; change (∑' i',peer_k _ _ _ _ (pull s 0 (Reef.echo _)))= _; rw [Reef.echo_p]; exact tsum_congr fun j=>peerP i _ _ (mint_b _) _ (batch_f _ i j r _ z)
lemma oak_f: oak T x (cedar M) q d l β B W r A= oak T x M q d l β B W r A:=by
 unfold oak; apply congrArg (-β*·); apply congrArg averaged; ext s; refine sum_congr rfl fun i _=>?_
 cases i with
 | inl i=> exact congrArg₂ (·+·) (park_f T M x q d l β h hu hd hm ht hz s _ B i _ (fun v=>(hu v).2.1)) (park_f T M x q d l β h hu hd hm ht hz s _ B i _ (fun v=>(hu v).2.2))
 | inr i=> exact congrArg Neg.neg (congrArg₂ (·+·) (visit_f M s _ W i _ (fun v=>(hd v).2.1)) (visit_f M s _ W i _ (fun v=>(hd v).2.2)))
lemma heat_f(i: Along S): heatR T ((Rink.cedar M).sent x T q d l β) (F).V s M.key q B W x α i=heatR T M' M.V s M.key q B W x α i:=by
 refine via T x q s α B W M' _ M.V _ M.key (fun i=>park_f T M x q d l β h hu hd hm ht hz s _ B i _ (fun v=>(hu v).1)) (fun i=>visit_f M s _ W i _ (fun v=>(hd v).1)) ?_ _
 intro i; rw [show (F).V= Reef.echo M.V from rfl,Reef.echo_p]; exact frame_f ..

end YM.CF.Tye
