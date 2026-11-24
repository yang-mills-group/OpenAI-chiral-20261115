import YM.CF.Rink.Noise
import YM.CF.Reine.Whee
import YM.CF.Lich.Way
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
open Reine AnalyticBridge.Annulus1AD
lemma shiftX(s:Signed)(b:Site c)(k:S.Choices)(U:Config G f)(h:S.patch.Branches S.kernel G)(i:Site c)(j:Bond c): let t:=Channels.ticket s b k; let V:=pull s (S.ratio.embed b) U; AnalyticBridge.Annulus1AD.frame t V i=AnalyticBridge.Annulus1AD.frame k U (affine s b i) ∧ AnalyticBridge.Annulus1AD.bond t V j=bond k U (StepData.sendBonds s b j):=by -- adapted Fleet
 let t:=Channels.ticket s b k; let P:=pull s (S.ratio.embed b) U; have hh : S.withinChoice s b t=k:= Equiv.apply_symm_apply .. ; change AnalyticBridge.Annulus1AD.frame t _ _=_ ∧ AnalyticBridge.Annulus1AD.bond t _ _=_
 rw [←hh]; constructor
 · unfold AnalyticBridge.Annulus1AD.frame; change _=S.patch.frameMass _ (expandAt (S.ratio.embed (affine s b i)) U) (S.withinSites s b t.1 (affine s b i)); rw [S.port_site,expandAt_pull,S.port]; exact (S.patch.frames_channel h ..).1
 obtain ⟨j,u⟩:=j; unfold AnalyticBridge.Annulus1AD.bond; change S.patch.predictorMass _ (S.connector _ t.1 (j,u)) (t.2 _) = S.patch.predictorMass _ (S.connector U (S.withinSites s b t.1) _) (S.withinBond s b t.2 (sendEdge s b (j,u))); rw [S.port_bond]; cases hu:s.flip u
 · rw [S.positive h _ _ _ _ _ _ hu]; exact (S.patch.bond_pull (h:=h) ..).1
 rw [S.negative h _ _ _ _ _ _ hu]; exact (S.patch.bond_inv (h:=h) ..).1
lemma lift_g(k:S.Choices)(U:Config G f)(g:Site f→SU.group.El)(h:S.patch.Branches S.kernel G)(i:Site c)(j:Bond c): AnalyticBridge.Annulus1AD.frame k (Lattice.gauge g U) i=AnalyticBridge.Annulus1AD.frame k U i∧ AnalyticBridge.Annulus1AD.bond k (Lattice.gauge g U) j=bond k U j:=by
 unfold AnalyticBridge.Annulus1AD.frame AnalyticBridge.Annulus1AD.bond; rw [expandAt_gauge,S.updateGauged h]; exact ⟨(S.patch.frame_gauged h ..).1,(S.patch.bond_gauge (h:=h) ..).1⟩
lemma lift_f(k:S.Choices)(U:Config G f)(h:S.patch.Branches S.kernel G)(i: Site c)(j:Bond c): AnalyticBridge.Annulus1AD.frame k (Reef.echo U) i=AnalyticBridge.Annulus1AD.frame k U i ∧AnalyticBridge.Annulus1AD.bond k (Reef.echo U) j=bond k U j:=by
 have he(i):expandAt i (Reef.echo U)=Reef.echo (expandAt i U):=rfl
 have hv(i y): S.frames (Reef.echo U) k.1 i y= qG (S.frames U k.1 i y):=congr_fun (sing_p h (expandAt (S.ratio.embed i) U) _).1 y
 have ht:S.connector (Reef.echo U) k.1 j=Reef.echo (S.connector U k.1 j):=by funext i; unfold StepData.connector; simp only [he,Reef.echo_t,hv, Reef.echo,map_mul,map_inv]
 unfold AnalyticBridge.Annulus1AD.frame AnalyticBridge.Annulus1AD.bond; rw [he,ht]; exact ⟨(sing_p h _ _).2,(rhyme h _ _).2⟩
section
variable (T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(s:Signed)(b:Site c)(g:Site c→ SU.group.El)(M:Monk G S)(Z:Stores S)(r:ℕ)(w a:ℝ)
variable (h:K.Funds S T)(p:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hm:0 < m)(hf:120 ≤ radiusB x)
include p hm hf h
lemma moon:(clue S s b M).silver x T a (Locations.book s b Z) q d l β w r=M.silver x T a Z q d l β w r:=by
 let N:=clue S s b M; let O:=Locations.book s b Z; let Y:=N.sent x T q d l β; let F:=M.sent x T q d l β
 have he:Y=pull s (S.ratio.embed b) F:=space_s T x q d l β s b M h p hm hf
 let X:=obv x r 100 O; let X':=obv x r 100 Z; let B:=obv x r 110 O; let B':=obv x r 110 Z
 change cohoT N.key _ _ _ q N.V Y _ X B=cohoT M.key _ _ _ q _ F _ X' B'; rw [he]; let hp:= funds_branch h; unfold cohoT Esti.total; refine congrArg₂ (·*·) (congrArg₂ (·*·) (prod_p (shiftFaces s (S.ratio.embed b)) (nearFace S B) (nearFace S B') (far_f s b Z _) _ _ ?_) (prod_p (StepData.sendBonds s b) _ _ (far_b s b Z ((r+100)*radiusB x)) _ _ fun i _=>wing_t s b M.key F M.V M.k hp q x w a i)) (congrArg₂ (·*·) (prod_p (StepData.sendSites s b) X X' (fun _=>dome_map ..) _ _ ?_) (prod_p (StepData.sendBonds s b) _ _ (far_b s b Z ((r+100)*radiusB x)) _ _ ?_))
 · intro i _; simp only [tokenF,AnalyticBridge.Annulus1AD.profile,rise_b, N,clue,Locations.book, Finset.mem_map_equiv, Equiv.symm_symm] -- tune
 · intro i _; exact if_congr (dome_map ..) (shiftX s b M.k F hp i (i,0)).1 rfl
 intro i _; exact if_congr (on_p s b M.key x i) (shiftX s b M.k F hp i.1 i).2 rfl
lemma mist:(shiftZ g M).silver x T a Z q d l β w r= M.silver x T a Z q d l β w r:=by
 let N:=shiftZ g M; let Y:=N.sent x T q d l β; let F:=M.sent x T q d l β
 change cohoT M.key _ _ _ q N.V Y _ _ _=cohoT M.key _ _ _ q M.V F _ _ _; rw [show Y= _ from gauge_s T x q d l β g M h p hm hf]; let hp:= funds_branch h; unfold cohoT Esti.total; refine congrArg₂ (·*·) (congrArg₂ (·*·) (prod_congr rfl ?_) (prod_congr rfl fun i _=>gear_t M.key F M.V M.k g hp q x w a i)) (congrArg₂ (·*·) (prod_congr rfl ?_) (prod_congr rfl ?_))
 · intro i _; simp only [tokenF,AnalyticBridge.Annulus1AD.profile,toll_gauge]; rfl
 · intro i _; exact if_congr Iff.rfl (lift_g M.k F _ hp i (i,0)).1 rfl
 intro i _; exact if_congr Iff.rfl (lift_g M.k F _ hp i.1 i).2 rfl
lemma ore_f(H: Reef.Rare T.up):(cedar M).silver x T a Z q d l β w r=M.silver x T a Z q d l β w r:=by
 let N:=cedar M; let Y:=N.sent x T q d l β; let F:=M.sent x T q d l β; have he:Y=Reef.echo F:= echo_s T x q d l β M h p hm hf H
 change cohoT M.key _ _ _ q N.V Y _ _ _=cohoT M.key _ _ _ q M.V F _ _ _; rw [he]; let hp:=funds_branch h; unfold cohoT Esti.total; refine congrArg₂ (·*·) (congrArg₂ (·*·) (prod_congr rfl ?_) (prod_congr rfl fun i _=>Rink.echo_t M.key F M.V M.k hp q x w a i)) (congrArg₂ (·*·) (prod_congr rfl ?_) (prod_congr rfl ?_))
 · intro i _; simp only [tokenF,AnalyticBridge.Annulus1AD.profile,mint_b]
 · intro i _; exact if_congr Iff.rfl (lift_f M.k F hp i (i,0)).1 rfl
 intro i _; exact if_congr Iff.rfl (lift_f M.k F hp i.1 i).2 rfl
end
end YM.CF.Rink
