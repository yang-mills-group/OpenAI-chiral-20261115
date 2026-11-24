import YM.CF.Arena.Nano
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Matrix
open Channels Locations
variable {K:Teller G}
lemma shine_T (s:Signed)(b:Site c)(M: Monk SU.group S)(h:K.Funds S T)(hv:M.z=0): let P:=clue S s b M; P.sent x T q d l β=pull s (S.ratio.embed b) (M.sent x T q d l β):=by
 intro P; let F:=calendar x M.key M.park s b; let O:=fiber s b M.V S; let f:= P.fuel x T q d l β; have hp:P.z=0:=by unfold P clue; simp only [hv,map_zero] -- ambiguity bind Pi
 have ht:f= Orthogonal.move (onBond O) F.onKey (M.fuel x T q d l β):=by
    obtain ⟨u,w,hT,Q⟩:=h.feeds; rw [←h.high] at hT; unfold f; rw [oasisN _ _ _ _ _ hp,oasisN _ _ _ _ _ hv,show P.bush x=_ from gen x S s b M]
    exact boxL (Char.turned T M.key M.park x M.V M.k q d (M.bush x) s b hT (funds_branch h)) (fun e=>green_map ..) (funds_branch h) hT -- tune
 change landed x P.key P.park P.V (P.bush x) f=_; rw [ht]; exact spike ..
def lawn (S:StepData c f)(b:Site c): Equiv.Perm (Along S):= Equiv.sumCongr (stepZ S b) (Equiv.sumCongr (Equiv.addRight (S.ratio.embed b)) (Equiv.addRight b))
lemma bloom(s u:Signed)(b:Site c)(V:Config G c)(U:Config G f)(k:S.Choices)(i:Along S)(h:K.Funds S T): let z:= pull s b V; let y:=pull s (S.ratio.embed b) U; ballot T x (pull u 0 z) (pull u 0 y) (choice u (Channels.ticket s b k)) i=ballot T x (pull (s*u) 0 V) (pull (s*u) 0 U) (choice (s*u) k) (lawn S (Channels.offset s b u) i):=by
 intro z y; let W:=s*u; let Z:=Channels.offset s b u; have hQ{c:Side}(V:Config G c)(p:PathData G)(i:Site c)(v:Site c)(r:ℕ): turF p r (Lattice.translate v V) i=turF p r V (i+v):=by
    have he{k:ℕ}(A:ℕ→ RG.Atom G k): gplot A (Lattice.translate v V) i=gplot A V (i+v):=by
       refine tsum_congr fun j=>?_ ; unfold Atom.unmasked; simp_rw [Work.F03.atSite_path,translated_face,slot_shift,translated_travel]
    exact congrArg₂ (·+·) (he ..) (he ..)
 have hv:pull u 0 z= Lattice.translate Z (pull W 0 V):= Channels.channel_turn ..; have hw:pull u 0 y=Lattice.translate (S.ratio.embed Z) (pull W 0 U):=by unfold y; rw [Channels.channel_turn,offset_fine]
 rw [hv,hw]; rcases i with i|i|i
 · apply dart _ _ Z _ ?_ i; rw [← hw,(carry u (funds_branch h) (Channels.ticket s b k) y).2, (carry W (funds_branch h) k U).2]; unfold y; rw [S.prediction_channel (funds_branch h)]; unfold Channels.ticket; rw [Equiv.apply_symm_apply,Channels.channel_turn]
 · apply hQ .. -- tune
 exact congrArg Neg.neg (hQ ..)
lemma clown(s:Signed)(b:Site c)(h:K.Funds S T)(V:Config G c)(k:Tab S)(u:Signed)(i:Along S): bale T (dial S s b k) q x d l u i (pull s b V)= bale T k q x d l (s*u) (lawn S (Channels.offset s b u) i) V:=by
 let M:=bunk S k V; let P:=clue S s b M; have hQ:P=bunk S (dial S s b k) (pull s b V):=by
    have ht:P.U=1:=by unfold P clue pull; funext k; simp only [Step.read]; split; change (1:SU.group.El)⁻¹ =1; simp; rfl
    have hv:P.key=bareStores S:=by change book s b (bareStores S)= _; simp [Locations.book,bareStores]
    have hz:P.z=0:=map_zero _; refine (show P={P with U:=1,z:=0,key:=bareStores S} from ?_)
    conv_lhs=> rw [show P= ⟨P.key,P.park,P.k,P.V,P.U,P.z⟩ from rfl]; skip
    rw [show ({ P with U:=1,z:=0,key:=bareStores S} : Monk G S)=⟨bareStores S,P.park,P.k,P.V,1,0⟩ from rfl, hv,hz,ht]
 let Z:= Channels.offset s b u; rw [show bale T (dial S s b k) q x d l u i (pull s b V)=(stars T x P q d l 0 u i:ℂ) from (congrArg (fun p:Monk G S=>(stars T x p q d l 0 u i:ℂ)) hQ.symm)]; change _=(stars T x M q d l 0 (s*u) _ :ℂ); rw [bluff _ _ _ _ _ _ _ (map_zero _),bluff _ _ _ _ _ _ _ rfl,show P.sent x T q d l 0= _ from shine_T s b M h rfl]; exact congrArg Complex.ofReal (bloom s u b V (M.sent x T q d l 0) k.2 i h)
end YM.CF.Arena
