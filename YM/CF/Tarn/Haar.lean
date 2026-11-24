import YM.Primitives.HAAR_LOG_JETS.Guard
import YM.CF.Tarn.Inky
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
section
variable (T:Tube G S)(x:ℝ)
variable(q:Chi)(d:ℝ)(l:ℕ)(R:ChartRatio G)(t:ℝ)
open AnalyticBridge.GaussianFieldAlignment Orthogonal Gauges Locations PhysicalNext.OrderedAffine2B.SymRows Tensor Channels Primitives.HaarLogJets.Guard
abbrev ansC{S:StepData c f}(i:Site c)(z:Bond f):ℝ:= if i∈grove S z then ((grove S z).card:ℝ)⁻¹ else 0 -- include S def
abbrev HWork (M:Monk G S)(i:Site c):ℂ:= ((∑ z:M.zoo x, ansC (S:=S) i z.val.val*logGuard q R t (tape (M.fuel x T q d l 0) z):ℝ):ℂ)
def MossZ(P:Tab S):FileM c G:=fun o v=>HWork T x q d l R t (bunk S P v) o-HWork T x q d l R t (bunk S P 1) o
variable (hp:0<t)(h:R.radius>4*t)(hx:LocalRatio R)(hv:K.Funds S T)
include hp h hx hv
lemma flash (g:Site c→SU.group.El)(P:Tab S)(i:Site c)(V:Config G c): MossZ T x q d l R t P i (Lattice.gauge g V)=MossZ T x q d l R t P i V:=by
 unfold MossZ HWork; let M:=bunk S P V; let N:=bunk S P (Lattice.gauge g V); have hv: N.fuel x T q d l 0=Pogo g M x (M.fuel x T q d l 0):=by
    let W:= shiftZ g M; have hh:W.bush x=N.bush x:=funext fun i=>False.elim ((notChilled S M.park x i.val) i.property); have ht:= brag g M q x d hv l; rw [hh] at ht; rw [oasisN T q x d l (M:=M) rfl, oasisN T q x d l (M:=N) rfl]; exact ht
 change ((∑ z:N.zoo x, ansC (S:=S) _ _*logGuard q R t (tape (N.fuel x T q d l 0) z):ℝ):ℂ)-_=_ -- tune implicit
 -- proof avoid congr
 refine congrArg₂ (·-·) (congrArg Complex.ofReal ?_) rfl; refine Finset.sum_congr rfl fun i hp'=>?_ ; apply congrArg (ansC (S:=S) _ _ * ·); rw [hv,Slate.Pogo, move_tape]; exact log_extended_turn _ false q hp hx h _ -- tune redex
lemma halo_p (s:Signed)(b o:Site c)(P:Tab S)(V:Config G c): MossZ T x q d l R t (dial S s b P) o (pull s b V)= MossZ T x q d l R t P (affine s b o) V:=by
 have he(V): HWork T x q d l R t (bunk S (dial S s b P) (pull s b V)) o= HWork T x q d l R t (bunk S P V) (affine s b o):=by
    let M:=bunk S P V; let N:=clue S s b M; let Q:=calendar x M.key M.park s b; let A:=fiber s b M.V S; rw [← bench]; apply congrArg Complex.ofReal; change (∑ i:N.zoo x,_)= _; rw [← Equiv.sum_comp Q.onKey]; let Y:= tape (M.fuel x T q d l 0); refine Finset.sum_congr rfl fun i _=>?_ ; have ht: N.fuel x T q d l 0= Orthogonal.move (onBond A) Q.onKey (M.fuel x T q d l 0):=by -- copy
       obtain ⟨u,w,hT,Q'⟩:=hv.feeds; rw [←hv.high] at hT; rw [oasisN _ _ _ _ _ (M:=N) (show N.z=0 from map_zero _),oasisN _ _ _ _ _ (M:=M) rfl,show N.bush x=_ from gen x S s b M]; exact boxL (Char.turned T M.key M.park x M.V M.k q d (M.bush x) s b hT (funds_branch hv)) (fun e=>green_map ..) (funds_branch hv) hT
    refine congrArg₂ (·*·) (prime_o (s:=s) (b:=b) (j:=0) x M (fun _=>i) o) ?_
    have hu:tape (N.fuel x T q d l 0) i=A i.val.val (Y (Q.onKey i)):= by rw [ht]; exact move_tape (onBond A) Q.onKey (M.fuel x T q d l 0) i -- tune
    change logGuard q R t (tape (N.fuel x T q d l 0) i) = logGuard q R t (Y (Q.onKey i)); rw [hu]; let v:= i.val.val; let y:= Y (Q.onKey i); let W:=replica S.ratio M.V; change logGuard q R t (Channels.scatter s (S.ratio.embed b) W v y)=logGuard q R t y; unfold Channels.scatter; split
    next he=> exact log_extended_turn _ true q hp hx h _ -- tune
    rfl
 have hz:=he (1:Config G c); rw [coldPull V] at hz; unfold MossZ; rw [he,hz]
end
end YM.CF.Tarn
