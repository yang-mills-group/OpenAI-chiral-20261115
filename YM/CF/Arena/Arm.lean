import YM.CF.Arena.Sigh
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
section
variable(T:Tube G S)(P:Tab S)(q:Chi)(x d:ℝ)(l:ℕ)(s:Signed)(V:Config G c)
abbrev bunk(S:StepData c f)(P:Tab S)(V:Config G c): Monk G S:=⟨bareStores S,P.1,P.2,V,1,0⟩
def bale (i:Along S)(V:Config G c):ℂ:= dense T x q d l 0 s i (bunk S P V) -- contains 0 since β arbitrary. use compare
lemma oasisN {M:Monk G S}(h:M.z=0): M.fuel x T q d l β= liftN T x M.V M.k M.key M.park q d (M.bush x) l:=by
 unfold Monk.fuel realP spinC; change _= _; have ht:M.bell x=0:=funext fun i=> by change M.z i.val.val=_; rw [h]; rfl
 rw [ht,show tape.symm (0: LogArray G (Active M.key x M.park))=(0:Prices G (Active M.key x M.park)) from (Push.Uniform.tint G _).symm.map_zero]; simp only [Matrix.mulVec_zero,smul_zero,add_zero]
lemma bluff(T:Tube G S)(N:Monk G S)(s:Signed)(h:N.z=0): stars T x N q d l β s= ballot T x (pull s 0 N.V) (pull s 0 (N.sent x T q d l β)) (choice s N.k) :=by
 unfold stars ballot; apply congrArg₂ Sum.elim _ rfl; unfold Slate.payer; rw [oasisN _ _ _ _ _ h]; simp only [sub_self]; suffices he:Gloss S s (fun _=>0)=0 by rw [he,sub_zero]
 funext i; rcases i with i|i|i; simp [Gloss]; rfl; exact rfl
-- gauge
lemma baleG {K:Teller G}(p:K.Funds S T)(i:Along S): GaugeInvariant (bale T P q x d l s i):=by
 intro g V; let M:=bunk S P V; let R:=shiftZ g M; let Q:=bunk S P (Lattice.gauge g V); have hz: R.fuel x T q d l 0=Pogo g M x (M.fuel x T q d l 0):=by rw [oasisN T q x d l (M:=R) (show R.z=0 from map_zero (Cay.latticeFieldEstimates S g)), oasisN T q x d l (M:=M) rfl,brag g M q x d p l] -- tune
 have hQ: R.bush x= Q.bush x:=funext fun i=> False.elim ((notChilled S M.park x i.val) i.property)
 have hR: R.sent x T q d l 0 = Q.sent x T q d l 0:=by change landed x M.key M.park Q.V (R.bush x) (R.fuel x T q d l 0)=landed x M.key M.park Q.V (Q.bush x) (Q.fuel x T q d l 0); rw [oasisN T q x d l (M:=R) (show R.z=0 from map_zero (Cay.latticeFieldEstimates S g)),oasisN T q x d l (M:=Q) rfl,hQ]
 have ha: Q.sent x T q d l 0=Lattice.gauge (constantGauge g S.ratio) (M.sent x T q d l 0):= hR.symm.trans (Eq.trans (show R.sent x T q d l 0=landed x M.key M.park (Lattice.gauge g M.V) (AnalyticBridge.GaussianFieldAlignment.Gauges.gaugeY g x M.key M.park (M.bush x)) (Pogo g M x (M.fuel x T q d l 0)) from congrArg (landed x M.key M.park (Lattice.gauge g M.V) (AnalyticBridge.GaussianFieldAlignment.Gauges.gaugeY g x M.key M.park (M.bush x))) hz) (audU g M x _ _))
 change (stars _ _ Q _ _ _ _ _ i:ℂ)= (stars _ _ M _ _ _ _ _ i:ℂ); obtain ⟨v,z,P,R⟩:= p.feeds; rw [bluff _ _ _ _ _ _ _ rfl, bluff _ _ _ _ _ _ _ rfl, ha, vega (T:=T) g p, show Q.V = Lattice.gauge g M.V from rfl, Work.F05.pull_gauge_zero M.V]; unfold ballot; rw [show Q.k= M.k from rfl]; let g':=AnalyticBridge.GaussianFieldAlignment.Gauges.turned g s; let G':=constantGauge g' S.ratio; let A:=pull s 0 M.V; let B:=pull s 0 (M.sent x T q d l 0); have ht:turF T.up (Stores.till x) (Lattice.gauge G' B)=turF T.up (Stores.till x) B:=funext fun i=> turP P i _ _ _; have hs':turF T.down (Hors.cart x S.patch.L) (Lattice.gauge g' A)= turF T.down (Hors.cart x S.patch.L) A:= funext fun i=> turP R i _ _ _
 exact congrArg (fun x:Along S→ℝ=>(x i:ℂ)) (congr_arg₂ (fun (a:Dill S→ℝ)(b:Site f⊕Site c→ℝ)=>Sum.elim a b) (rgba A B (choice s M.k) g' p (Stores.till x) x) (show _=_ from congr_arg₂ (fun a (b:Site c→ℝ)=>Sum.elim (α:=Site f) a (-b)) ht hs'))
end
end YM.CF.Arena
