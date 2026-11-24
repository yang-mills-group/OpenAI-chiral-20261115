import YM.CF.Tarn.Loops
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
variable(q:Chi)(d α:ℝ)(l:ℕ)
lemma gaZ (K:Teller G)(p:K.Funds S T)(P:Tab S)(g:Site c→SU.group.El)(V:Config G c):(bunk S P (Lattice.gauge g V)).sent x T q d l 0=Lattice.gauge (constantGauge g S.ratio) ((bunk S P V).sent x T q d l 0):=by
 let M:=bunk S P V; let R:=shiftZ g M; let Q:=bunk S P (Lattice.gauge g V); have hz: R.fuel x T q d l 0=Pogo g M x (M.fuel x T q d l 0):=by rw [oasisN T q x d l (M:=R) (show R.z=0 from map_zero (Cay.latticeFieldEstimates S g)), oasisN T q x d l (M:=M) rfl,brag g M q x d p l] -- tune
 have hQ: R.bush x= Q.bush x:=funext fun i=> False.elim ((notChilled S M.park x i.val) i.property)
 have hR: R.sent x T q d l 0 = Q.sent x T q d l 0:=by change landed x M.key M.park Q.V (R.bush x) (R.fuel x T q d l 0)=landed x M.key M.park Q.V (Q.bush x) (Q.fuel x T q d l 0); rw [oasisN T q x d l (M:=R) (show R.z=0 from map_zero (Cay.latticeFieldEstimates S g)),oasisN T q x d l (M:=Q) rfl,hQ]
 have ha: Q.sent x T q d l 0=Lattice.gauge (constantGauge g S.ratio) (M.sent x T q d l 0):= hR.symm.trans (Eq.trans (show R.sent x T q d l 0=landed x M.key M.park (Lattice.gauge g M.V) (AnalyticBridge.GaussianFieldAlignment.Gauges.gaugeY g x M.key M.park (M.bush x)) (Pogo g M x (M.fuel x T q d l 0)) from congrArg (landed x M.key M.park (Lattice.gauge g M.V) (AnalyticBridge.GaussianFieldAlignment.Gauges.gaugeY g x M.key M.park (M.bush x))) hz) (audU g M x _ _))
 exact ha
abbrev tilT (P:Tab S)(s:Signed)(i:Along S)(V:Config G c):ℂ:= loreG T x q d α l s i (bunk S P V)-loreG T x q d α l s i (bunk S P 1) -- subtract re coercion carefully
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal Gauges PhysicalNext.OrderedAffine2B.SymRows Channels
lemma keepK(c:Side)(R:PathData G)(V:Config G c)(g:Site c→SU.group.El)(r b:ℕ)(x:ℝ)(P:Clip)(i:Cell c): king ∅ R P r b x (Lattice.gauge g V) i=king ∅ R P r b x V i:=by rw [manta,manta,face_gauge]; unfold sore; simp_rw [SU.group.price_conj,SU.group.curvature_conjugate,SU.group.norm_adjoint]; refine congrArg₂ (·+·) rfl (sum_congr rfl fun j _=>?_); rw [plotted_turn,SU.group.norm_adjoint]
lemma til_g (p:K.Funds S T)(P:Tab S)(s:Signed)(i:Along S)(hr:Ready T x)(hp:1000 ≤radiusB x):Rel.Atom (tilT T x q d α l P s i) (herald S s i) (horn x l):=by
 constructor
 · intro V g; obtain ⟨σ,a,H,K⟩:=p.feeds; have hh: loreG T x q d α l s i (bunk S P (Lattice.gauge g V))=loreG T x q d α l s i (bunk S P V):=by
      have hp{n:Side}(g:Site n→SU.group.El)(y:Site n)(t:ℕ)(Q:ℕ→ RG.Atom G 2)(V:Config G n)(H:∀ i,(Q i).Invariant): gplot (batch Q t) (Lattice.gauge g V) y=gplot (batch Q t) V y:=by
         refine tsum_congr fun i=>?_ ; unfold batch; split
         · unfold RG.Atom.unmasked; simp only [Work.F05.slot_gauge]; exact H i ..
         simp only [dimU]
      unfold loreG; rw [gaZ T x q d l _ p]; change TaleX _ _ _ (pull s 0 (Lattice.gauge g V)) _ i= _; rw [Work.F05.pull_gauge_zero, Work.F05.pull_gauge_zero]
      rcases i with (i |i|i|i)|i|i
      · rfl
      · rfl
      · exact congrArg (-α * ·) (keepK c ..)
      · rfl
      · exact hp _ _ _ _ _ (fun i=>(H.invariant i).1)
      exact congrArg Neg.neg (hp _ _ _ _ _ (fun i=>(K.invariant i).1))
   unfold tilT; rw [hh]
 intro V W h; unfold tilT; let u:Rel.SpaceX G c:=tilT T x q d α l P s i; have hu:loreG T x q d α l s i (bunk S P V)=loreG T x q d α l s i (bunk S P W):= crisp T x q d α l i hr hp s ⟨fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun i t _=>h i ((theatre ..).mp t),fun _ _=>rfl,fun _ _=>rfl⟩; rw [hu]
lemma til_tr (s t:Signed)(b:Site c)(P:Tab S)(i:Along S)(V:Config G c)(h:K.Funds S T): tilT T x q d α l (dial S s b P) t i (pull s b V)=tilT T x q d α l P (s*t) (lawn S (Channels.offset s b t) i) V:=by
 have he(V:Config G c): loreG T x q d α l t i (bunk S (dial S s b P) (pull s b V))=loreG T x q d α l (s*t) (lawn S (Channels.offset s b t) i) (bunk S P V):=by
    let g(V:Config G c):=bunk S P V; let U:= (g V).sent x T q d l 0; let Z:=Channels.offset s b t
    have hp{n:Side}(i:Site n)(V:Config G n)(A:ℕ→ RG.Atom G 2)(y:Site n): gplot A (Lattice.translate y V) i=gplot A V (i+y):=by
       refine tsum_congr fun j=>?_ ; unfold RG.Atom.unmasked; simp_rw [Work.F03.atSite_path,translated_face,slot_shift,translated_travel]
    have hv:= Channels.channel_turn (V:=V) s b t -- tune
    have hu:pull t 0 (pull s (S.ratio.embed b) U)= Lattice.translate (S.ratio.embed Z) (pull (s*t) 0 U):=by rw [Channels.channel_turn,offset_fine]
    unfold loreG; rw [←bench, shine_T s b (g V) h rfl,hu]; change TaleX _ _ _ (pull _ _ (pull _ _ _)) _ _= _; rw [hv]
    rcases i with (i|i|i|i)|i|i
    · rfl
    · rfl
    · refine congrArg (-α * ·) ?_
      show king ∅ T.down T.low (Stores.till x) S.patch.L.val x (Lattice.translate Z (pull (s*t) 0 V)) i= king ∅ T.down T.low (Stores.till x) S.patch.L.val x _ (Channels.shift Z PlaqAxes i)
      rw [manta,manta, translated_face]; refine congrArg₂ (·+·) rfl (sum_congr rfl fun i _=>?_); rw [translated_plot]; rfl
    · rfl
    · exact hp i ..
    exact congrArg Neg.neg (hp i ..)
 have hp:=he (1:Config G c); rw [coldPull V] at hp; unfold tilT; rw [he,hp]
end
end YM.CF.Tarn
