import YM.CF.Arena.Sign
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
variable {K:Teller G}
open AnalyticBridge.GaussianFieldAlignment Channels Locations
open PhysicalNext.OrderedAffine2B.SymRows Matrix
-- ALL oriented channels even ord. translation after tag switch verifies.
def stepZ (S:StepData c f)(b:Site c): Equiv.Perm (Dill S):= Equiv.sumCongr (Channels.shift (S.ratio.embed b) PlaqAxes) (Equiv.sumCongr (Channels.shift b Axis) (Equiv.sumCongr (Channels.shift b PlaqAxes) (Channels.shift b Gain)))
lemma dart(V:Config G c)(U:Config G f)(b:Site c)(d:ℕ){k k': S.Choices}(p:S.prediction (Lattice.translate (S.ratio.embed b) U) k'=Lattice.translate b (S.prediction U k))(i:Dill S): Yaught T d (fiery G x S.patch.L) (temp x) (Lattice.translate b V) (Lattice.translate (S.ratio.embed b) U) k' i= Yaught T d (fiery G x S.patch.L) (temp x) V U k (stepZ S b i):=by
 let V':=Lattice.translate b V; let w:= S.ratio.embed b; let U':=Lattice.translate w U; let L:=twin b; let M:=twin w; let A:=Channels.shift b Axis; let B:=Channels.shift b Gain; let K:=RiftN d V' T
 have hn(i): RiftN d V' T i=RiftN d V T (B i):=by
    unfold RiftN Tube.Xn; unfold V'; unfold Pressure.zip Tube.N gk; simp_rw [translated_lane, translated_plot]; exact Equiv.sum_comp (twin b) (fun j=>(T.N d V (B i) j) (T.Xn d V j))
 rcases i with i|i|i|i; all_goals unfold Yaught; simp only [stepZ,Equiv.sumCongr_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr]; simp only [Sum.elim_inl,Sum.elim_inr] -- tune
 · rw [hiatus,hiatus]; apply congrArg₂ (· + ·)
   · unfold KissP; rw [translated_face]
   refine sum_congr rfl fun j _=> ?_
   unfold RiftF; rw [sendsF,Tube.Xf,translated_plot]; rfl
 · rw [iham,iham]; unfold KissI tideX RiftI; rw [p,sendsI, translated_Z]; rfl
 · rw [inka,inka,zpia,zpia]; unfold KissQ; rw [translated_face]; refine congrArg₂ Add.add rfl ?_; refine sum_congr rfl fun j _=>?_
   unfold RiftL RiftD lGap dGap; rw [p]; -- maybe unfolds arguments
   have hug{α β:Type}[Fintype α](h: Equiv.Perm α)(e:Equiv.Perm β)(A A':α→β→Pay SU.group)(p:∀ i j,A' i j=A (h i) (e j))(U V:α→ SU.group.Color)(w:∀ i,U i=V (h i))(i:β): Pressure.unzip A' U i=Pressure.unzip A V (e i):=by unfold unzip; simp_rw [w,p]; exact Equiv.sum_comp h (fun j=>(A j (e i)).adjoint (V j))
   let q:=(i,j); have ht(i:Twin c): T.Xn d V' i=T.Xn d V (L i):= translated_plot ..
   have hα:∀ i j,T.Φ d V' i j=T.Φ d V (M i) (L j):= fun i j=> translated_leap ..; have hβ:∀ i j,T.Φ' d V' i j=T.Φ' d V (A i) (L j):= fun i j=> translated_lane T.R.mn ..; have hγ:∀ i j,T.N d V' i j=T.N d V (B i) (L j):= fun i j=> translated_lane T.R.o .. -- tune
   have ha:= hug M L (T.Φ d V) (T.Φ d V') hα; have hb:= hug A L (T.Φ' d V) (T.Φ' d V') hβ; have hc:= hug B L (T.N d V) (T.N d V') hγ
   rw [ha (T.Xf d U') (T.Xf d U) (fun i=>translated_plot ..),hb (Tube.Z S (Lattice.translate b (S.prediction U k)) V') (Tube.Z S (S.prediction U k) V) (fun i=>translated_Z ..), ha (Pressure.zip _ _) (Pressure.zip _ (T.Xn d V)) (sendsF b V T _), hb (Pressure.zip _ _) (Pressure.zip _ (T.Xn d V)) (sendsI b V T _), hc (Pressure.zip (T.N d V') (T.Xn d V')) (Pressure.zip (T.N d V) (T.Xn d V)) hn, ht]; rfl
 rw [nk,nk, hn]
end YM.CF.Arena
