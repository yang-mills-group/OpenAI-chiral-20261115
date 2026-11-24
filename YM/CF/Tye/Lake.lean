import YM.CF.Tye.Dual
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
lemma rough_s : rough Y₀ 0=clue S s b (rough M 0):=by unfold rough clue; congr 1; exact (map_zero (Tensor.lifting (fiber s b M.V S) (diagram s b S))).symm
lemma rough_g : rough U 0=shiftZ g (rough M 0):=by unfold rough shiftZ; congr 1; exact (map_zero (latticeFieldEstimates S g)).symm
lemma rough_f : rough F 0=Rink.cedar (rough M 0):=by unfold rough Rink.cedar; congr 1; exact (map_zero (Tensor.lifting (Char.shiftF (Bond f)) (Equiv.refl _))).symm
-- ink
include h hm hz ht
lemma fle_s (α:ℝ)(t:Signed)(i:Along S): fle T x q d α l β t i Y₀=fle T x q d α l β (s*t) (lawn S (Channels.offset s b t) i) M:=by
 have hp{N:Side}(i:Site N)(V:Config SU.group N)(A:ℕ→ RG.Atom G 2)(y:Site N): gplot A (Lattice.translate y V) i=gplot A V (i+y):=by refine tsum_congr fun j=>?_ ; unfold RG.Atom.unmasked; simp_rw [Work.F03.atSite_path,translated_face,slot_shift,translated_travel]
 let Z:=Channels.offset s b t; unfold fle; rw [space_s T x q d l β s b M h hm hz ht, show (Y₀).V=_ from rfl]; change TaleX _ _ _ (pull _ _ (pull _ _ _)) _ _= _; rw [channel_turn,channel_turn,Channels.offset_fine]
 rcases i with (i|i|i|i)|i|i
 · rfl
 · rfl
 · refine congrArg (-α * ·) ?_
   show king ∅ T.down T.low (Stores.till x) S.patch.L.val x (Lattice.translate Z (pull (s*t) 0 M.V)) i= king ∅ T.down T.low (Stores.till x) S.patch.L.val x _ (Channels.shift Z PlaqAxes i)
   rw [manta,manta, translated_face]; refine congrArg₂ (·+·) rfl (sum_congr rfl fun i _=>?_); rw [translated_plot]; rfl
 · rfl
 · exact hp i ..
 exact congrArg Neg.neg (hp i ..)
lemma ink_s(α:ℝ)(i:Site c): ink T x q d α l β i Y₀=ink T x q d α l β (affine s b i) M:=by
 apply av_a s; intro t; refine Finset.sum_equiv (lawn S (Channels.offset s b t)) (fun j=>?_) (fun i _=> fle_s T M x q d l β h hm ht hz s b α t i); simp only [Arena.hoop,mem_filter,mem_univ,true_and]; rw [← herZ b t s]; exact (StepData.sendSites s b).injective.eq_iff.symm -- tune
lemma ink_g (α:ℝ)(i:Site c): ink T x q d α l β i U=ink T x q d α l β i M:=by
 unfold ink; apply congrArg averaged; ext t; refine sum_congr rfl fun i _=>?_; obtain ⟨σ,a,H,K⟩:= h.feeds
 have hp{N:Side}(g:Site N→SU.group.El)(y:Site N)(t:ℕ)(Q':ℕ→ RG.Atom G 2)(V:Config G N)(H:∀ i,(Q' i).Invariant): gplot (batch Q' t) (Lattice.gauge g V) y=gplot (batch Q' t) V y:=by
    refine tsum_congr fun i=>?_ ; unfold batch; split
    · unfold RG.Atom.unmasked; simp only [Work.F05.slot_gauge]; exact H i ..
    simp only [dimU]
 unfold fle; rw [gauge_s T x q d l β g M h hm hz ht]; change TaleX _ _ _ (pull t 0 (Lattice.gauge _ _)) _ i= _; rw [Work.F05.pull_gauge_zero,Work.F05.pull_gauge_zero]
 rcases i with (i|i|i|i)|i|i
 · rfl
 · rfl
 · exact congrArg (-α * ·) (keepK c ..)
 · rfl
 · exact hp _ _ _ _ _ (fun i=>(H.invariant i).1)
 exact congrArg Neg.neg (hp _ _ _ _ _ (fun i=>(K.invariant i).1))
omit h hm hz ht in
lemma king_f (V: Config G c)(X:PathData G)(i:Cell c)(r k:ℕ)(P':Clip)(v:ℝ): king ∅ X P' r k v (Reef.echo V) i=king ∅ X P' r k v V i:=by rw [manta,manta]; unfold sore faceValue; rw [Reef.echo_t,swing,cold,frolic.norm_map]; apply congrArg₂ (·+·) rfl; exact sum_congr rfl fun j _=>by rw [Char.plotE,frolic.norm_map]
include hu hd
lemma ink_f(α:ℝ)(i:Site c): ink T x q d α l β i F=ink T x q d α l β i M:=by
 unfold ink; apply congrArg averaged; ext t; refine sum_congr rfl fun i _=>?_
 have hp{N:Side}(g:ℕ)(v:ℕ→RG.Atom G 2)(x:Site N)(y: Config G N)(p:∀ i, Reef.Prist (v i)): gplot (batch v g) (echo y) x=gplot (batch v g) y x:=by
    refine tsum_congr fun i=>?_; unfold batch; split
    · unfold RG.Atom.unmasked; simp_rw [Reef.tollSlot]; exact p i _
    simp only [dimU]
 unfold fle; rw [echo_s T x q d l β M h hm hz ht hu]; change TaleX _ _ _ (pull _ _ (Reef.echo _)) _ i= _; rw [Reef.echo_p, Reef.echo_p]
 rcases i with (i|i|i|i)|i|i; exact rfl; exact rfl; exact congrArg (-α * ·) (king_f ..); exact rfl; exact hp _ _ _ _ (fun i=>(hu i).1); exact congrArg Neg.neg (hp _ _ _ _ (fun i=>(hd i).1))
include p hg hx
lemma zen_f (α:ℝ)(i:Site c): zenA T x q d α l F β R v i= zenA T x q d α l M β R v i:=by
 unfold zenA; rw [rough_f, ink_f T M x q d l β h hu hd hm ht hz, ink_f T (rough M 0) x q d l β h hu hd hm ht hz,kite_f T M x q d l β h hu hm ht hz R v p hg hx,kite_f T (rough M 0) x q d l β h hu hm ht hz R v p hg hx]; rfl
omit hu hd
lemma zen_s(α:ℝ)(i:Site c): zenA T x q d α l Y₀ β R v i= zenA T x q d α l M β R v (affine s b i):=by
 unfold zenA; rw [rough_s,ink_s T M x q d l β h hm ht hz,ink_s T (rough M 0) x q d l β h hm ht hz,kite_s T M x q d l β h hm ht hz R v p hg hx,kite_s T (rough M 0) x q d l β h hm ht hz R v p hg hx,curve_l _ _ _ _ _ _ _ _ _ _ h p,curve_l _ _ _ _ _ _ _ _ _ _ h p]
lemma zen_g (α:ℝ)(i:Site c): zenA T x q d α l U β R v i=zenA T x q d α l M β R v i:=by unfold zenA; rw [rough_g, ink_g T M x q d l β h hm ht hz g, ink_g T (rough M 0) x q d l β h hm ht hz,kite_g T M x q d l β h hm ht hz R v p hg hx,kite_g T (rough M 0) x q d l β h hm ht hz R v p hg hx]; rfl
end YM.CF.Tye
