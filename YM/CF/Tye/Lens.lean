import YM.CF.Tye.Lake
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
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
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
open Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare
local notation "X"=>kist M
variable (j:ℕ)
lemma kist_s : kist Y₀=clue S s b X:=by unfold kist; rw [bench,coldPull M.V]; rfl
-- per path.Pric tilt REAL.
include h q
lemma tit_s (i:Site c): tit T x (clue S s b M) i j= tit T x M (affine s b i) j:=by
 obtain ⟨σ,b',H,Z⟩:=h.feeds; rw [←h.high] at H; let V:= Equiv.arrowCongr (Equiv.refl (Fin (j+2))) (Q s b).onKey; unfold tit; rw [← Equiv.sum_comp V]; refine sum_congr rfl fun v _=> congrArg₂ (·*·) (prime_o _ _ v i) (congrArg (-(1/2:ℝ)*·) (letter_edge (Char.turned T M.key M.park x M.V M.k q 0 (M.bush x) s b H (funds_branch h)) v)) -- need Chi Nonempty or q
include hu hm ht hz
lemma pes_f (i: Run (M.zoo x) (j+1)) : pes T x q d l (cedar M) i=pes T x q d l M i:=by
 obtain ⟨σ,a,H,A⟩:=h.feeds; rw [←h.high] at H; have he:=storyE T M.key M.park x M.V M.k q d (M.bush x) (funds_branch h) H hu; obtain ⟨hQ,hT⟩:=letterZ he hm ht hz (fun _=>Iff.rfl) l (funds_branch h) H i; exact congrArg₂ (·+·) (congrArg₂ (·+·) (congrArg (-(1/2:ℝ)*·) (letter_edge he i)) (congrArg ((1/2:ℝ)*·) hQ)) hT
lemma beds_f(i:Site c): beds T x q d l (cedar M) j i=beds T x q d l M j i:=by rw [priceBeds, priceBeds]; exact sum_congr rfl fun w _=>congrArg (plant S i (stave w)*·) (pes_f T M x q d l h hu hm ht hz j w)
lemma quill_f(i:Site c): Quill T x q d l (cedar M) i=Quill T x q d l M i:= sum_congr rfl fun j _=>beds_f T M x q d l h hu hm ht hz j i
lemma qerr_f(i:Site c): qerr T x q d l F i=qerr T x q d l M i:=congrArg₂ (·-·) (quill_f T M x q d l h hu hm ht hz i) rfl
omit hu
lemma qerr_g(i: Site c): qerr T x q d l U i=qerr T x q d l M i:= congrArg₂ (·-·) (Tarn.groundX g T x q d l M h hm hz ht i) rfl
lemma beds_s(i:Site c): beds T x q d l Y₀ j i=beds T x q d l M j (affine s b i):=by
 rw [priceBeds, priceBeds]; let B':=Equiv.arrowCongr (Equiv.refl (Fin (j+2))) (Q s b).onKey; rw [← Equiv.sum_comp B']; exact sum_congr rfl fun w _=>congrArg₂ (·*·) (prime_o _ _ w _) (Tarn.vita T x q d l M h s b hm hz ht w)
variable (hh: FreeResolvent.Gap (baseX T x (kist M).key M.park M.k 1) m)
include hh
lemma qerr_s (i:Site c): qerr T x q d l Y₀ i=qerr T x q d l M (affine s b i):=by unfold qerr; rw [turnQuill T x q d l M h s b hm hz ht,kist_s,turnQuill T x q d l X h s b hh hz ht] -- kist_s before rewrite
omit hm
lemma art_s (i:Site c): artU T x q d l Y₀ i=artU T x q d l M (affine s b i):=by unfold artU porry; rw [kist_s,turnQuill T x q d l X h s b hh hz ht]; exact congrArg₂ (·-·) rfl (sum_congr rfl fun j _=>tit_s T X x q h s b j i)
end YM.CF.Tye
