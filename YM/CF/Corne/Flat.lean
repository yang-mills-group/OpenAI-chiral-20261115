import YM.CF.Corne.Star
import YM.CF.Corne.Item
import YM.CF.Corne.Rug
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Corne
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reine
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r j:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
variable(T:Tube G S)(x u v:ℝ)(P:Tab S)(q:Chi)(d α:ℝ)(l:ℕ)(M: Monk G S)
local notation "a₀"=> M.key
local notation "Q₀"=>(M.park,M.k)
local notation "Z₀"=>rough M 0
-- k₀ flat payments at j>0 only. One lens.
structure Taurus (j:ℕ)(h:Site c):Prop where
 found : Tarn.found (pines G c u) h j M.V
lemma beatY(i:Site c)(ht:Taurus x M j i)(hv:r≤j): Taurus x M r i:=by
 obtain ⟨u₁,v,h,p⟩:=ht.found; exact ⟨u₁,v,h,fun i p'=>p _ (p'.trans hv)⟩
variable(β:ℝ)(J:ChartRatio G)(t:ℝ)
lemma due (p:M.z=0)(hr:Ready T x)(hp:1000 ≤radiusB x)(u:Site c)(ht:u∉M.key.dome (Cay.horn x l)): (dua T x q d l β J t u M:ℂ)-(dua T x q d l β J t u (kist M):ℂ)=MossZ T x q d l J t Q₀ u M.V:=by
 let I:= bunk S Q₀ M.V; let Y:= faint M
 have he(P: Monk G S)(t':P.z=0): (dua T x q d l β J t u P:ℂ)=HWork T x q d l J t P u:=by unfold dua HWork flare; simp_rw [oasisN T q x d l (M:=P) t']
 rw [he M p,he (kist M) rfl]; have hv:=cit_p T x q d l J t u hr hp (Subset.refl _) (aura ht); dsimp only at hv; rw [hv]; unfold MossZ; apply congrArg (·- HWork T x q d l J t (kist M) u); -- term dependent
 unfold HWork
 have hu:Y.bush x= I.bush x:= funext fun i=> False.elim ((notChilled S I.park x i.val) i.property)
 have he':Y.fuel x T q d l 0=I.fuel x T q d l 0:=by rw [oasisN T q x d l (M:=Y) p,oasisN T q x d l (M:=I) rfl,hu]; -- tune let
 apply congrArg Complex.ofReal; exact sum_congr rfl fun i hp=> congrArg (ansC (S:=S) u i.val.val * ·) (congrArg (logGuard q J t ∘ (fun x=>tape x i)) he')
lemma tipC (h:FreshT T x u q J t α σ n l Q₀ C m) (i:Site c)(hx:i∉ M.key.dome ((l+68)*radiusB x))(p:K.Funds S T)(hp:Ready T x)(ht:1000 ≤ radiusB x)(hu:0 < m)(hd:Taurus u M ((l+68)*radiusB x) i): neatQ T x u q d l Q₀ i M.V=(Quill T x q d l M i:ℂ)-(Quill T x q d l (kist M) i:ℂ):=by
 let Y:=pines G c u; let X(v):=bunk S Q₀ v
 obtain ⟨g,v,hv,he⟩:=hd.found; unfold neatQ; rw [land_s (zStamp T x u q d l h.growth p hu hp ht) hv _ he]; obtain ⟨y,t',rfl⟩:=hv; rw [Tarn.lore T x q d l _ _ (h.growth y (mem_ball_zero_iff.mp t')) p hu hp ht g he] -- ambiguous
 have hh:= Quill_r i hp ht (Subset.refl _) (aura hx) (l:=l) (d:=d) (q:=q); dsimp only at hh; unfold zestQ; rw [Complex.ofReal_sub, hh]; let W:=faint M; have hK: Quill T x q d l (X M.V) i=Quill T x q d l W i:=by
    unfold Quill; refine sum_congr rfl fun j _=>?_ ; rw [priceBeds,priceBeds]; refine sum_congr rfl fun z _=>?_ ; unfold pes; rw [show (X M.V).bush x=W.bush x from funext fun i=> False.elim ((notChilled S (X M.V).park x i.val) i.property)]; rfl
 exact congrArg (fun v:ℝ=>(v:ℂ)-((Quill T x q d l (kist M) i):ℂ)) hK -- tune
end YM.CF.Corne
