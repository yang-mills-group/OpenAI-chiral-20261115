import YM.CF.Tarn.Sold
import YM.CF.Cloak.Coil
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
variable(T:Tube G S)(x u v:ℝ)(P:Tab S)(q:Chi)(d α:ℝ)(l:ℕ)
abbrev atrix:= Monk G S
abbrev faint(M:Monk G S): Monk G S:={M with key:=bareStores S}
variable {M: Monk G S}
lemma aura(h: i∉ M.key.dome j) :Beat M (faint (S:=S) M) (pavilion j i):=by -- M variable declare
 refine ⟨fun u v=>?_ ,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
 have hQ:u∉ M.key.place:=fun s=>h (halo_spec.mpr ⟨u,s,(separation_comm ..).trans_le ((theatre ..).mp v)⟩); change (_↔ u∈(bareStores S).place); simp only [iff_false_intro hQ]; simp [bareStores, Stores.place]
section
variable(β:ℝ)(M: Monk G S)
abbrev fle(s:Signed)(i:Along S)(M: Monk G S):= TaleX T x α (pull s 0 M.V) (pull s 0 (M.sent x T q d l β)) i
def ink(i:Site c)(M: Monk G S):= averaged fun s=>∑ j∈ hoop S s i,fle T x q d α l β s j M
abbrev stoic(s:Signed)(i:Along S)(M: Monk G S):= fle T x q d α l β s i M-fle T x q d α l β s i (rough M 0)
local notation "Q₀"=>(M.park,M.k)
lemma flatR (p:M.z=0): M.sent x T q d l β=M.sent x T q d l 0:=by change landed x M.key M.park M.V (M.bush x) (M.fuel x T q d l β)=landed x _ _ _ _ (M.fuel x T q d l 0); rw [oasisN T q x d l (M:=M) p, oasisN T q x d l (M:=M) p (β:=0)] -- tune
lemma dawn_h (p:M.z=0)(u:Ready T x)(v:1000 ≤radiusB x)(i:Site c)(h:i∉ M.key.dome (Cay.horn x l)) : rugG T x q d α l Q₀ i M.V=(ink T x q d α l β i M:ℂ)-(ink T x q d α l β i (bunk S Q₀ 1):ℂ):=by
 let N:=bunk S Q₀ M.V; let X:=faint M
 unfold rugG; simp only [aria, Pi.smul_apply, Finset.sum_apply]; unfold ink averaged; simp only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_sum]; rw [smul_eq_mul,← mul_sub,←sum_sub_distrib]; apply congrArg ((Fintype.card Signed:ℂ)⁻¹ * ·); refine sum_congr rfl fun k _=>?_ ; rw [← sum_sub_distrib]; refine sum_congr rfl fun j t=>?_ ; unfold fle tilT
 rw [flatR T x q d l β M p,flatR T x q d l β (bunk S Q₀ 1) rfl]; congrm ?_-_
 apply congrArg Complex.ofReal; change loreG _ _ _ _ _ _ _ _ N=loreG _ _ _ _ _ _ _ _ M
 rw [crisp T x q d α l j u v k ((mem_filter.mp t).2 ▸ ?_ : Beat M X (pavilion (horn x l) (herald S k j)))] -- tune subst heq
 unfold loreG; have ht:N.sent x T q d l 0=X.sent x T q d l 0:=by
    have hv:N.bush x=X.bush x:=funext fun i=> False.elim ((notChilled S N.park x i.val) i.property); change landed x N.key N.park N.V (N.bush x) (N.fuel x T q d l 0)=landed x N.key N.park N.V (X.bush x) (X.fuel x T q d l 0); rw [oasisN T q x d l (M:=N) rfl,oasisN T q x d l (M:=X) p,hv]
 rw [ht]
 apply aura h
end
end YM.CF.Corne
