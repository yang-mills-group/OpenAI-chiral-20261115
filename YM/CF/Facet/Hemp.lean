import YM.CF.Facet.Horn
import YM.CF.Cour.Culm
import YM.CF.Tarn.Sold
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Facet
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff  InnerProductSpace
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
local notation "G₅"=> SU.group
open Cube Lat Rush Cour Scroll Laic Kennel Paige Spire Branch Broc Pec
variable {n B m X: Side}{T: Roam m X B}{G: Ratio (CSide m B) (CSide X B)}{p:Tube G₅ T}
variable{K:Teller G₅}{c f:Side}{S:StepData c f}{A:Finset (Site f)}{o:Site c}{s:Signed}{b:Site c}{x e d β a r σ v w:ℝ}{l k:ℕ}
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
abbrev mount (g:Ratio c f)(A: Finset (Site f)): Support c:= A.image g.parent
def turtle (g:Ratio c f)(A:Finset (Site f))(o: Site c):ℝ:= if o∈mount g A then ((mount g A).card:ℝ)⁻¹ else 0
lemma turtle_k(g:Ratio c f) {A:Support f}(p:A.Nonempty):∑ i,turtle g A i=1:=by
 have he:0< (mount g A).card:=card_pos.mpr (Nonempty.image p _)
 unfold turtle; rw [←Finset.sum_filter]; simp only [sum_const,nsmul_eq_mul]; rw [filter_mem_eq_inter,univ_inter,mul_inv_cancel₀ (by positivity)] -- Nonempty.image ambiguity
lemma turtle_u(g:Ratio c f) : |turtle g A o|≤1:=by
 unfold turtle; split
 next v=> have hp: 1 ≤ ((mount g A).card:ℝ):= Nat.one_le_cast.mpr (card_pos.mpr ⟨_,v⟩); exact (abs_of_nonneg (by positivity)).trans_le (inv_le_one_of_one_le₀ hp)
 simp
lemma thigh(g:Ratio c f)(hp:Grove (Tenant.terr _) A)(hz:o∈ mount g A)(p:Site f)(t:p∈A):separation o (g.parent p) ≤ A.card+1:=by
 obtain ⟨y,u,rfl⟩:= mem_image.mp hz; have ht:= hp.lim _ u _ t; have hf:(separation (g.parent y) (g.parent p):ℝ) ≤ separation y p + 1:=by
    apply (Font.hleft (g:=g) _ _).trans; gcongr; exact div_le_self (Nat.cast_nonneg _) (show 1 ≤ _ from Nat.one_le_cast.mpr g.count.property)
 apply le_trans (b:=separation y p+1); exact_mod_cast hf; exact Nat.add_le_add_right ht.le _
abbrev Rose (m X B:Side):=Seal (Site (More (CSide X B))) -- no conflict
abbrev mSeal(X B:Side):=Seal (Site (More (CSide X B)))
variable{I: Set (Config SU.group c)}
section
variable(T:Tube SU.group S)(X:Finset (Site f))
end
variable(G) (p:Tube G₅ T)(q:Chi)(x d:ℝ)(l:ℕ)(h:T.ratio=ratio G)
def test (Q: Msca m X B G e)(j:mSeal X B)(ρ:0<e)(F:Tab T)(U:Config G₅ (More (CSide m B))):ℂ:= Q j (pear G ρ (hornY p q x d l F U))
def turf (Q:Msca m X B G e)(ρ:0<e)(F: Tab T)(i:Site (More (CSide m B)))(V: Config G₅ (More (CSide m B))):ℂ:= ∑ j∈ univ.filter (fun j:mSeal X B=> j.card ≤ Stores.till x), turtle (ratio G) j i • test G p q x d l Q j ρ F V
variable {i:Site (More (CSide m B))}{b Y A Z C:ℝ}{F F':Tab T}{j:mSeal X B}
-- in saturated-neighborhood extensions.
include h
lemma stitch (Q:Msca m X B G e)(T':mSeal X B)(V W:Config G₅ (More (CSide m B)))(t:0<e)(v:(hornY p q x d l F V)∈Rent0 G e)(w:(hornY p q x d l F' W)∈Rent0 G e)(r:ℝ)(H:Ready p x)(ht:1000 ≤radiusB x)(hj:T'.card≤ Stores.till x)(hb:Kind T F F' (pavilion (Cay.horn x l) i))(hp:drift G₅ i (Cay.horn x l) V W) (hx: Broc.Peak (dressL G e) T' (Q T') r):
 turtle (ratio G) T' i • test G p q x d l Q T' t F V=turtle (ratio G) T' i • test G p q x d l Q T' t F' W:=by
 unfold test; rw [pear_even G t v,pear_even G t w]; by_cases z:r=0; · apply congrArg ( (turtle (ratio G) T' i) • ·); simp only [show Q T'=0 from funext fun i=> norm_le_zero_iff.mp ((hx.sumline _).trans_eq z)]; rfl
 by_cases g:i∈mount (ratio G) T'; swap; simp only [turtle,if_neg g,zero_smul]
 let U:= (⟨_,v⟩:Rent0 G e); let R:= (⟨_,w⟩:Rent0 G e); let X:= pavilion (Cay.horn x l) i; have hk(y:Site _)(hy:y∈T'): separation i (T.ratio.parent y) ≤ radiusB x+1:=by rw [h]; apply (thigh (ratio G) (hx.travel z) g y hy).trans; exact Nat.add_le_add_right (hj.trans (Nat.div_le_self _ _)) _
 apply congrArg ( (turtle (ratio G) T' i) • ·); apply hx.reads U R
 let X':=bunk T F V; let Y':=bunk T F' W; have hX:Beat X' Y' X:= ⟨fun _ _=>Iff.rfl,hb.site,fun i hu=> hb.edge i (hu (mem_insert_self ..)), KinT hb,fun i p _=>hp _ ((theatre ..).mp p),fun _ _=>rfl,fun _ _=>rfl⟩
 constructor <;> intro e a b
 · refine hX.backF H ht _ ?_; exact aroundBk X (Subset.refl _) (by have hv:= hk _ a; unfold Cay.horn; simp_rw [Nat.add_mul]; omega) -- tune
 apply hp; have hv:=hk _ (mem_filter.mp a).2; rw [h,Ratio.embed_parent] at hv; unfold Cay.horn; simp_rw [Nat.add_mul]; omega
lemma threads (Q:Msca m X B G e)(t:0<e)(a b c ze X':ℝ) (W:nomA m X B→ℂ)(H:Tally Q W a b c X' k)(U V:Config G₅ (More (CSide m B)))(v:(hornY p q x d l F U) ∈ Rent0 G e)(w:hornY p q x d l F' V∈ Rent0 G e)(t':Ready p x)(hv:1000≤ radiusB x)(hp: Kind T F F' (pavilion (Cay.horn x l) i))(hx:drift G₅ i (Cay.horn x l) U V) : turf G p q x d l Q t F i U=turf G p q x d l Q t F' i V:=by
 obtain ⟨N,H,K⟩:=H.members; unfold turf; exact sum_congr rfl fun i q=>stitch G _ _ _ _ _ h Q i _ _ _ v w _ t' hv (mem_filter.mp q|>.2) hp hx (H i).toPeak
end YM.CF.Facet
