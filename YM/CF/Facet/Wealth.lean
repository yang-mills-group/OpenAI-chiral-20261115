import YM.CF.Facet.Warm
import YM.CF.Facet.Sole
import YM.CF.Facet.North
import YM.CF.Facet.Gust
import YM.CF.Facet.Law
import YM.CF.Facet.Arc
import YM.CF.Facet.Hemp
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
variable{K:Teller G₅}{c f:Side}{S:StepData c f}{A:Finset (Site f)}{o:Site c}{s:Signed}{b:Site c}{x e d β a r σ w:ℝ}{l k:ℕ}
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {F:Tab T}{C V R Z η:ℝ}{Q: Msca m X B G e}{Φ:nomA m X B→ ℂ}{i:Site (More (CSide m B))}
variable{U U':Config G₅ (More (CSide m B))}{t:ℕ}
open Levier
variable{u:ℝ}{q:Chi}{h:0<e}
open Stationary Push.Loops
open Stationary Push.Loops
variable{α:ℝ}{J:ChartRatio G₅}
variable (H:Thu p x u l Q h K k η C a Z V R Φ)
include H
lemma perk (d:ℝ)(q:Chi)(F F':Tab T)(i:Site (More (CSide m B)))(hp:Kind T F F' (pavilion (Cay.horn x l) i)): snowG G p q x u α d l Q h F i=snowG G p q x u α d l Q h F' i:=by
 unfold snowG tripK; simp only [Pi.add_apply,Pi.sub_apply]; rw [show franc p x q d u l Q h F i=_ from rate_pP (F:=F) (F':=F') (q:=q) (d:=d) H i hp,rug_k p x q d α l i F F' hp H.ready H.fine,rug_k p x q d 0 l i F F' hp H.ready H.fine] -- args tune
lemma taleX (q:Chi)(d:ℝ)(α:ℝ)(F:Tab T)(y:Mast G₅ (More (CSide m B)))(hy:‖y‖<1):let L:= crownB T p x Q h l α F.1 F.2
 ∑ i:Site (More (CSide m B)),snowG G p q x u α d l Q h F i (satU G₅ u y) = L (u • y)-L 0:=by
 intro L;
 let g(z:Mast G₅ (More (CSide m B))) := fence Q h (Stores.till x) (Laic.hats F.1 (Souk.flute F.1 (sol T p F.2 x F.1 l) 1 z)); let P:= satU (c:=More (CSide m B)) G₅ u
 let X:= tripK p q x α d l; have hO: ‖(0:Mast G₅ (More (CSide m B)))‖<1:=by simp
 have hz(v:Mast G₅ (More (CSide m B)))(hv:‖v‖<1):∑ i,plain p x q d u l Q h F i (P v)=g (u • v):=by
    simp_rw [show ∀ i,plain p x q d u l Q h F i (P v)= turf G p q x d l Q h F i (P v) from fun i=>song _ _ _ _ _ _ _ h H.funds H.ready (H.tall F) H.pay (H.ears F) H.sizes H.fine (pine_p u _ hv)]
    unfold turf g fence test; rw [Finset.sum_comm]; have he:hornY p q x d l F (P v)=Laic.hats F.1 (Souk.flute F.1 (sol T p F.2 x F.1 l) 1 (u • v)):=by
       rw [wreath p q x d l F v (H.ears F v hv|>.2.2)]; simp only [Souk.flute,one_smul]
    rw [he]; apply Finset.sum_congr rfl; intro i _; rw [←Finset.sum_smul]; obtain ⟨N,hN,hM⟩:=H.pay.members
    by_cases h:N i=0; rw [show Q i=0 from funext fun x=> norm_le_zero_iff.mp ((hN i).sumline _|>.trans_eq h)]; simp
    have ht: i.Nonempty:=by have ht:= (hN i).travel h; cases ht<;> simp
    rw [turtle_k _ ht,one_smul]
 have hp:P 0=1:=by simp [P,satU,facadeX]
 have hx:=hz _ hO; rw [smul_zero, hp] at hx
 unfold snowG franc; simp only [Pi.add_apply,sum_add_distrib,sum_sub_distrib]; change (∑ i,plain _ _ _ _ _ _ _ _ _ _ (P y)) - _ + (∑ i,X F i (P y))= _; rw [show (∑ i,plain p x q d u l Q h F i (P y))=_ from hz y hy,hx]; unfold X tripK; simp only [Pi.sub_apply,sum_sub_distrib]; have hf:= (H.ears F y hy).2.2; have hv:=(H.ears F 0 hO).2.2; rw [rug_s p x q d α l F u y hf hv,rug_s p x q d 0 l F u y hf hv] -- tune
 unfold L crownB draft; dsimp only [g,Hors.cart]; simp only [Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,zero_mul,zero_add]; simp_rw [Complex.real_smul,secondM]; abel
lemma sight(d:ℝ)(q:Chi)(F:Tab T)(z:ℝ)(hg:∀ i:Site (More (CSide m B)), ContDiffAt ℝ (2:ℕ) (satX (snowG G p q x u α d l Q h F i)) 0)(ht:pierce (crownB T p x Q h l α F.1 F.2) z): Prox (snowG G p q x u α d l Q h F) 2 z:=by
 let P':=snowG G p q x u α d l Q h F; let f(y):= crownB T p x Q h l α F.1 F.2 y; let F'(z):=f z-f 0; let L:= chair p F.1
 have p':satX (∑ i,P' i)=ᶠ[𝓝 0] F' ∘ L:=by
    let R:=u⁻¹ • L; filter_upwards [R.continuous.continuousAt.eventually (isOpen_ball.mem_nhds (show R 0∈ ball _ 1 by rw [map_zero]; exact mem_ball_self zero_lt_one))] with i hi; have ht':=(taleX (Q:=Q) H q d α F (R i) (mem_ball_zero_iff.mp hi)); dsimp only at ht'; unfold satU at ht'; rw [show u • R i=L i from smul_inv_smul₀ H.width.ne' _,show facadeX G₅ (L i)=_ from chap p F.1 i] at ht'; change (∑ i,P' i) _ = _; rw [Finset.sum_apply]; exact ht'
 intro i s; let w:=fun k=>(i k,s k); let ζ(l):= flaw G₅ (i l) (s l)
 have hf: ContDiffAt ℝ (2:ℕ) f 0:=ht.1.of_le (by norm_num); have hζ : ContDiffAt ℝ (2:ℕ) F' (L 0):=by rw [map_zero]; exact hf.sub contDiffAt_const
 have hz: (iteratedFDeriv ℝ 2 (satX (∑ i,P' i)) 0 ζ)= Push.Uniform.entry f 0 w:=by
    rw [(p'.iteratedFDeriv ℝ 2).eq_of_nhds,Push.Uniform.iter_lin_at (L:=L) hζ,map_zero]; change (iteratedFDeriv ℝ 2 F' 0) (fun t=>L (ζ t)) = _; rw [show F'=f-(fun _=>f 0) from rfl,iteratedFDeriv_sub_apply hf (show ContDiffAt ℝ (2:ℕ) _ _ from contDiffAt_const),iteratedFDeriv_const_of_ne (by decide:2≠0),Pi.zero_apply,sub_zero]; unfold L ζ; simp_rw [voice_y]; rfl
 rw [sumF _ 2 _ hg]; unfold cake; rw [_root_.smul_apply, show iteratedFDeriv _ _ _ _ _ = _ from hz,norm_smul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_) (ht.2 w); norm_num [Nat.factorial]
end YM.CF.Facet
