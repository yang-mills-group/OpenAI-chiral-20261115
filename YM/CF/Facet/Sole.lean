import YM.CF.Facet.Spur
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
variable{T:Pressure.Tube SU.group S}
open Stationary Push.Loops
section
open scoped Matrix.Norms.Frobenius
variable(T:Pressure.Tube G₅ S)(q:Chi)(u x α d:ℝ)(l:ℕ)
-- eliminate loops parts and β apply for extraction. stable difference
abbrev tripK(P:Tab S):FileM c G₅:= rugG T x q d α l P-rugG T x q d 0 l P
lemma kappaY(P:Tab S)(J:ChartRatio G₅)(u r:ℝ): tripK T q x α d l P = Coin T x u q J r d α l P- Coin T x u q J r d 0 l P:=by unfold Tarn.Coin tripK; abel
lemma rock_p(W:Config G₅ c)(i:Site c)(P:Tab S)(h:K.Funds S T) (t:Signed)(b:Site c): tripK T q x α d l (Arena.dial S t b P) i (pull t b W)= tripK T q x α d l P (affine t b i) W:=by
 unfold tripK; simp only [Pi.sub_apply]; rw [rug_o T x q d α l K h,rug_o T x q d 0 l K h]
lemma colt_p(W:Config G₅ c)(i:Site c)(P:Tab S): star (tripK T q x α d l P i W)=tripK T q x α d l P i W:=by
 unfold tripK rugG Arena.aria; simp only [Pi.sub_apply,Pi.smul_apply,Finset.sum_apply, tilT, smul_eq_mul, star_sub,Complex.star_def,Complex.conj_ofReal, map_mul,map_sum,map_sub, map_natCast,map_inv₀] -- tune
lemma turnJ (V:Config G₅ c)(p:PathData G₅)(t:Clip)(x:ℝ)(l r:ℕ)(i: Cell c): Esti.king ∅ p t l r x (Reef.echo V) i= Esti.king ∅ p t l r x V i:=by
 rw [manta,manta]; unfold Vol.sore; rw [faceValue,faceValue,Reef.echo_t,Reef.cold,Reef.swing, Reef.frolic.norm_map]; simp_rw [Char.plotE,Reef.frolic.norm_map]
lemma taleK(V:Config G₅ c)(g:Config G₅ c)(W Y:Config G₅ f)(i:Cay.Along S)(he:g=Reef.echo V):TaleX T x α g W i-TaleX T x 0 g W i=TaleX T x α V Y i-TaleX T x 0 V Y i:=by
 subst g; rcases i with (i|i|i|i)|i|i <;> simp only [TaleX,sub_self,turnJ] -- slots
lemma tale_p (W:Config G₅ c)(P:Tab S)(i:Cay.Along S)(s:Signed):tilT T x q d α l P s i (Reef.echo W)-tilT T x q d 0 l P s i (Reef.echo W)=tilT T x q d α l P s i W-tilT T x q d 0 l P s i W:=by
 let f(a:ℝ)(V:Config G₅ c):ℝ:= loreG T x q d a l s i (bunk S P V)
 let V:=Reef.echo W; have he:f α V-f 0 V= f α W-f 0 W:=taleK T x α (pull s 0 W) (pull s 0 V) (pull s 0 ((bunk S P V).sent x T q d l 0)) (pull s 0 ((bunk S P W).sent x T q d l 0)) i (Reef.echo_p W s 0)
 change ((↑(f α V):ℂ)-↑(f α 1))- ((↑(f 0 V):ℂ)-(↑(f 0 1):ℂ))=((↑(f α W):ℂ)-↑(f α 1))- ((↑(f 0 W):ℂ)-(↑(f 0 1):ℂ)); rw [sub_sub_sub_comm]; conv_rhs=>rw [sub_sub_sub_comm]
 simp_rw [←Complex.ofReal_sub]; rw [he]
lemma spine_t (W:Config G₅ c)(i:Site c)(P:Tab S): tripK T q x α d l P i (Reef.echo W)= tripK T q x α d l P i W:=by
 unfold tripK; simp only [Pi.sub_apply,rugG,Arena.aria,Pi.smul_apply, Finset.sum_apply]; rw [←smul_sub,←smul_sub, ← sum_sub_distrib,← sum_sub_distrib]; apply congrArg; apply Finset.sum_congr rfl; intro s _; rw [←sum_sub_distrib,←sum_sub_distrib]; exact sum_congr rfl fun k _=> tale_p T q x α d l W P k s
end
end YM.CF.Facet
