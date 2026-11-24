import GaugeFieldConstruction.Popins
set_option autoImplicit false
set_option maxHeartbeats 48000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
local notation "oX"=> Θk n x
open Phys
abbrev Tagφ:= GaugeFieldConstruction.Cauchy.Spin × SU.Slot
def fisc (b:Bool)(i:Tagφ): Hove.Kt:= (GaugeFieldConstruction.Cauchy.band b i.1,i.2)
def primeF (i:Tagφ):= YM.GaugeFieldConstruction.Wick.Yacht.debtF i.1 i.2
-- only chiral bins. map Pal to ordered Spair
abbrev wedgeCR (i j:Tagφ):= Cauchy.times' (primeF i) (primeF j)
def goldΦ : Pal →ₗ[ℂ] Cauchy.J Spair where
 toFun X:=∑ i:Tagφ,∑ j:Tagφ, X (fisc false i) (fisc true j) • wedgeCR i j
 map_add' a b:=by simp only [Matrix.add_apply,add_smul, Finset.sum_add_distrib]
 map_smul' z a:=by simp only [Matrix.smul_apply,Finset.smul_sum,smul_smul,RingHom.id_apply]; rfl
lemma gold_f (i j:Tagφ)(h:ℂ): goldΦ (flare_one (fisc false i) (fisc true j) h)= h • wedgeCR i j:=by
 have hx(b:Bool):Injective (fisc b):= fun _ _ e=> Prod.ext (bandη b (congrArg Prod.fst e)) (by have h:=congrArg Prod.snd e; exact h)
 change ∑ a:Tagφ,∑ b:Tagφ, Matrix.single (fisc false i) (fisc true j) h (fisc false a) (fisc true b) • wedgeCR a b=_
 simp_rw [Matrix.single_apply, (hx false).eq_iff,(hx true).eq_iff,ite_smul,zero_smul]; simp [ite_and,Finset.sum_ite_irrel]
-- joint moments
variable (P:Op (Single n))(H0:Dialat x P)(h)
abbrev Skor (i j: ArcK x):ℂ:= (h:ℂ)^2*(Γpay n x i j* P (AngleP n x false i) (AngleP n x true j))
abbrev KnotΛ (i j: ArcK x):= κviews (Θk n x) (wrap n i.1.val) (wrap n j.1.val)
include H0 w
-- scalar sum weighted with markJet.Z. combinator r practice
abbrev zery (i j:ArcK x):Ole Views Pal:= mastF (Θk n x) P h (AngleP n x false i, AngleP n x true j)
lemma circum (j:PalOne→ₗ[ℝ]Pal)(f:ArcK x→ArcK x→ℂ)(p:∀ i k,j (zery h x P i k)=flare_one (fisc false i.2) (fisc true k.2) (f i k)):∑ i:ArcK x,∑ k:ArcK x,f i k • wedgeCR i.2 k.2= goldΦ (j (markJet (Θk n x) P h)):=by
 rw [Spale x w P H0,map_sum,map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_sum,map_sum]; exact sum_congr rfl (fun k _=>by rw [p i k,gold_f])
-- may drop n binder
abbrev eyeX(u:Views): PalOne→ₗ[ℝ]Pal:=LinearMap.comp (ContinuousLinearMap.apply ℝ Pal u).toLinearMap (LinearMap.comp (LinearMap.fst ℝ (OneF Views Pal) (Duo Views Pal)) (LinearMap.snd ℝ Pal (OneF Views Pal × Duo Views Pal)))
def eyeY(u v:Views): PalOne→ₗ[ℝ]Pal:= by
 refine { toFun:=fun a=> a.2.2.val u v,map_add':=fun _ _=> rfl,map_smul':=fun _ _=>rfl}
lemma Ph0: ∑ i:ArcK x, ∑ j:ArcK x, Skor h x P i j • wedgeCR i.2 j.2= goldΦ (markJet (Θk n x) P h).1:=by
 refine circum h x w P H0 (LinearMap.fst ℝ _ _) (Skor h x P) ?_; intro i k
 change flare_one _ _ ((bookP _ _).1)= _; rw [fund0]; rw [← show hill_Z (Θk n x) P h (AngleP n x false i) (AngleP n x true k)=Skor h x P i k from pricesP x w P h i k]; rfl
lemma Ph1 (u:Views): ∑ i:ArcK x, ∑ j:ArcK x, ((Complex.I*↑(KnotΛ (n:=n) x i j u))*Skor h x P i j) • wedgeCR i.2 j.2= goldΦ ((markJet (Θk n x) P h).2.1 u):=by
 let f(i j:ArcK x):=(Complex.I*↑(KnotΛ (n:=n) x i j u))*Skor h x P i j
 refine circum h x w P H0 (eyeX u) f ?_; intro i k; change flare_one _ _ ((bookP _ _).2.1 u)= _; rw [fund1]; unfold f; rw [← show hill_Z (Θk n x) P h (AngleP n x false i) (AngleP n x true k)= Skor h x P i k from pricesP x w P h i k]; rfl
lemma Ph2 (u v: Views): ∑ i:ArcK x,∑ j:ArcK x, ((Complex.I*↑(KnotΛ (n:=n) x i j u))*(Complex.I*↑(KnotΛ (n:=n) x i j v))*Skor h x P i j) • wedgeCR i.2 j.2 = goldΦ ((markJet (Θk n x) P h).2.2.val u v):=by
 let f(i j:ArcK x):=(Complex.I*↑(KnotΛ (n:=n) x i j u))*(Complex.I*↑(KnotΛ (n:=n) x i j v))*Skor h x P i j
 refine circum h x w P H0 (eyeY u v) f ?_; intro i k; change flare_one _ _ ((bookP _ _).2.2.val u v)= _; rw [fund2]; unfold f; rw [← show hill_Z (Θk n x) P h (AngleP n x false i) (AngleP n x true k)= Skor h x P i k from pricesP x w P h i k]; rfl
end YM.CF.XGarden.MastTin.ArtCart
end
