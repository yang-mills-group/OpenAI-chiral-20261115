import YM.CF.DPress.Motto.Frame
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Larch Ione Taxi Bake Salt LinearT
namespace Arco
variable {n:Side}{X:Scree.Hub n}{L:ℕ}(T:BudgetPoint){a h b:ℝ}(t:1≤h)
variable {E G:RegBudget n}
local notation "Δ"=> (E-G)
-- real-linearity for licensed sorted frame. no holo.
abbrev αV(K:RegBudget n):= caw T L (cry_H K) -- use local notation
local notation "α" E:max=> (αV (L:=L) T E)
lemma wageS : (α (E-G))=(α E)-(α G) :=by
 funext X; unfold αV caw; rw [Pi.sub_apply]; split; next t=> exact funext fun i=> LinearT.wageSub _ _ _
 next h=> exact (sub_zero _).symm
lemma realS(X:Scree.Hub n) : Taxi.realH (α Δ) X= Taxi.realH (α E) X-Taxi.realH (α G) X:=by
 rw [wageS]; funext i; exact (show (Complex.reCLM.comp (pot (n:=n) ∅)) ((α E) X i- (α G) X i) = _ from map_sub ..)
private lemma hollowS(a b:ℂ): hollow (n:=Dwell n) (a-b)= hollow a-hollow b:=Subtype.ext (sub_smul a b (1:FC (Dwell n)))
lemma porchS(X:Scree.Hub n) : porch (α Δ) X= porch (α E) X-porch (α G) X:=by rw [wageS]; funext i; unfold Taxi.porch; rw [show lifeH (((α E)-(α G)) X) 1= lifeH ((α E) X) 1-lifeH ((α G) X) 1 from ?_]; apply hollowS; exact map_sub (Beau.pot ∅) _ _ -- tune placeholders
variable (e:IncX Utrue E T h a) (g:IncX Utrue G T h b)
include t
lemma τa(X:Scree.Hub n) (e:IncX Utrue E T h a) : (pintK T).Regular X.val.2 (Taxi.realH (α E) X):=by
 obtain ⟨y,w,-⟩:= (Beau.price_Q T _ e).2.weight; have vℚ:= cashR (X0:=X) _ (w X) (zero_le_one.trans t) Complex.reCLM ‖Complex.reCLM‖ le_rfl; unfold Taxi.realH αV caw; split; exact vℚ.regular; exact reg_const 0 -- tune instance
include e g
lemma fluxS(X:Scree.Hub n)(a b:PlaqAxes): fluxP X (Taxi.realH (α Δ) X) a b= fluxP X (Taxi.realH (α E) X) a b-fluxP X (Taxi.realH (α G) X) a b:=by
 rw [realS]; unfold fluxP; split; exact hessian_sub (τa (L:=L) T t X e) (τa (L:=L) T t X g) _ _; simp
lemma guess : aora T L Δ=aora T L E-aora T L G:=by
 unfold aora lureC payoutF; rw [←sum_sub_distrib]; exact sum_congr rfl fun i _=>by rw [←mul_sub,←fluxS T t e g]
lemma fundQ(X:Scree.Hub n)(u:WagesC.Point n)(i:Pane n): Taxi.fuelC X (Taxi.realH (α Δ) X) u i=Taxi.fuelC X (Taxi.realH (α E) X) u i- Taxi.fuelC X (Taxi.realH (α G) X) u i:=by
 unfold Taxi.fuelC counter AnalyticBridge.VerifiedReset.quad; simp_rw [Pi.smul_apply,fluxS T t e g,sub_mul,sum_sub_distrib,sub_div,smul_sub]
lemma bankS(X:Scree.Hub n): mowR (α Δ) X=mowR (α E) X-mowR (α G) X:=by
 have he: bankT (α Δ) X= bankT (α E) X-bankT (α G) X:=by
    funext i; unfold bankT payout; simp_rw [Finset.sum_apply,(fundQ (L:=L) T t e g X),sum_sub_distrib,Complex.ofReal_sub,Pi.sub_apply]; exact hollowS ..
 unfold mowR; rw [he,porchS,wageS,Pi.sub_apply]; abel
lemma guru : Coil (α Δ)=Coil (α E)-Coil (α G):=by
 funext i; unfold Beau.Coil sunY; simp_rw [bankS T t e g,sum_sub_distrib]; rfl
lemma Ξfilm (x:Aura n)(D:Support (More n))(y:Scree.Hub n): pamE (α Δ) y x D=pamE (α E) y x D-pamE (α G) y x D:=by
 unfold pamE chasmR; by_cases h:x=pur (stateT y); swap; · rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne h,Pi.single_eq_of_ne h]; exact (sub_zero _).symm
 have hp(i:WagesC.Point n):say_t (α Δ) y D i= say_t (α E) y D i-say_t (α G) y D i:=by
    unfold say_t; split; exact (sub_zero _).symm; exact funext fun p=> by unfold oV page; rw [fundQ T t e g,map_sub]; rfl -- tune Pi.congru
 rw [h,Pi.single_eq_same,Pi.single_eq_same,Pi.single_eq_same]; unfold peelR; simp_rw [hp,sum_sub_distrib, porchS, wageS (E:=E) (G:=G),Pi.sub_apply]; rw [show ∀ f g:InkD n,flick (pur y) (oV (f-g)) D=flick (pur y) (oV f) D-flick (pur y) (oV g) D from (fun u v=>by unfold Vow.flick; split; rfl; simp),show ∀ f g:InkD n,oV (f-g)= oV f- oV g from (fun _ _=>rfl)]; abel -- rw order flick unfreeze
lemma voidS : voids (α Δ)=voids (α E)-voids (α G):=by unfold Beau.voids; funext i d; simp_rw [Pi.sub_apply,Finset.sum_apply,Ξfilm T t e g,sum_sub_distrib]
variable(R:PathData SU.group)(p:Clip)(Q:Ids n)
-- Act.exact linear since poolζ parameter scales.Promo.No thresholds beyond wizard needed.
omit e g t
lemma duoS(v w:ℝ): lite_b n T R p (v-w)=lite_b n T R p v - lite_b n T R p w∧lit_P n T R p (v-w)=lit_P n T R p v-lit_P n T R p w:=by
 constructor; · funext i U; simp only [Pi.sub_apply]; rw [(bothC T R p (v-w) i U).1,(bothC T R p v i U).1,(bothC T R p w i U).1,sub_smul] -- tune focus tactic
 funext i U; simp only [Pi.sub_apply]; rw [(bothC T R p (v-w) i U).2,(bothC T R p v i U).2,(bothC T R p w i U).2,sub_smul]
lemma θQ(v w:ℝ): ΘK Q T R p (v-w)=ΘK Q T R p v-ΘK Q T R p w:=by funext i D U; simp only [Pi.sub_apply]; rw [pique_z T R Q p (v-w),pique_z T R Q p v,pique_z T R Q p w,sub_smul]
lemma headS : head_L Δ=head_L E-head_L G:=by funext i V; change cut_V _ = _; exact map_sub cut_V _ _
lemma canS : can_V T L (cry_H Δ)=can_V T L (cry_H E)-can_V T L (cry_H G):=by funext i; unfold can_V; rw [Pi.sub_apply]; split; exact (sub_zero _).symm; exact funext fun j=> LinearT.wageSub 0 _ _
include e g t
lemma brolS : brol T R p L Δ= brol T R p L E-brol T R p L G:=by
 unfold brol; dsimp only; rw [canS,guess T t e g,guru T t e g,(duoS T R p _ _).1,(duoS T R p _ _).2, ←add_sub_add_comm,←add_sub_add_comm,LinearT.write, headS]; abel
lemma truceS : truce T R p L Δ Q=truce T R p L E Q-truce T R p L G Q:=by rw [truce,guess T t e g, θQ,voidS T t e g, sub_sub_sub_comm,LinearT.writes] -- orientation
end Arco
end YM.CF.Py.Kay
