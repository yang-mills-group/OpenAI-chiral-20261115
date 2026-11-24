import YM.CF.Taxi.Mile
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open AnalyticBridge.VerifiedReset Push.Local Next.Foundations
variable (X0: Scree.Hub n)(o:Site (More n)){F:Pane n→ℝ}
local notation "Xp"=> X0.val.2
local notation "Op"=> X0.val.1
local notation "Z"=> villa X0
private lemma troy (R: BudgetPoint) (v: LinearJet SU.group)(X: Finset (Site (More n)))(p:60 < (More n).val): logHessian (∑ j∈X, fuelC X0 F j) (v.field Op) (v.field Op)= (∑ j∈X,motto Op j) * AnalyticBridge.VerifiedReset.quad (fluxP X0 F) v.positive v.positive:=by
 let L:=v.field Op
 induction X using Finset.induction_on with
 | empty => simp only [sum_empty,zero_mul]; exact hessian_zero 0 L L
 | insert i S u ih=>
   let V:= fuelC X0 F i; let K:=∑ j∈S, fuelC X0 F j; let M:= counter (G:=SU.group) (fluxP X0 F) i
   have hk: logHessian V L L=motto Op i* AnalyticBridge.VerifiedReset.quad (fluxP X0 F) v.positive v.positive:=by
      by_cases h:motto Op i=0; · rw [show V=0 from (by unfold V fuelC; rw [h,zero_smul]),h,zero_mul]; exact hessian_zero 0 _ _
      rw [←roseL X0 i p h (fluxP X0 F) v R]; let y:=motto Op i; change iteratedFDeriv ℝ 2 (AnalyticBridge.VerifiedReset.germ V) _ _=y * logHessian M L L; rw [show AnalyticBridge.VerifiedReset.germ V=y • AnalyticBridge.VerifiedReset.germ M from rfl] -- tune f syntactic
      rw [iteratedFDeriv_const_smul_apply (AnalyticBridge.VerifiedReset.germ_diff (counter_regular (G:=SU.group) i _ R))]; rfl
   rw [sum_insert u,sum_insert u,add_mul,←ih, ←hk]; change iteratedFDeriv ℝ 2 (AnalyticBridge.VerifiedReset.germ V + AnalyticBridge.VerifiedReset.germ K) 0 _=_; rw [iteratedFDeriv_add_apply (germ_diff (holdS (P:=R) X0 i)) (germ_diff (rent (P:=R) X0 S))]; rfl
variable(h':BandS P X0 F c)
include h'
lemma zeroQ(p:60< (More n).val)(g:Nonwrapping Z Op) (x y:tangD n)(t:IsAffineDirection Op x)(v:IsAffineDirection Op y): logHessian (F-payout X0 F) x y=0:=by
 let H:= reg_larger h'.regular (show Xp⊆Z from Finset.subset_union_left); let Vt:= payout X0 F; have hp:=h'.regular; let A:=pintK P
 apply affine_zero (reg_sub H (rent (P:=A) X0 _)) Op _ x y t v; intro w; let S:=Thera.yet_one
 rw [hessian_sub H (rent X0 univ),sub_eq_zero]; -- tune.
 rw [troy X0 A w univ p,mot_b,one_mul]; unfold fluxP; simp only [g,↓reduceIte]; rw [show AnalyticBridge.VerifiedReset.quad (AnalyticBridge.VerifiedReset.coeff F Op) w.positive w.positive=logHessian F ((primitive w.positive).field Op) ((primitive w.positive).field Op) from (flux_formula _ S h'.regular ..).symm]; exact LinearJet.hessian_curl S hp (fun x v=>g x (mem_union_left _ v)) (by omega) (positive_primitive _).symm (positive_primitive _).symm
-- echo conjugation antisym of imaginary part.PER X even though F basis.V-out. colour J5 irreducibility.PR.Simple. Ct ETH.(det− allowed theta disappears due standalone C:Charge independent Sym.)
omit h'
open StressFlux Reef
private lemma roseE(u: Skye.Seat n)(c: PlaqAxes)(x:SU.group.Color): Reef.cloak _ ((AnalyticBridge.VerifiedReset.wedge c x).field u)=(AnalyticBridge.VerifiedReset.wedge c (Reef.frolic x)).field u:=by
 funext i; unfold Reef.cloak; simp only [ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,wedge_field]; split_ifs; exact Reef.frolic.map_smul _ _; exact Reef.frolic.map_zero
include h'
lemma pure_e (g:∀ U:Pane n,F (echo U)=-F U)(x y:PlaqAxes): fluxP X0 F x y=0:=by
 unfold fluxP; split
 next hm=>
    let L:=Reef.cloak (Bond (More n)); let A:= pintK P; let c:= AnalyticBridge.VerifiedReset.coeff F Op x y; let f:= AnalyticBridge.VerifiedReset.germ F; let Z':= AnalyticBridge.VerifiedReset.spike SU.group; let w(i:PlaqAxes):=(AnalyticBridge.VerifiedReset.wedge i Z').field Op
    have hv:f ∘ L= - f:=by
       funext i; apply Eq.trans (show f (L i)= F (echo (increment 1 i)) from ?_) (g _)
       change F (increment 1 (L i))=_; apply congrArg; funext j; simp only [RG.increment,Reef.echo,Pi.one_apply,mul_one]; exact cool_a _
    let S:=Thera.yet_one; have hQ:logHessian F (L (w x)) (L (w y))=c:=by
       rw [roseE,roseE,label_color _ S h'.regular]; simp [Reef.frolic.norm_map, AnalyticBridge.VerifiedReset.spike_norm S,Z',c]
    have ht:= h'.regular; have hx:= AnalyticBridge.VerifiedReset.germ_diff ht; have hh:logHessian F (L (w x)) (L (w y))= -logHessian F (w x) (w y):=by
       have he:iteratedFDeriv ℝ 2 (f ∘ L) 0=-(iteratedFDeriv ℝ 2 f 0):=by rw [hv]; exact iteratedFDeriv_neg_apply
       rw [jets_linear L (f:=f) (k:=2) (by exact hx)] at he -- tune ns
       let W:=![w x,w y]
       have hz:=congrArg (fun i:(Directions E' (More n) [×2]→L[ℝ] ℝ)=> i W) he; change (iteratedFDeriv ℝ 2 f 0) (fun i=> L (W i))= -(iteratedFDeriv ℝ 2 f 0 W) at hz; rw [show (fun i:Fin 2=> L (W i))= (![L (w x),L (w y)]:Fin 2→Directions E' (More n)) from funext fun i=> by fin_cases i<;>rfl] at hz; exact hz
    rw [hQ] at hh; change AnalyticBridge.VerifiedReset.coeff F Op x y=0; change c=0; change c = -c at hh; linarith
 rfl
end YM.CF.Taxi
