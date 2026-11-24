import YM.CF.Lilt.Rail
import YM.CF.Muse.Bill
import YM.CF.Jade.Pond
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
variable{r:ℕ}
local instance textK_P0 :MeasurableSpace (Finset (Sat S)):= ⊤
local instance textK_P1 :MeasurableSingletonClass (Finset (Sat S)):=⟨fun _=>trivial⟩
local instance textK_P2 :MeasurableSpace (List (Hos S r)):= ⊤
local instance textK_P3 :MeasurableSingletonClass (List (Hos S r)):=⟨fun _=>trivial⟩
local instance textK_P4 :Finite ↥(Sil S r):=Set.Finite.to_subtype sill_p
local notation "Sν"=> (Sil S r)
local notation "ΦT"=> (tale S k t)
local notation "dP"=> Directions SU.group (Domain P B)
open Girt Plume
open Lilt Feu Nor
variable(F₁:Support (Domain N B))(u ρ:ℝ)(h:0 < ρ)(hu:0 ≤ u)
abbrev text_r(S:StepData (Domain N B) (Domain P B)) (F:Support (Domain N B))(u v:ℝ):Set ↥(Robe S v):= {p|¬ Lilt.textP F p.val u}
local notation "pQ"=> ↥(Robe S ρ)
local notation "М₃"=> tour (S:=S) ρ
local notation "Gp"=> plummy S ρ
local notation "XQ"=> text_r S F₁ u ρ
lemma textR_m: MeasurableSet (text_r S F₁ u ρ):=measurable_subtype_coe ((Lilt.burns_m (S:=S) F₁ u).compl) -- maybe preimage exact
variable (C:Sil S r→ℝ)
local notation "XC"=> ({v:dP|¬∀ i:Bond (Domain P B),S.ratio.parent i.1 ∈ F₁→‖v i‖≤ u})
local notation "Dμ"=> (tableG SU.group (Bond (Domain P B)) ρ)
include h
-- independence
lemma text_y : (∫ i in XQ, C (era i.val.2.2)∂М₃) = (М₃).real XQ*(∫ A:Ids (mid P B),C (era A)∂depot (mid P B)):=by
 let U:= text_r S F₁ u ρ; let A': Set (dP):= XC; let Q(x:↥(Robe S ρ)):= (x.val.2.1.2,x.val.2.2); let f(x:dP):ℝ:=Set.indicator A' (fun _=>1) x; let P':= depot (mid P B); let X(t:dP× Ids (mid P B)):= f t.1 * C (era t.2); have H: Q ⁻¹' (Prod.fst ⁻¹' A')=U:=rfl
 let Z:= (loral (S:=S) h).comp (rock_m h); have hx:MeasurableSet A':=by
    let F:=univ.filter fun i:Bond (Domain P B)=> S.ratio.parent i.1∈F₁
    rw [show A'=⋃ i:F,{v:dP|‖v i.val‖ > u} from (by ext v; unfold A'; simp [F])]; exact MeasurableSet.iUnion fun i=> measurableSet_lt measurable_const ((measurable_pi_apply i.val).norm) -- tune
 haveI:IsProbabilityMeasure М₃:=tour_p h; haveI:IsProbabilityMeasure Dμ:=how _ h; have hx':=measurePreserving_fst (μ:=Dμ) (ν:=depot (mid P B)); have hf:Integrable f Dμ:= (integrable_const _).indicator hx; have hp:Integrable (fun x:Ids (mid P B)=>C (era x)) P':=frill _ (sill_m (S:=S) (r:=r)) C _
 have hu: (∫ x,f x ∂Dμ)=(М₃).real XQ:=by
    rw [←show (∫ x:↥(Robe S ρ), f (Q x).1 ∂М₃)= _ from (Girt.hinge _ _ (hx'.comp Z) hf).symm]; rw [show (fun x:↥(Robe S ρ)=> f (Q x).1)=U.indicator (fun _=> (1:ℝ)) from ?_, integral_indicator (textR_m ..)] -- tune
    · simp [U]
    funext x; unfold f Set.indicator; split_ifs with g t y; any_goals rfl
    exact False.elim (t (H ▸ g)); exact False.elim (g (show x∈Q ⁻¹' (Prod.fst ⁻¹' A') from H.symm ▸ y))
 have he:Integrable X (Measure.prod Dμ P'):=by exact hf.mul_prod hp -- tune name
 rw [←MeasureTheory.integral_indicator (textR_m ..), ←show (fun p:pQ=> X (Q p))=U.indicator (fun i=> C (era (S:=S) i.val.2.2)) from ?_, show (∫ p:pQ,X (Q p)∂М₃)= _ from (Girt.hinge _ _ Z he).symm,←hu, MeasureTheory.integral_prod X he]; simp only [X,integral_const_mul]; rw [MeasureTheory.integral_mul_const] -- tune
 funext x; unfold X f Set.indicator; split_ifs with g t y; · simp [Q]
 exact False.elim (t (H ▸ g)); exact False.elim (g (show x∈Q ⁻¹' (Prod.fst ⁻¹' A') from H.symm ▸ y)); rw [zero_mul]
variable {a C₀:ℝ}(htZ:1 ≤ ρ) (p:0<a)(ps: let F(x:SU.group.Color):= Real.exp (a*‖x‖^2); Integrable F (Appel.feast SU.group ρ) ∧ (∫ i,F i∂Appel.feast SU.group ρ) ≤ C₀)
omit h
include p htZ ps hu
abbrev tentX (a u C:ℝ)(S:StepData (Domain N B) (Domain P B))(k:ℕ):= Real.exp (-a*u^2) *(((k+k+1)^4 :ℕ)* (S.patch.L.val^4:ℕ)* (Fintype.card Axis:ℕ)* C)
lemma tire_p : ((М₃).real XQ) ≤ (coverNumber (radiusB x) F₁:ℝ)*tentX a u C₀ S (radiusB x):=by
 have h:= zero_lt_one.trans_le htZ; haveI:=tour_p (S:=S) h; let A:=coverNumber (radiusB x) F₁; have hx:= Lilt.tail_q (S:=S) htZ p ps u F₁ hu; have hc:0 ≤ C₀:= (integral_nonneg (μ:=Appel.feast SU.group ρ) (fun x:SU.group.Color=>(Real.exp_pos (a*‖x‖^2)).le)).trans ps.2 -- tune
 rw [show (М₃).real XQ=(∫ x:pQ,(if textP F₁ x.val u then (0:ℝ) else 1) ∂М₃) from ?_]; swap; · rw [show (fun x:pQ=> if textP F₁ x.val u then (0:ℝ) else 1)=(XQ).indicator (fun _=> (1:ℝ)) from funext fun x=>by unfold Set.indicator text_r; simp [ite_not], integral_indicator (textR_m ..)]; simp -- tune
 apply (le_trans (phraseT h (fun i:Cord S=>if textP F₁ i u then (0:ℝ) else 1) |>.trans_le hx.2)); have hh:= creek_w (S:=S) (x:=x) F₁ u le_rfl; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hh) hc) (Real.exp_pos _).le); unfold tentX; push_cast; exact le_of_eq (by ring)
end YM.CF.Jade
