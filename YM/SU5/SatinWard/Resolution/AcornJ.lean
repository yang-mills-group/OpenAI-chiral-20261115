import YM.SU5.SatinWard.Resolution.Inning
import YM.SU5.SatinWard.Resolution.Timpani

/-!
# Character frames (physics-specific Sweep reps)
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

open ResolutionFrame
variable (F:ResolutionFrame ι) (C K A:ℝ) (L: Side)
local notation "cι"=> (Fintype.card ι:ℝ)
local notation "ε1" => Real.exp (1:ℝ)
namespace ResolutionFrame
open SoulField
local notation "Ι"=>Wage3
local notation "CΙ"=> Coords Ι
local notation "r✥"=>Real.exp (-1) / 8
local notation "ε1"=> Real.exp (1:ℝ) -- duplicate notation hygiene
abbrev Talent:= CΙ→ₗ[ℝ] CΙ
abbrev CoinSong:= CΙ→L[ℝ] CΙ
abbrev ζL(L:Side) := ((L.val:ℝ)⁻¹)^3
abbrev floorL(L:Side):= headFine*ζL L
abbrev roofL(L:Side):=4*Real.exp 1*ζL L
lemma ζL_pos(L:Side) :0<ζL L:=by unfold ζL; positivity
lemma floorL_pos(L:Side):0<floorL L:= mul_pos headPos (ζL_pos L)
lemma roofL_pos(L:Side):0<roofL L:= by unfold roofL; exact mul_pos (by positivity) (ζL_pos L)
noncomputable abbrev meterTiny:ℝ:=(1/10000)*surgeBudget⁻¹*surgeBudget⁻¹
lemma tiny_p:0< meterTiny:=by unfold meterTiny; have ht:=lt_of_lt_of_le zero_lt_one surge_herald; positivity
lemma tiny_w:10000*meterTiny ≤1:=by
 have ht:0< surgeBudget⁻¹:= inv_pos.mpr (zero_lt_one.trans_le surge_herald); let a:= surgeBudget⁻¹
 have hv:a*a≤1:= mul_le_one₀ (inv_le_one_of_one_le₀ surge_herald) ht.le (inv_le_one_of_one_le₀ surge_herald)
 unfold meterTiny; linarith only [hv] -- reducible a
lemma tiny_m:meterTiny*surgeBudget*surgeBudget= 1/10000:=by
 have ht:=lt_of_lt_of_le zero_lt_one surge_herald; unfold meterTiny; field_simp
noncomputable abbrev markCount:ℝ:=(Fintype.card Wage3)
lemma count_pos_J :0< markCount:=by unfold markCount; exact_mod_cast Fintype.card_pos
noncomputable abbrev stepTiny:= meterTiny/(8*markCount)
lemma stepTiny_pos:0<stepTiny:=div_pos tiny_p (mul_pos (by norm_num) count_pos_J)
lemma step_b:8*markCount*stepTiny=meterTiny:= mul_div_cancel₀ _ (mul_pos (by norm_num) count_pos_J).ne'
lemma pulse_round (k:Axis) :Fintype.card (Fin (finrank ℝ chiralModule)) = Fintype.card Wage3:=rfl -- remove
-- spirit+ requirement can be asked with green bill before prep
local notation "U★" t:max=> (spinFrame t)
lemma tinyAppointment (H A B:ℝ)(k:Axis)(x:1≤ H)(y:1≤A)(z:1≤ B) :∀ᶠ n:ℕ in atTop,∀ L:Side,n≤L.val→ (U★ k).pulseHidden L H A B ≤ stepTiny:=by
 let X:=receiptCost; let D:=accuracy H A B; let t:=stepTiny; let w:=X*D/t
 filter_upwards [(tendsto_natCast_atTop_atTop («R»:=ℝ)).eventually_ge_atTop w] with n u L l
 let Y:ℝ:= L.val; have hp:1≤ Y:=by unfold Y; exact_mod_cast L.property
 have hK:0<X:=receipt_pos; have hD:0<D:=accuracy_pos H A B x y z; have hT:0<t:=stepTiny_pos
 have he:w≤Y:=(show w≤ (n:ℝ) from u).trans (by unfold Y; exact_mod_cast l); apply le_trans (b:=X*D/Y^2)
 · unfold pulseHidden; rw [pulse_power]; change X*Y^3 * (D*Y⁻¹^5)≤_; exact Eq.le (by field_simp)
 apply (div_le_iff₀ (by positivity)).2; refine (mul_le_mul_of_nonneg_right  he hT.le).trans' ?_ |>.trans ?_ -- tune
 change _≤(X*D/t)*t; rw [div_mul_cancel₀ _ hT.ne']
 change Y*t ≤ t*Y^2; nlinarith only [mul_le_mul_of_nonneg_left hp (show 0≤t*Y by positivity)]

abbrev Adjacent(X: Talent)(c:ℝ):Prop:= ∀ i, ‖X i-i‖≤ c*‖i‖
namespace Adjacent
variable {X Y: Talent}{a b:ℝ}
lemma pay (h:Adjacent X a) (i:CΙ): ‖X i‖ ≤ (1+a)*‖i‖:=by have ht:= (norm_sub_norm_le (X i) i).trans (h i); linarith
lemma raises (p:Adjacent X a)(q:a≤b):Adjacent X b:=fun i=> (p i).trans (mul_le_mul_of_nonneg_right q (norm_nonneg i))
lemma compose (p:Adjacent X a)(q:Adjacent Y b)(u:b≤1)(h:0≤a) : Adjacent (X.comp Y) (2*a+b):=by
 intro i; change ‖X (Y i)-i‖ ≤ _; have ht: ‖Y i‖≤2*‖i‖:=(q.raises u|>.pay i).trans_eq (by norm_num)
 rw [show X (Y i)-i=X (Y i)-Y i+(Y i-i) by abel]; exact (norm_add_le ..).trans ((add_le_add ((p _).trans (mul_le_mul_of_nonneg_left ht h)) (q _)).trans_eq (by ring))
-- θ both budgets
end Adjacent
section Fields
variable {Q Q':CΙ≃ₗ[ℝ]CΙ}
def Filer (Q:CΙ≃ₗ[ℝ]CΙ):Prop:= ∀ i:Wage3, ‖Q (ShapeLab.leg i)-ShapeLab.leg i‖≤ stepTiny
namespace Filer
lemma sits (p:Filer Q): Adjacent Q.toLinearMap meterTiny:=by
 have hx:= step_b; intro i; let t:=Q.toLinearMap-LinearMap.id; have hh(k:Ι): ‖t (leg k)‖≤ stepTiny:= p k; exact (columns_le_of_tips t i _ hh).trans (mul_le_mul_of_nonneg_right (by change markCount*_≤_; linarith only [hx,tiny_p]) (norm_nonneg i))
lemma fits (p:Filer Q)(t:∀ i,‖Q.symm i‖≤ 2* ‖i‖):Adjacent Q.symm.toLinearMap (2*meterTiny):=by
 intro i; rw [norm_sub_rev]; have h:= ((sits p) (Q.symm i)); rw [show Q.toLinearMap (Q.symm i) = i from Q.apply_symm_apply i] at h -- tune
 exact h.trans ((mul_le_mul_of_nonneg_left (t _) tiny_p.le).trans_eq (by ring)) -- cyclic norm order currently ‖i-Q⁻¹i‖ not ‖Q⁻¹i-i‖
end Filer
variable {L r₂:Side}{A C H κ q Q₁:ℝ}{X Y:BudgetPoint}{η:Type}[Fintype η][DecidableEq η]{t:Axis}
variable {R:Reflow Wage3 (Wage3⊕η)}
local notation "δ"=> κ * ζL L *(q/Q₁)
lemma gamma_house (i:Wage3): (U★ t).typical L X Y κ i*(q/Q₁)= δ:=rfl
lemma rangeUp (e:Economics (spinFrame t) C H A L X Y κ q Q₁ R) (u:(U★ t).pulseHidden L C H A ≤ stepTiny): Adjacent (δ • R.U.symm.toLinearMap : Talent) meterTiny:=by
 intro i; let U:=R.U; let g:=δ; change ‖g • (U.symm i)-i‖≤ _
 rw [show g • (U.symm i)-i= -(U.symm (U i - g • i)) from by rw [map_sub, map_smul, U.symm_apply_apply, neg_sub], norm_neg]
 let t':= U.toLinearMap- g • LinearMap.id; let A':= accuracy C H A*nullLoss L; let K:= (U★ t).pulseBase L
 have hc(j:Ι):‖t' (ShapeLab.leg j)‖ ≤ A':=e.track j
 have hx:= (e.sail (t' i)).trans (mul_le_mul_of_nonneg_left (columns_le_of_tips t' i _ hc) (by exact (div_pos receipt_pos ((U★ t).chi_pos _)).le))
 apply hx.trans; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); change K*((markCount)* A') ≤_; refine le_trans (b:=markCount*stepTiny) ?_ ?_; swap; · linarith only [step_b,tiny_p]
 rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left u count_pos_J.le -- mul_left_comm K mark
noncomputable def latticeFieldEstimatesRisk (X:Talent):Talent:=LinearMap.id + (2:ℝ) • X
lemma planted (Z:Talent)(t₀:∀ i:Ι,‖Z (ShapeLab.leg i)‖≤2*stepTiny) : Adjacent (latticeFieldEstimatesRisk Z) meterTiny:=by
 intro i; simp only [latticeFieldEstimatesRisk, LinearMap.add_apply,LinearMap.id_coe,id_eq, LinearMap.smul_apply]; rw [add_sub_cancel_left,norm_smul, show ‖(2:ℝ)‖=2 from abs_of_nonneg zero_le_two]; refine ((mul_le_mul_of_nonneg_left (columns_le_of_tips Z i _ t₀) zero_le_two)).trans ?_; linarith only [mul_le_mul_of_nonneg_right (le_of_eq step_b) (norm_nonneg i),mul_nonneg tiny_p.le (norm_nonneg i)]

noncomputable def reelBooster (R: Reflow Wage3 (Wage3⊕η))(Q Q':CΙ ≃ₗ[ℝ] CΙ)(Z:Talent):Talent:= Q'.symm.toLinearMap.comp (R.U.symm.toLinearMap.comp ((latticeFieldEstimatesRisk Z).comp Q.toLinearMap))
lemma forecast_tick (e:Economics (spinFrame t) C H A L X Y κ q Q₁ R) (u:(U★ t).pulseHidden L C H A ≤ stepTiny) (Z:Talent)(t₀:∀ i:Ι,‖Z (ShapeLab.leg i)‖≤2*stepTiny)(v:Filer Q)(w:Filer Q')(p:∀ i,‖Q'.symm i‖≤2*‖i‖): Adjacent (δ • reelBooster R Q Q' Z) (32*meterTiny):=by
 let f:=tiny_w; let y:=tiny_p; rw [show δ • reelBooster R Q Q' Z= ((Q'.symm.toLinearMap.comp (δ • R.U.symm.toLinearMap)).comp (latticeFieldEstimatesRisk Z)).comp Q.toLinearMap from by apply LinearMap.ext; intro i; unfold reelBooster; simp only [LinearMap.smul_apply,LinearMap.comp_apply,map_smul]]
 let t:=planted Z t₀; let h0:= (w.fits p).compose (rangeUp e u) (by linarith only [f]) (by linarith only [y]); let k:= (h0.compose t (by linarith only [tiny_w]) (by linarith only [tiny_p])).compose v.sits (by linarith only [tiny_w]) (by linarith only [tiny_p]); exact k.raises  (by linarith only [y])
end Fields
noncomputable abbrev upright :ℝ:=32*meterTiny
lemma quarterStep : upright ≤1/2:=by unfold upright; linarith only [tiny_w]
abbrev Nomina (δ:ℝ)(B:ℝ)(X: Talent)(L:Side):Prop:=floorL L ≤ |δ| ∧ |δ|≤roofL L ∧ Adjacent (δ • X) B
lemma Nomina.guide(t:Axis){L:Side}{δ:ℝ}{x:Talent}(v:Nomina δ (1/2) x L) (z:Soul):
  ‖x z‖ ≤ (U★ t).pulseBase L* ‖z‖:=by
 rcases v with ⟨h,p,q⟩; have hv:= q.pay z
 change ‖δ • x z‖ ≤ _ at hv; rw [norm_smul,Real.norm_eq_abs] at hv; have hb:=floorL_pos L
 have ht:(U★ t).pulseBase L= 2/floorL L:=by change (2/headFine)/ζL L=2/(headFine*ζL L); rw [div_div]
 apply le_of_mul_le_mul_left _ hb; linarith only [ (mul_le_mul_of_nonneg_right h (norm_nonneg (x z))).trans hv,norm_nonneg z,show floorL L*((U★ t).pulseBase L *‖z‖)=2*‖z‖ by rw [ht,←mul_assoc]; field_simp]
#print axioms forecast_tick
end ResolutionFrame
end ShapeLab
end YM.CF.QuadClock
