import GaugeFieldConstruction.Harvest
import GaugeFieldConstruction.Fangs
/-! graded operator shape & comparison.-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Cour Hest
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Fief Jet Vol Rel
open Yaw Pig
open Feu Feu.Corset Haro
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Lich.Muster
open Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten Lenten.Layout Fren
open Frugal
open scoped YM.CF.Mew
open BellPrice PinRack
open BellPrice PinRack
open Py.Rate.Pitching.Focus
open Filter
variable {K:Side} (τ:ℝ) {F:Side→ℝ}(p:SlowP F)(v:∀ᶠ L:Side in atTop,0 ≤ F L)
abbrev LαK (L:Side)(x:ℝ):=(L.val:ℝ)^x
lemma alpha_nnC (x:ℝ) :0 <LαK K x:= Real.rpow_pos_of_pos (by exact_mod_cast K.property) _
lemma alpha_zero (L:Side): LαK L 0=1:= Real.rpow_zero _
lemma alpha_addC (x y:ℝ):LαK K (x+y)=LαK K x* LαK K y:=Real.rpow_add (by exact_mod_cast K.property) _ _
lemma alpha_negC (x:ℝ):LαK K (-x)=(LαK K x)⁻¹:=Real.rpow_neg (by positivity) _
abbrev DimsP (n:ℕ):ℝ:=-(3+(n:ℝ))
lemma alpha_invC:LαK K (-1)=αN K:=Real.rpow_neg_one _ -- tune
lemma alpha_rate (n:ℕ):LαK K (DimsP n)=Rateκ K n:=by
 unfold DimsP; rw [alpha_negC]; unfold LαK Rateκ αN; rw [inv_pow]; congr 1; rw [←Real.rpow_natCast]; norm_cast -- tune
include p
lemma alpha_race {a x y:ℝ}(hx:0<a)(e:x<y): ∀ᶠ L:Side in atTop,F L * LαK L x ≤ LαK L y * a:=by
 filter_upwards [(p.escapes (sub_pos.mpr e)).eventually (ge_mem_nhds hx)] with L z
 let A:=LαK L; have he:F L*(A (y-x))⁻¹ ≤ a:=by rw [←div_eq_mul_inv]; exact le_trans (div_le_div_of_nonneg_right (le_abs_self _) (alpha_nnC ..).le) z
 have hp : A y=A (y-x)*A x:= by rw [←show A (y-x+x)=A (y-x)*A x from alpha_addC ..,sub_add_cancel]
 have H:F L≤a*A (y-x):=(div_le_iff₀ (alpha_nnC _)).mp (by rw [div_eq_mul_inv]; exact he)
 change F L*A x ≤ A y*a; rw [hp]; apply le_trans (mul_le_mul_of_nonneg_right H (alpha_nnC ..).le); ring_nf; exact le_rfl -- tune
lemma escape_q {a x:ℝ}(e:0 < a)(h:x<0): ∀ᶠ L:Side in atTop,F L*LαK L x≤ a:=by
 filter_upwards [alpha_race p e h] with L v; exact v.trans (le_of_eq (by rw [alpha_zero,one_mul]))
lemma escape_g {a x:ℝ}(e:0 < a)(h:0<x): ∀ᶠ L:Side in atTop,F L ≤ LαK L x*a:=by
 filter_upwards [alpha_race p e h] with L v; rwa [alpha_zero,mul_one] at v
lemma Slow_X (n:ℕ):SlowP (fun L=>TowerX τ (F L) n):=by
 induction n with
 | zero=> exact SlowP.level _
 | succ n h=> exact h.join ((SlowP.level _).prod ((SlowP.level _).join (p.prod h)))
lemma Slow_Y : SlowP (fun L => Winner (F L) τ):=by
 exact (((SlowP.level _).prod p).join ((SlowP.level _).prod p)).join (SlowP.level _)
lemma Slow_C (D:ℕ):SlowP (fun L=>Chest τ (F L) D):= (SlowP.level _).prod (Slow_X _ ((SlowP.level _).prod (Slow_Y _ p)) _)
abbrev κMini (L:Side):= LαK L (Alto/4)
-- counts for Gram ℓ1. bound row-to Book post. Terms labels per group.Clock.
structure PocketL (L:Side)(σ τ:ℝ)(D:ℕ):Prop where
    sand: αN L* RamoK L ≤1
    lobe: TowerX τ (BxMir σ τ) (D+1)*Slipρ L σ ≤1/2
    feral : Chest τ σ D*τ ≤ κMini L
    visage: τ*BxMir σ τ≤κMini L
    outset :τ*RayBudget L σ D ≤LαK L (DimsP (D+1) +2*Alto)
    pact : (Rateκ L D)⁻¹ * ClawB L τ σ D ≤ LαK L (-1+3*Alto)
    kiosk : Chest τ σ D*τ*Winner σ τ ≤RamoK L/16
    gain : GapCostUp L τ σ D ≤RamoK L/16
omit p
private lemma TrayU (σ:ℝ): Gapμ K σ≤ (2*σ+1)*LαK K Alto:=by unfold Gapμ; have ht:RamoK K=LαK K Alto:=rfl; rw [←ht]; nlinarith only [ramo_v K]
include p
include v
lemma escape_δ (w:0≤τ) (D:ℕ) : ∀ᶠ L:Side in atTop, PocketL L (F L) τ D:=by
 let U(x:Side):= Winner (F x) τ; let B(x):=SectorVal* U x; let N(x:Side):=2* F x+1; let S(x):=TowerX τ (B x) (D+1); let V(x):= Chest τ (F x) D
 have hu:SlowP B:= (SlowP.level _).prod (Slow_Y _ p); have hn:=Slow_X τ hu (D+1); have hw:=Slow_C τ p D; have hg:SlowP N:= ((SlowP.level (2:ℝ)).prod p).join (SlowP.level _)
 let y:=(3+(D:ℝ))+(19:ℝ)/20
 let X(L:Side):= N L+ V L*(SectorVal*N L)*U L
 have hx:SlowP X:=hg.join ((hw.prod ((SlowP.level _).prod hg)).prod (Slow_Y _ p)) -- tune
 -- inertia gap cost need multiplier $(x+y)$.
 filter_upwards [escape_q (F:=fun _=>1) (SlowP.level _) (by norm_num:0 < (1:ℝ)) (show (-1:ℝ)+ Alto<0 by norm_num [Alto]),
    escape_q (hn.prod hg) (by norm_num:0 < (1/2:ℝ)) (show Alto + -1 <0 by norm_num [Alto]),
    escape_g (hw.prod (SlowP.level τ)) (by norm_num:0 < (1:ℝ)) (show 0<Alto/4 by norm_num [Alto]), escape_g ((SlowP.level τ).prod hu) (by norm_num:0 < (1:ℝ)) (show 0<Alto/4 by norm_num [Alto]),
    alpha_race ((SlowP.level (τ*SectorVal)).prod hg) zero_lt_one (show Alto+DimsP (D+1)< DimsP (D+1)+2*Alto by linarith only [(by norm_num [Alto]:0<Alto)]),
    alpha_race (hw.prod ((SlowP.level SectorVal).prod hg)) zero_lt_one (show -DimsP D+ (Alto+DimsP (D+1))< -1+3*Alto by unfold DimsP; push_cast; linarith only [(by norm_num [Alto] :0<Alto)]),
    escape_g ((hw.prod (SlowP.level τ)).prod (Slow_Y τ p)) (by norm_num: 0 < (16:ℝ)⁻¹) (show 0<Alto by norm_num [Alto]), alpha_race hx (by norm_num:0 < (16:ℝ)⁻¹) (show y+(Alto+DimsP (D+1))<Alto by unfold y DimsP; push_cast; linarith),v] with i a b c e f g J K h0
 have hW:=Chest_nn _ _ h0 w D; have hS:=Tower_nn τ (B i) w (mul_nonneg InterestC (PosW h0 w)) (D+1); let A:=LαK i; let q:=A Alto; let d:=A (-1); let m:= Rateκ i D; let M:= Rateκ i (D+1); have hm:0 ≤ M:= (Rate_pr ..).le
 have he: Gapμ i (F i) ≤N i*q:= TrayU _; have hv:0 ≤A y:= (alpha_nnC _).le; have hg:0 ≤V i:= hW; have ht : 0 ≤ τ*SectorVal:= mul_nonneg w InterestC; have hf:S i* (Gapμ i (F i)*d) ≤ 1/2:= by
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (alpha_nnC _).le) hS).trans (le_trans (b:=S i*N i*LαK i (Alto+ -1)) (le_of_eq (by unfold q A S; rw [alpha_addC]; ring)) b)
 constructor
 · rw [←alpha_invC]; rw [alpha_addC] at a; exact (le_trans (le_of_eq (by change _=1*(LαK i _*LαK i _); rw [one_mul])) a) -- tune
 · unfold Slipρ; rw [←alpha_invC]; exact hf
 · exact c.trans (by rw [mul_one])
 · exact e.trans (by rw [mul_one])
 · have hF:(τ*SectorVal)*Gapμ i (F i)*M ≤ (τ*SectorVal)*(N i*q)*M:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he ht) hm
   calc
      _= (τ*SectorVal)*Gapμ i (F i)*M:=by unfold M RayBudget; ring
      _≤ (τ*SectorVal)*(N i*q)*M:=hF
      _= τ*SectorVal*N i*LαK i (Alto+DimsP (D+1)):=by rw [alpha_addC,alpha_rate]; unfold q A M; ring
      _≤ _:= f.trans (le_of_eq (mul_one _))
 · have hV:= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he InterestC) hm) hg) (show 0 ≤ m⁻¹ from inv_nonneg.mpr (Rate_pr ..).le)
   refine hV.trans ?_; rw [show m⁻¹=A (-DimsP D) from (alpha_negC (K:=i) (DimsP D)|>.trans (congrArg (·⁻¹) (alpha_rate _))).symm]; apply le_trans (b:=V i*(SectorVal*N i)*A (-DimsP D+(Alto+DimsP (D+1)))) (le_of_eq _) (g.trans (le_of_eq (mul_one _)))
   unfold A; rw [alpha_addC _ (Alto+DimsP _),alpha_addC Alto,alpha_rate]; unfold q A M; ring
 · exact J.trans (le_of_eq (div_eq_mul_inv ..).symm)
 unfold GapCostUp ClawB RayBudget
 let V':= Gapμ i (F i)
 have hU:= PosW h0 w;
 change A y * (V'*M+ V i * (SectorVal*V'*M)* U i) ≤ _
 refine (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right he hm) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he InterestC) hm) hg) hU)) hv).trans ?_
 apply le_trans (b:= X i * LαK i (y + (Alto+DimsP (D+1)))) (le_of_eq _) (K.trans_eq (div_eq_mul_inv ..).symm) -- trans_eq? syntax. Ramo.
 rw [alpha_addC y,alpha_addC Alto,alpha_rate]; unfold X q A M U V; ring
lemma pocket_d (w:0≤τ) : ∀ᶠ L in atTop,∀ j:ℕ,j≤ 2→PocketL L (F L) τ j:=by filter_upwards [escape_δ τ p v w 0,escape_δ τ p v w 1,escape_δ τ p v w 2] with i a b c d v; interval_cases d <;> assumption
end
end YM.CF.Oath
end
