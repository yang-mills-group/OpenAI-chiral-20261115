import GaugeFieldConstruction.Amber
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
variable {I:Type}[Fintype I]{N:Side}{L:Side}{P:BudgetPoint}{o:Seat N}{v h f τ μ t b:ℝ}{M:Male}{D:ℕ}
variable {H:I→Zone N}{K:Zone N}{V:I→Waves}{G:I→ℕ}
variable (p:Freight (P:=P) o M t μ τ h b D H G L) (hq:∀ i,G i ≤ D) (hs:0<t)(he:0≤h)(hu:0≤μ)(hy:0≤τ)
-- normalized inverse incl costs. Can lower τ? no.
abbrev Rate_c {N:Side}(o:Seat N)(p:BudgetPoint)(M:Male)(h:ℝ)(D:ℕ)(K:Zone N)(t:ℝ): Waves:= ((↑(t⁻¹)):ℂ) • CardT K (KeyUp p) M h o D
abbrev RayBudget (L:Side)(Q:ℝ)(D:ℕ):ℝ:=SectorVal*(Gapμ L Q)*Rateκ L (D+1)
abbrev KeyμB (L:Side)(P:BudgetPoint)(o:Seat N)(H:I→Zone N) (G:I→ℕ)(u:FrameK I):= W_s H (Walt L G u) -- definition
-- Pc matrix specified in coordinate-free form, both norm bounds including Z inverse on arbitrary target. Cρ and inverse unique. Watt linear
abbrev SwitchP {I:Type}[Fintype I](b:I→Waves)(o:Seat N)(p:BudgetPoint)(M:Male)(h q:ℝ)(j:ℕ)(H:I→Zone N)(L:Side)(G:I→ℕ)(Z:FrameK I→ₗ[ℂ]FrameK I):Prop:= ∀ x:FrameK I, Woof x b=scalB (Plug p o M h j H L G q) (Z x)
abbrev ClawB (L:Side)(τ μ:ℝ)(D:ℕ):=Chest τ μ D*RayBudget L μ D
-- weighted substitutions. EPL 
abbrev GapGain (L:Side)(D:ℕ):ℝ:= (L.val:ℝ)^ ((3+(D:ℝ))+(19:ℝ)/20)
abbrev G_price (K:Zone N)(X:I→Zone N)(G:I→ℕ)(L:Side)(D:ℕ)(Z:FrameK I):=let t:ℂ:=(GapGain L D:ℝ); t • (K+W_s X (Walt L G Z)) -- correction Z with sign minus
lemma Gap_nv (L:Side)(D:ℕ):0 ≤ GapGain L D:= Real.rpow_nonneg (by positivity) _
lemma Chest_nn (μ τ:ℝ)(p:0≤μ)(v:0≤τ)(D:ℕ):0 ≤ Chest τ μ D:=by unfold Chest Bbt; exact mul_nonneg (by positivity) (Tower_nn _ _ v (mul_nonneg InterestC (PosW p v)) D.succ)
include p hs he hu hy
-- κ* orientations before Budget. p works all.
structure CostumeT (μ τ t b:ℝ)(G:I→ℕ)(V:I→Zone N)(g:FrameK I)(p:BudgetPoint)(o:Seat N)(M:Male)(h:ℝ)(D:ℕ)(L:Side)(T:Waves) : Prop where
    solves: Woof g (Plug p o M h D V L G t)=T
    budget: LoomK g ≤ Chest τ μ D *‖T‖
    earns : Basalt p o L.val (L.val+1) (W_s V (Walt L G g)) ((Chest τ μ D*‖T‖)*(Winner μ τ*t)) 2 (LoomK (Walt L G g)*b) h D M
    part : CardT (W_s V (Walt L G g)) (KeyUp p) M h o D= (t:ℂ) • T
lemma CostW (T:Waves)(g:FrameK I)(p0:Woof g (Plug P o M h D H L G t)=T) : CostumeT μ τ t b G H g P o M h D L T:=by
 have ⟨A,Y⟩:= Plinth p.charm he (Walt L G g)
 have He:=p.purse g; rw [p0] at He
 refine ⟨p0,He,A.sharpen ?_ (le_refl _),?_⟩
 · rw [Walt_tip]; exact mul_le_mul_of_nonneg_right He (mul_nonneg (PosW hu hy) hs.le)
 · rw [Y D,wave_spend H g G D h L hs,p0]
-- input and output basis maybe same indices any grade/hom. condition of target.T.
variable (bO:I→ℕ) (bP:Planaris bO ΓProj D V τ)
include bP
lemma InZ (Z:FrameK I→ₗ[ℂ]FrameK I)(e:SwitchP V o P M h t D H L G Z) : Bijective Z ∧ (∀ x:FrameK I, LoomK (Z x)≤ Chest τ μ D*τ* LoomK x ∧ LoomK x ≤ τ*BxMir μ τ* LoomK (Z x) ∧ CardT (W_s H (Walt L G (Z x))) (KeyUp P) M h o D = (t:ℂ) • Woof x V) :=by
 let bT:= Plug P o M h D H L G t
 have h(x:FrameK I): Woof (Z x) bT= Woof x V := (e x).symm
 have hx(x):= CostW p hs he hu hy (Woof x V) (Z x) (h x) -- includes hq? no
 have Hτ(w:FrameK I): LoomK w ≤ τ*BxMir μ τ * LoomK (Z w):= by
    apply le_trans (b:=τ* (LoomK (Z w)*BxMir μ τ)) _ (le_of_eq (by ring))
    apply le_trans (bP.brake w)
    exact mul_le_mul_of_nonneg_left ((h w) ▸ p.plank _) hy -- dependent.rewriter
 have hY:Injective Z:= LinearMap.ker_eq_bot.mp (by
    rw [LinearMap.ker_eq_bot']; intro v g
    have ht:LoomK v ≤0:=by have ht:=Hτ v; rw [g,show LoomK (0:FrameK I)=0 from (by simp [LoomK]),mul_zero] at ht; exact ht
    exact funext fun i=> norm_le_zero_iff.mp ((single_k v i).trans ht)) -- syntax
 refine ⟨⟨hY, LinearMap.injective_iff_surjective.mp hY⟩,fun i=> ⟨?_,Hτ i,(hx i).part⟩⟩
 refine le_trans (b:=Chest τ μ D*(LoomK i*τ)) (le_trans (hx i).budget (mul_le_mul_of_nonneg_left (woof_cost i bP.bounded) (Chest_nn μ τ hu hy D))) (le_of_eq (by ring))
set_option maxHeartbeats 150000 in
lemma Certified_pc : ∃ Z:FrameK I→ₗ[ℂ] FrameK I, SwitchP V o P M h t D H L G Z:=by
 have hv(i):ΓProj D (V i)=V i:=by rw [bP.saturated,if_pos (bP.ray i)]
 choose T u using fun i=>p.lever (V i) (hv i)
 -- build linear directly mapping all. scans. 
 let Z:= scalB T; -- E= I→ℂ. 
 refine ⟨Z,fun i=>?_⟩; let B:=Plug P o M h D H L G t
 change _= scalB B (∑ k:I,i k • T k); rw [map_sum]; exact sum_congr rfl (fun j _=> (congrArg (fun x=>i j • x) (u j)).trans ((scalB _).map_smul ..).symm)
omit bP
section
def Khat (x y:ℝ) := x*y
-- gap charge billed. after sign-correction. 
variable (hG:Basalt P o L.val (L.val+1) K (Gapμ L μ*(Rateκ L (D+1)*t)) 2 b h D M)
omit p hu hy
include hG
lemma Gap_s : let T:=Rate_c o P M h D K t; ‖T‖≤ RayBudget L μ D ∧ ΓProj D T=T:=by
 intro T
 have ht: ΓProj D (CardT K (KeyUp P) M h o D)= _:= MStore _ (le_refl D)
 refine ⟨?_, (show _ from ((ΓProj D).map_smul (↑(t⁻¹):ℂ) _).trans (congrArg ( ((↑(t⁻¹):ℂ)) • ·) ht))⟩
 have hx:= N_prW Packs_U (show 0 ≤ t⁻¹ from inv_nonneg.mpr hs.le) (CardT K (KeyUp P) M h o D)
 calc
    _ ≤ t⁻¹ *(SectorVal*(Gapμ L μ*(Rateκ L (D+1)*t))):= hx.trans_le (mul_le_mul_of_nonneg_left (CardT_note hG he (by norm_num) _) (by positivity))
    _ = _:=by unfold RayBudget; field_simp
abbrev GapCostUp (L:Side)(τ μ:ℝ)(D:ℕ) := GapGain L D*(Gapμ L μ * Rateκ L (D+1) + (ClawB L τ μ D)* Winner μ τ)
omit hG he hs
local instance wavesN : Neg Waves:=kinnA.toNeg
private lemma Cσ_er (t:ℝ)(p:0<t)(E:Waves): E+(t:ℂ) • (-((↑(t⁻¹):ℂ) • E))=0:=by
 let τ:ℂ:=t; have hv:(t:ℂ)*(↑(t⁻¹):ℂ)=1:=by rw [← Complex.ofReal_mul,mul_inv_cancel₀ p.ne',Complex.ofReal_one]
 exact (show ∀ {E:Type}(P:TPack E)(a b:ℂ),a*b=1→letI:=P.G; letI:=P.S;∀ x:E,x+a • -(b • x)=0 from fun {_} P a b e=> (by letI:=P.G; letI:=P.S; intro x; simp only [smul_neg,smul_smul,e,one_smul]; simp)) Packs_U _ _ hv E -- tune
include hG he hs p hu hy
set_option maxHeartbeats 140000 in
lemma Gap_call (g:FrameK I)(u:Woof g (Plug P o M h D H L G t) = -Rate_c o P M h D K t): let R:= G_price K H G L D g; LoomK g ≤ ClawB L τ μ D ∧ Basalt P o L.val (L.val+1) R (GapCostUp L τ μ D*t) 2 (GapGain L D*(b+LoomK (Walt L G g)*b)) h D M ∧ CardT R (KeyUp P) M h o D=0:=by
 intro R; let q:=Rate_c o P M h D K t; let qι:= GapGain L D; have hx:0 ≤ qι:= Gap_nv ..
 obtain ⟨Hf,HT⟩:= Gap_s hs he hG
 let w:= ClawB L τ μ D; have hk: ‖-q‖≤ RayBudget L μ D:=by rw [norm_neg]; exact Hf
 have hz:= mul_le_mul_of_nonneg_left hk (Chest_nn _ _ hu hy D); let r0:= W_s H (Walt L G g); have heP:= CostW p hs he hu hy (-q) g u; have H0:= (hG.terms heP.earns he); have hB:= H0.smul (qι:ℂ) he
 have hv : ‖(qι:ℂ)‖ = qι:=α_money _ hx
 refine ⟨heP.budget.trans hz,hB.sharpen ?_ (le_of_eq (by rw [hv])),?_⟩
 · rw [hv]; unfold GapCostUp; change _ ≤ qι*_*t; rw [mul_assoc qι]; apply mul_le_mul_of_nonneg_left _ hx
   rw [add_mul (Gapμ L μ * Rateκ L _) _ t,mul_assoc _ (Rateκ L _),mul_assoc _ (Winner μ τ)]; exact add_le_add_right (mul_le_mul_of_nonneg_right hz (mul_nonneg (PosW hu hy) hs.le)) _
 have hf:= (CardT_plus hG heP.earns he D); rw [heP.part] at hf
 exact (CardT_scalar (↑qι:ℂ) H0 he D).trans ((congrArg ( (↑qι:ℂ) • ·) (hf.trans (Cσ_er _ hs _))).trans (Troot_z Packs_U _))
set_option maxHeartbeats 150000 in
lemma Gap_z_ (H0:FrameK I→ₗ[ℂ]FrameK I)(ev:SwitchP V o P M h t D H L G H0)(Tz:FrameK I)(p0:Woof Tz V=Rate_c o P M h D K t): Woof (H0 (-Tz)) (Plug P o M h D H L G t)= - Rate_c o P M h D K t:=by
 change scalB _ _= _; rw [←ev,←p0]; exact map_neg (scalB V) Tz
end
end
end YM.CF.Oath
end
