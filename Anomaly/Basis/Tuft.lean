import Anomaly.Basis.Ready
import YM.CF.Swell.Beam
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
variable {N B M:Side}{Y:SOp N}{S:Sa N}{P:BudgetPoint}{a t d f h p' x₀ y s:ℝ}{k p q j L:ℕ}
local notation "θ"=> mid M B
local notation "I"=> Single θ
open Buffered TreasuryFog Vow.TreasuryFog
open Neon
-- all mom columns: spin, copy and gauge Born line (still on contour purchases for ALL thin Marks including bra null later)
variable {K:Scree.Loom (mid M B)}{Z:Op (Single (mid M B))}{o:Site (mid M B)} (H:Fit o P.power 1 f Z) (T:Tucked o Z) (A:DockPulse P K t d a h s j q) (l:16+1+10+q≤ j*P.B) (p_:d≤1) (Γ: Gala P.power P.order 100 y 3)(hp:1 ≤ Pressure.radiusB y)(x:P.threshold=Pressure.temp y)(hL: axleCap j^3 <L)
abbrev KazZ(p:BudgetPoint)(v h:ℝ):ℝ:=deck_K p.order p.power 10*(stakeH p.order*h^2*v)
abbrev arcLoad {N B:Side}(o:Site (mid N B))(Z:Op (Single (mid N B))):ArcΦ:= (0,Hove.jetsL o Z)
local notation "pΞ"=> temple j P (node o)
local notation "μz"=> νt a d 16*(Haro.horn*f)
local notation "Mh"=> pay_Y Z
include T H A l p_ Γ hp x hL
lemma bodyK: Drill P q j L o h s (pozV (node o) P j (shipInc K (ρlens Z) (faceD true false))) (arcLoad o Z) (cashPoncho (vaporB P h (μz)) s j) (cashPoncho (KazZ P f h) P.supportExponent j) 0:=by
 let BX:= pΞ; have he:halo (16*1+1+q+10) {node o}⊆ (pΞ).val :=Corona.halo_mono (by omega) le_rfl
 have hs:PressB P (momHub j P (node o)) Mh h (KazZ P f h):= vaneL _ (Φrap θ o 10) _ P h _ (pose_K Z o P 1 _ H 100 Γ (by omega) 10 (by omega) hp x rfl h) (Corona.halo_mono (by omega) le_rfl) rfl -- B shadow! remove.
 have ht:Neon.pillar o Mh P=arcLoad o Z:=by
    apply Prod.ext; funext i k; unfold Neon.pillar Moto.tooth; rw [show Taxi.lifeH Mh ∘ increment 1=(fun _:tangD θ=> (0:ℂ)) from funext (fun i=> Moto.bail_m _ _), iteratedFDeriv_const_of_ne (by norm_num: (2:ℕ)≠0)]; rfl
    change Hove.jetsL _ (orbitPH (Mh 1))=_; rw [hail_K]
 rw [←ht]; refine gain_core (knit_C H T pΞ he A p_) A.high A.most A.hood hs ?_ hL
 intro U v; unfold shipInc; rw [profile_bind H T pΞ he A p_ U v,← vision]; exact Sault.sky (Sault.skit _) (Flour.allP (fineShape _)) (Sault.tileL _)
-- also actual flat contraction cost pre-L all orientations. No assumption V trace at 0 is cool.
omit T A p_ l Γ hp x hL
lemma contraction (U: Op (Single (mid M B)))(p:IsStarProjection U): let Q:= ρlens Z (profile 1); ‖Matrix.trace (U*Q)‖≤ f:=by
 intro Q; have he:Q= Z:=by
    ext i j; rw [show Q i j= _ from (show Q i j=arm Z i.1 j.1 (profile 1) i.2 j.2 from stride_X Z i.1 j.1 (profile (1:Pane θ)) (fun _=>0) i.2 j.2),χtone Z i.1 j.1 (fun _=>0)] -- unfold taxi at1
    have hf(i:Site (More θ))(w:Lattice.Walk): travel (1:Pane θ) i w=1:=by induction w generalizing i with | nil=>rfl| cons a b ih=>rw [travel,ih]; simp [Step.read]
    unfold Haro.taxi; rw [hf]; unfold mater; simp only [map_one]; rw [show Subtype.val (1:UNI SU.Slot)=(1:Op SU.Slot) from rfl, mul_one]; rfl
 rw [he]; have hν: ‖U‖≤1:=by
    have hs:=CStarRing.norm_star_mul_self (x:=U); rw [show star U=U from p.isSelfAdjoint,show U*U=U from p.isIdempotentElem] at hs; nlinarith
 have hx(i j): ‖U i j‖≤1:=(norm_entry ..).trans hν
 apply le_trans _ H.1; unfold Matrix.trace; refine (norm_sum_le ..).trans ?_; unfold Hove.paid_M Tap.paidX; rw [Fintype.sum_prod_type (α₁:=I) (α₂:=I), sum_comm (s:=(univ:Finset I)) (t:=(univ:Finset I))]; apply sum_le_sum; intro i _; rw [Matrix.diag_apply,Matrix.mul_apply]; refine (norm_sum_le ..).trans (sum_le_sum fun j _=> ?_); rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (hx i j)).trans (le_mul_of_one_le_left (norm_nonneg _) (le_trans (Hove.nook_l o P.power _) (le_add_of_nonneg_left (zero_le_one.trans (Hove.nook_l o P.power _))))) -- second term maybe ≥1 not =1
end YM.CF.Swell.Porticus
