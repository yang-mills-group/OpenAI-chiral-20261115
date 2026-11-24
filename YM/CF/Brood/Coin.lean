import YM.CF.Brood.Duke
import YM.CF.Brood.Harp
import YM.CF.Roots.Halo
import YM.CF.Brood.Crew
import YM.CF.Brood.Quill
import YM.CF.Brood.Told
import YM.CF.Roots.Sail
import YM.CF.Fans.Cause
import YM.CF.Roots.Flux
import YM.CF.Roots.Melt
import YM.CF.Fans.Emit
import YM.CF.Neon.Park
import YM.CF.Fans.Moon
import YM.CF.Fans.Wake
import YM.CF.Fans.Pose
import YM.CF.Neon.Quay
import YM.CF.Neon.Lux
import YM.CF.Fans.Toll
import YM.CF.Rive.Lob
import YM.CF.Ups.Tree
import YM.CF.Ups.Shea
import YM.CF.Paxos.Pen
import YM.CF.Pso.Tide
import YM.CF.Pso.Wage
import YM.CF.Pso.Azim
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
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
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
open Larch Vow Bake Mew Roots Rive Neon
local notation "BN"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
local notation "Θ"=> X.p.supportExponent
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J→Site (mid N B))(K_ E0:Key J→ RegBudget (mid N B))(F_:Key J→ ForceBudget (mid N B))
variable (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
open Moto Hove Haro Tap
open Module
open scoped YM.CF.Mew
-- mark tags.Support PU packet. σ unique location at projected Seat.Shape.On.A
abbrev LabelΩ(I:Type):= Lex (I×Ξθ)
variable {I:Type} [Fintype I][LinearOrder I]
local notation "Φ"=> LabelΩ I
abbrev tagΨ (i:I)(j:Ξθ):LabelΩ I:=toLex (i,j)
def tiβ (i:LabelΩ I):= (ofLex i).1
def tiν (i:LabelΩ I):= (ofLex i).2
lemma emit_X(i:Φ):i=tagΨ (tiβ i) (tiν i):=rfl
variable (n':Side)(σ:I→ Site (mid N B))(pσ:Injective (Cube.node ∘ σ))
abbrev xΞ (i:LabelΩ I): Site (mid N B):=σ (tiβ i)
local notation "xv"=> Cube.node ∘ xΞ σ
variable (XY : I→ BadgeΦ ≃ₗ[ℂ] BadgeΦ)(L:Side)(A Q Ξ:ℝ)
abbrev θCir (i j:LabelΩ I):ℂ:=if tiβ i=tiβ j then Φcell L Q (XY (tiβ i)) Ξ (tiν i) (tiν j) else 0
local notation "θQ"=> θCir XY L Q Ξ
abbrev eqtag_β (i:I):Ξθ ↪ LabelΩ I:= ⟨tagΨ i,fun a b h=>congrArg tiν h⟩
include pσ
lemma ΨM(i:Φ):Roots.pipe_ζ (Cube.node ∘ xΞ σ) i=univ.map (eqtag_β (tiβ i)):=by
 ext j; constructor
 · intro p; have hp: tiβ j= tiβ i:=pσ (mem_filter.mp p).2; exact mem_map.mpr ⟨tiν j,mem_univ _,hp ▸ (emit_X j).symm⟩
 intro p; obtain ⟨k,w,rfl⟩:=mem_map.mp p; exact mem_filter.mpr ⟨mem_univ _,rfl⟩
abbrev payBound(L:Side)(q:ℝ):ℝ:= 1+ξμ q* (2*(L.val:ℝ)^4)
abbrev pass_C(L:Side)(v:ℝ):=1+Fintype.card Ξθ * payBound L v
variable (hQ:0<Q)(h_Ξ:0<Ξ)(v:ℝ)(hv:0<v)(hL:Ξ ≤ 2*Q)(ωM:∀ i:I,∀ v':BadgeΦ,‖(XY i).symm v'‖≤ v*‖v'‖)
omit pσ
include hv
lemma pay_g:1≤payBound L v∧1 ≤ pass_C L v:=by
 have hQ:0 ≤ ξμ v:=mul_nonneg (mul_nonneg (μp_pos Gior).le hv.le) hPπ
 have hp:1≤ payBound L v:=le_add_of_nonneg_right (mul_nonneg hQ (by positivity))
 exact ⟨hp,le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hp))⟩
include hQ h_Ξ hv hL ωM
lemma mir (i j:Φ):‖θQ i j‖≤payBound L v:=by
 have ht:= pay_g L v hv; unfold θCir; split; swap; · rw [norm_zero]; exact zero_le_one.trans ht.1
 refine le_trans (ζclip L Q hQ Ξ v hv (XY _) (ωM _) h_Ξ _ _) ((le_trans ?_ (show ξμ v*(2*(L.val:ℝ)^4)≤payBound L v from le_add_of_nonneg_left zero_le_one))) -- $1+
 refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (μp_pos Gior).le hv.le) hPπ)
 let a:=(L.val:ℝ)⁻¹; have hx:0 < a:=by unfold a; positivity
 have hu:a≤1:=inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr L.property); rw [div_le_iff₀ (chipX L Q hQ _)]; have hV(j:Ξθ): Q*a^4≤ chipH L Q j:=by cases j; exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx.le hu (by norm_num)) hQ.le; exact le_rfl
 refine hL.trans ((Eq.le ?_).trans (mul_le_mul_of_nonneg_left (hV _) (by positivity))); unfold a; field_simp -- tune L
include pσ
lemma beam_Ψ (x:Key Φ)(u:x∈hill Φ)(i:Φ): ‖Roots.toV_C xv θQ x i‖≤ pass_C L v:=by
 unfold Roots.toV_C Roots.pipe_ζ; apply (norm_sum_le ..).trans; calc
    _ ≤ ∑ j∈ Roots.pipe_ζ xv i,payBound L v:= sum_le_sum fun j _=>by rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) (hill_i.mp u j)).trans (mir XY L Q Ξ hQ h_Ξ v hv hL ωM i j)
    _ ≤ _:=by rw [ΨM σ pσ,Finset.sum_const, card_map,card_univ,nsmul_eq_mul]; exact le_add_of_nonneg_left zero_le_one
omit hv hL ωM
lemma direct_C(x:Key Φ)(i:I)(j:Ξθ): Roots.toV_C xv θQ x (tagΨ i j)=(↑(Ξ/(chipH L Q j)):ℂ)* (Gior.equivFun ((XY i).symm (Gior.equivFun.symm (fun k=>x (tagΨ i k)))) j):=by
 unfold Roots.toV_C; rw [ΨM σ pσ,Finset.sum_map, Gior.equivFun_symm_apply, map_sum,map_sum]; rw [Finset.sum_apply, Finset.mul_sum]; refine sum_congr rfl fun k _=>?_ ; change θQ _ _ * x (tagΨ i k)= _; unfold θCir; rw [if_pos (show tiβ (tagΨ i j)=_ from Eq.trans (show tiβ (tagΨ i j)=i from rfl) (show i=tiβ ((eqtag_β (tiβ (tagΨ i j))) k) from rfl))]; change (↑(Ξ/(chipH L Q j)):ℂ)*(Gior.equivFun _ j)*_= _; simp_rw [map_smul]; rw [mul_assoc]; congr 1; exact mul_comm .. -- `congr 1`
lemma τInject : Bijective (Roots.toV_C xv θQ):=by
 constructor
 · intro x y p; funext k; let i:=tiβ k; let j:=tiν k; let X(g:Key Φ):=fun l=>g (tagΨ i l); have hf:Gior.equivFun ((XY i).symm (Gior.equivFun.symm (X x)))= Gior.equivFun ((XY i).symm (Gior.equivFun.symm (X y))):=by
      funext l; have ht:= congrFun p (tagΨ i l); rw [direct_C σ pσ XY L Q Ξ hQ h_Ξ,direct_C σ pσ XY L Q Ξ hQ h_Ξ] at ht; exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (div_pos h_Ξ (chipX L Q hQ _)).ne') ht
   exact congrFun (Gior.equivFun.symm.injective ((XY i).symm.injective (Gior.equivFun.injective hf))) j
 intro x; let X(i:I):=fun j=> (↑(Ξ/(chipH L Q j)):ℂ)⁻¹ *x (tagΨ i j); let M(i:I):= (XY i) (Gior.equivFun.symm (X i)); let G'(k:Φ):= Gior.equivFun (M (tiβ k)) (tiν k); refine ⟨G',?_⟩; funext k
 rw [emit_X k, direct_C σ pσ XY L Q Ξ hQ h_Ξ G']; let i:= tiβ k; let j:=tiν k; change _ * Gior.equivFun ((XY i).symm (Gior.equivFun.symm (Gior.equivFun ((XY i) (Gior.equivFun.symm (X i)))))) j=x _; rw [Gior.equivFun.symm_apply_apply,(XY i).symm_apply_apply,Gior.equivFun.apply_symm_apply]; exact mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (div_pos h_Ξ (chipX L Q hQ _)).ne') _
end YM.CF.Py
