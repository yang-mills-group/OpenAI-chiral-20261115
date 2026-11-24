import YM.CF.Rive.Grid
import YM.CF.Rive.Ora
import YM.CF.Mew.Firth
import YM.CF.Vow.Law
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue Trees
abbrev gift_β (P:BudgetPoint)(Θ:ℝ)(X:Support (More n))(v:ℝ):ℝ := Trees.currency P.B Θ X*v
variable {K:Cusp n} {C: blazeK n} (p:ArmsK P K C h) (x':Force n)
include p
lemma mezzo(t:0 ≤h)(k:Seat n)(a Θ:ℝ)(hw:0 < a) : (∑ i:Force n, if k∈ i.val.1.val.2 then gift_β P Θ i.val.1.val.2 (rentH P C i) else 0) ≤ Nor.reserveT P.power P.order P.B a * tallB (hymn C) P.B (Θ+a) k:=by
 let KQ(i: Force n):=rentH P C i; let TV (i:Aura n):=∑ y: Force n with lordD y=i,gift_β P Θ y.val.1.val.2 (KQ y); let R:=Nor.reserveT P.power P.order P.B a
 have hp(X:Aura n)(D: Support (More n))(i: Force n)(v: i∈motV X D):KQ i=fareX P.B P X.val*(bassH X*C X D):=by obtain ⟨a,t⟩:= (mem_filter.mp v).2; unfold KQ rentH; rw [a,t]
 have hr(X:Aura n)(D: Support (More n))(v:D∈ fullD X):(∑ i∈motV X D,gift_β P Θ i.val.1.val.2 (KQ i)) ≤ R*(C X D*currency P.B (Θ+a) X.val):=by
    rw [sum_congr rfl (fun j u=> show gift_β P Θ j.val.1.val.2 (KQ j)=gift_β P Θ X.val (fareX P.B P X.val*(bassH X*C X D)) from (by rw [hp _ _ j u,(show j.val.1.val.2 = X.val from congrArg Subtype.val (mem_filter.mp u).2.1)])),sum_const, countV X v,nsmul_eq_mul]
    have hx: (X.val.card:ℝ)≠0:=by exact_mod_cast (card_pos.mpr X.property).ne'
    rw [show (X.val.card:ℝ)*gift_β P Θ X.val _= Trees.currency P.B Θ X.val* C X D*fareX P.B P X.val from (by unfold gift_β bassH Trees.currency; field_simp <;> ring)] -- tune
    apply le_trans (mul_le_mul_of_nonneg_left (Nor.coinPay P X.val a hw) (mul_nonneg (Real.exp_pos _).le ((p.price X _ (mem_filter.mp v).2.1 (mem_filter.mp v).2.2).wage t))); unfold R Trees.currency; rw [add_mul,Real.exp_add]; exact le_of_eq (by ring)
 have hv(X:Aura n): TV X ≤ R * (hymn C X * currency P.B (Θ+a) X.val):=by
    unfold TV hymn; rw [←sum_fiberwise_of_maps_to (s:=univ.filter (lordD ·=X)) (g:=extraD) (t:=fullD X) ?_,sum_mul,Finset.mul_sum]; swap; · intro i h; rw [←(mem_filter.mp h).2]; exact mem_filter.mpr ⟨mem_univ _,i.property⟩ -- tune h implicit
    refine sum_le_sum fun i g=>?_ ; rw [filter_filter]; exact hr X i g
 rw [←sum_filter, ←sum_fiberwise_of_maps_to (t:= (univ.filter fun i:Aura n=> k∈i.val)) (g:=lordD) ?_]; swap; · intro i p; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2⟩
 unfold tallB; rw [mul_sum]; refine sum_le_sum fun i p=>?_ ; apply le_trans _ (hv i); apply le_of_eq; unfold TV; apply sum_congr _ (fun _ _=>rfl); ext j; simp only [mem_filter, mem_univ, true_and,and_iff_right_iff_imp]; intro g; change k∈ (lordD j).val; rw [g]; exact (mem_filter.mp p).2 -- tunes co lift
end YM.CF.Vow
