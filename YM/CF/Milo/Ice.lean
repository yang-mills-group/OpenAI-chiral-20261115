import YM.CF.Milo.Dove
import YM.CF.Milo.Chart
import YM.CF.Pith.Pole
import YM.CF.Ione.Pose
import YM.CF.Pith.LogP
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Larch
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
-- second grade corrections.L General receipt.One-ball log-tail. split off constants or scalar portal. reserve α budgeting.
open Trees Ursell Push.AbsoluteSums.Graph
open Lilt Bake Vow
variable {F G E Q:Pax n}(Y:Aura n)(V:Orbit n) {A C H W L':Aura n→ℝ}{z u γ δ q v β:ℝ}
-- structural.Normal P. Keep.Hit.Utils
open Salt Ione Bake
local notation "η"=> P.supportExponent+1+1
variable (T V':RegBudget n)(α:ℝ)(hu:0<α)(ht:Ready Palot.stern P.B A (P.supportExponent+1+1) γ δ q)(hy:1 ≤ h)
variable (u0:∀ X,Medal P X.val ∅ (F X) h (A X))(hv: ∀ X,Medal P X.val ∅ (G X) h (A X))(hp:∀ X,Medal P X.val ∅ (F X-G X) h (α⁻¹*A X))(WDX:∀ X:Aura n,Medal P X.val ∅ (E X) h (W X))
-- F new.OP.Like tiny.G old. Earth.P.F.
variable (pX:∀ (X:Aura n)(V:Orbit n),F X V=G X V+orbV T X V+ E X V)
-- clip tiny ERP for exponent after.Series.Post.Fl. receipts.Compt.
local notation "N'"=> Nu P F G T
variable (fu:Sym_a F)(fg:Sym_a G)(cT:IncX Ione.Utrue T P h y)
include ht u0 hv fu fg cT hy
lemma veil_Ψ : Sym_a N':=by
 intro s X V; let Y:=moldA s X; let U:= yellA s V; have ha:suit_Y s (orbV T X V) = orbV T Y U:=by
    unfold orbV; rw [map_sum]; apply Finset.sum_equiv (scope_q s); intro i; rw [web0,web0,mem_filter,mem_filter,and_iff_right (mem_univ _),and_iff_right (mem_univ _)]; symm; rw [show lagE _= _ from (show lagE (scope_q s i)=moldA s (lagE i) from Subtype.ext rfl)]; exact (moldA s).injective.eq_iff
    intro i _; exact ((cT.face s trivial (spinU ..) (spinZ ..) i V.1).trans (tama s _ (spinZ ..) _)).symm
 have he :0≤ P.supportExponent+1+1:=(add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le
 unfold Nu zenS; rw [←yarnV s _ _ (0:ℝ)]; split_ifs with a; swap; exact (map_zero _).symm
 dsimp only; rw [map_sub,map_sub]; exact congrArg₂ (·-·) (congrArg₂ (·-·) (show FeeD P F Y U=suit_Y s (FeeD P F X V) from Vow.spinsE s X (suit_Y s) V (fun i=>fu s i V) ht hy u0 he 0) (show FeeD P G Y U=suit_Y s (FeeD P G X V) from Vow.spinsE s X (suit_Y s) V (fun i=>fg s i V) ht hy hv he 0)) ha.symm
omit ht u0 hv fu fg cT hy
variable (b_:Turf F)(b': Turf G)(τ:Ids n)
include b_ b'
lemma π_u:Turf N':=by
 intro X V U; unfold Nu zenS; split_ifs with v; · change FeeD P F X _- _- _ = _; rw [turfK (P:=P) F b_ X V U,turfK (P:=P) G b' X V U]
 exact rfl
include ht u0 hv fu fg cT hy hp WDX pX hu
abbrev uk_b(b α γ q:ℝ):= b+2*α⁻¹*(γ*q^1*(1-q)⁻¹)+2*(γ*q^2*(1-q)⁻¹)
lemma globe_u(t:∀ o:Seat n,tallB W P.B (P.supportExponent+1+1) o≤ b): IncX Utrue (cast_E N' τ) P h (reserveT P.power P.order P.B 1*(uk_b b α γ q)):=by
 exact worth_R P _ τ (veil_Ψ T ht hy u0 hv fu fg cT) (π_u T b_ b') (zero_le_one.trans hy) (α_G T α hu ht hy u0 hv hp WDX pX) (fun i=>cost_p T α hu ht hy u0 hv hp WDX pX i (t i))
omit ht u0 hv fu fg cT hy hp WDX pX hu b_ b'
lemma marker_L(V:Orbit n) (P:BudgetPoint):exponentL P T V.1=∑ i:Aura n with pingS P.threshold i.val V.1,orbV T i V:=by
    unfold exponentL; rw [sum_filter, ← Finset.sum_fiberwise_of_maps_to (s:=univ) (t:=univ) (g:=lagE) (fun i _=>mem_univ _)]; apply sum_congr rfl; intro i _; change ∑ j∈ web0 i,_=_; split; next p=>
       apply sum_congr rfl; intro j h; have hl:pingS P.threshold j.val.2 V.1:=(show pingS P.threshold (Bake.lagE j).val V.1 from (mem_filter.mp h).2.symm ▸ p); exact Set.indicator_of_mem (f:=T j) (s:={v|pingS P.threshold j.val.2 v}) hl -- tune implicit
    next p=> apply sum_eq_zero; intro j t; apply Set.indicator_of_notMem (s:={v|pingS P.threshold j.val.2 v}); intro u; apply p; rw [←(mem_filter.mp t).2]; exact u
include ht u0 hv fu fg cT hy hp WDX pX hu b_ b'
lemma circa(V:Orbit n):coldE P (FeeD P F) V= coldE P (FeeD P G) V+exponentL P T V.1+ exponentL P (Ione.cast_E N' τ) V.1:=by
 let Z(i:Aura n):=orbV T i V; have he:=marker_L T V P
 rw [he, Ione.ocean P _ _ (π_u T b_ b')]; unfold coldE; rw [←sum_add_distrib,←sum_add_distrib]; apply sum_congr rfl; intro X u; have hv:visible P X.val ∅ V.1:=hates (by rw [sdiff_empty]; exact (mem_filter.mp u).2)
 unfold Nu zenS; rw [if_pos hv]; dsimp only; abel
end YM.CF.Larch
