import YM.CF.Feu.Rill
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Feu
open Nor
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
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
local notation "B_"=> (More N)
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
variable (zα:ℕ)(o:Seat N)(h:ℝ)(X:Finset (Dwell N))(J:ℕ)(ht:0 ≤ h)
abbrev stir_l(X: Finset (Dwell N)):ℝ :=max 1 ((1+(endL o X:ℝ))/(1+(J:ℝ)))
abbrev price_l(h:ℝ)(X: Finset (Dwell N)):ℝ:= (stir_l o J X)^n*h^X.card -- order tune J,h
lemma max_s(I Q:Finset (Dwell N)): endL o (I∪Q)= max (endL o I) (endL o Q):=Finset.sup_union
include ht
lemma engine : Turner (price_l (n:=n) o J h):=by
 have hz(I):1 ≤ stir_l o J I:=le_max_left ..; have hu(I):0 ≤ stir_l o J I:=zero_le_one.trans (hz I); refine ⟨fun i=>mul_nonneg (pow_nonneg (hu i) _) (pow_nonneg ht _), ?_,fun i j p=>?_⟩
 · unfold price_l stir_l endL; simp only [sup_empty, Nat.bot_eq_zero,Nat.cast_zero,add_zero, card_empty,pow_zero, mul_one]; refine pow_le_one₀ (zero_le_one.trans (le_max_left ..)) (max_le le_rfl ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) J])))
 simp only [price_l, mul_mul_mul_comm _ (h^i.card) _ (h^j.card),card_union_of_disjoint p, pow_add,←mul_pow]; refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hu _) ?_ _) (mul_nonneg (pow_nonneg ht _) (pow_nonneg ht _)); rcases le_total (endL o i) (endL o j) with u|u
 · rw [show stir_l o J (i∪j)=stir_l o J j from (by unfold stir_l; rw [max_s,max_eq_right u])]; exact le_mul_of_one_le_left (hu j) (hz i)
 rw [show stir_l o J (i∪j)=stir_l o J i from (by unfold stir_l; rw [max_s,max_eq_left u])]; exact le_mul_of_one_le_right (hu i) (hz j)
lemma raid_t(P0: BudgetPoint): Scree.tariff P0 o h X ≤ (1+J:ℝ)^P0.power* price_l (n:=P0.power) o J h X:=by
 unfold Scree.tariff price_l; rw [←mul_assoc,←mul_pow]; have hv:0<1+(J:ℝ):=by positivity
 apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ _) (pow_nonneg ht _); apply le_trans _ (mul_le_mul_of_nonneg_left (le_max_right ..) hv.le); exact le_of_eq (by field_simp)
lemma verge_l(P0:BudgetPoint): Turner (Scree.tariff P0 o h):=by rw [show Scree.tariff P0 o h=price_l (n:=P0.power) o 0 h from funext fun i=> by unfold Scree.tariff price_l stir_l; norm_num]; exact engine o h 0 ht
variable (i0:Seat (mid P B))(I: Finset (Dwell (mid P B)))
local notation "h'"=> (endL i0 I)
local notation "o'"=> (ratio G).parent i0
local notation "c'"=> (ratio G).count
local notation "t'"=> (G.count.val:ℝ)
lemma whom (u:Odd G.count.val) (i:Dwell (mid P B))(g:i∈I)(y:Dwell (mid N B)): price_l (n:=n) o' h' h {y} ≤ stepV G ((4:ℝ)^n*h) ((G.count.val:ℝ)⁻¹) n (twigS (Scion.tinOre (switchG G).symm (twigExt i))).2 (patchQ G y.2):=by
 let p:= Cube.node i.2.1.1; let q:= Cube.node y.2.1.1; let v:=separation p ((ratio G).embed q)
 have he: G.count.val * separation ((ratio G).parent p) q ≤ v+G.count.val:=by have ht:=Corona.foreshorten (ratio G) p ((ratio G).embed q); rw [Ratio.embed_parent] at ht; exact ht
 have hf:separation i0 p ≤ h':=Finset.le_sup (f:=fun i:Dwell _=> separation i0 (Cube.node i.2.1.1)) g; have hq:=Work.E04.parent_separation (ratio G) i0 p
 let R:= separation ((ratio G).parent p) q; have hs: (separation o' q:ℝ)≤ (h':ℝ)+1+(R:ℝ):=by exact_mod_cast (separation_triangle o' ((ratio G).parent p) q).trans (Nat.add_le_add_right (hq.trans (Nat.add_le_add_right hf 1)) R)
 unfold price_l stir_l stepV; rw [card_singleton,pow_one,show endL o' {y} = separation o' q from sup_singleton,show lookM G (twigS (Scion.tinOre (switchG G).symm (twigExt i))).2=p from ?_,trK G y.2 u,←mul_assoc,←mul_pow]; swap; · change node ((switchG G ((switchG G).symm i.2)).1.1)=_; rw [Equiv.apply_symm_apply]
 let N:=1+t'⁻¹*(v:ℝ); have ht':0<t':=by positivity
 have hm:1 ≤ N:=by unfold N; apply le_add_of_nonneg_right; positivity
 have hv: (R:ℝ)≤ N:=by rw [show N=t'⁻¹*(v+t':ℝ) from (by unfold N; field_simp; ring),le_inv_mul_iff₀ ht']; exact_mod_cast he
 change max _ _ ^ n * h ≤ (N*4)^n*h; apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by exact le_trans zero_le_one (le_max_left ..)) ?_ _) ht; apply max_le _ ((div_le_iff₀ (by positivity)).mpr ?_) <;> nlinarith [mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg (α:=ℝ) h')]
end YM.CF.Feu
