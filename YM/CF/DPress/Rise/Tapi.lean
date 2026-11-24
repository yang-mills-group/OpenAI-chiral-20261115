import YM.CF.DPress.Rank.Gallery
import YM.CF.DPress.Mant.Membrane
import YM.CF.Pso.Nibs
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open Cad Mercer LinQ Glyph Qzeta Push.AbsoluteSums Larch Ione Trees Py Wray
variable {N:Side}{P:BudgetPoint}
-- pricing actual ranks. h,ζ ambient.Seam.*
structure Docket(P:BudgetPoint) where
 Sh : ℝ
 SF : ℝ
 Γ : ℝ
 γ : ℝ
 d : ℝ
 z : ℝ
 κ : ℝ
 fundsE : 0≤ Sh
 fundsF : 0≤ SF
 fundsG : Sh+κ*SF < Γ
 positive : 0<d
 gpos : 0< γ
 zpos : 0< z
 unitK : 1 ≤ κ
 degrees : degreePrice P.B γ wΨ ≤ 1/2
 stint : Sh+Γ+z*(d+rentΦ P Γ d) ≤ γ
 tick : spanV P.B*Γ ≤ 1
 bank : spanV P.B*d ≤ wΨ
 collect : d+spanV P.B*d*Γ-(wΨ-spanV P.B*d)*Γ<0
namespace Docket
variable (D:Docket P)
abbrev Week := rentΦ P D.Γ D.d
abbrev qr := degreePrice P.B D.γ wΨ
abbrev Nr := uk_b D.Week D.z D.γ D.qr
abbrev Tr := tintK P D.Week D.γ D.z
abbrev Bh (μ:Aura N→ℝ) (I:blazeK N)(x:ℝ):Prop := Timer (Cadre.chip (cribR μ) I) μ D.κ (wu P) wΨ (widthK N P.B) (spanV P.B) D.Γ D.d (spanV P.B *D.d) D.d x μ
lemma uΨ : 0 < wΨ:=by norm_num [wΨ]
lemma Wu : 0 ≤ wu P:=by unfold wu; linarith [P.exponent_pos]
lemma ℓZ : 0 ≤ ρL P:=by unfold ρL; linarith [uΨ,P.exponent_pos]
lemma ℓP : ρL P+wΨ ≤ wu P-wΨ*1:=by unfold ρL wu wΨ; linarith
lemma ℓε : ρL P ≤ wu P:=by linarith only [uΨ,ℓP (P:=P)] -- param P not p? 
lemma ℓTop : ρL P ≤ wu P - wΨ * 1:= (le_add_of_nonneg_right uΨ.le).trans (ℓP (P:=P))
lemma tiny2 : Py.Kay.lev2 P≤ρL P:= le_add_of_nonneg_right uΨ.le
lemma Γp : 0<D.Γ:=lt_of_le_of_lt (add_nonneg D.fundsE (mul_nonneg (zero_le_one.trans D.unitK) D.fundsF)) D.fundsG
lemma qlimit : D.qr<1:= D.degrees.trans_lt (by norm_num)
lemma qr_pos : 0 ≤ D.qr:= mul_nonneg (by norm_num) (stretch_pos P.B D.gpos uΨ).le
-- public funds.Credit.Special
structure Account (I:blazeK N) : Prop where
 nn(X:Aura N)(r:Support (More N)): r⊆X.val→0 ≤ I X r
 first(o:Seat N):tallB (urnL I) P.B (wu P) o ≤ D.Sh
 later(o:Seat N):tallB (Vow.hymn I) P.B (wu P) o ≤ D.SF
abbrev Chip (μ:Aura N→ℝ):Prop := 0 ≤ μ ∧ ∀ o:Seat N,tallB μ P.B (wu P+2) o ≤ D.d
variable (μ:Aura N→ℝ)(I:blazeK N)
lemma earnB (t:D.Chip μ)(f:D.Account I): D.Bh μ I 1:=by
 let u:= (show ∀ i:Seat N,nook (μ*loom_v (wu P+2) 0 (widthK N P.B) 0) i ≤ D.d from fun i=> by rw [←parse,mul_zero,sub_zero]; exact t.2 i)
 have hp:0≤ wu P-wΨ*1:= le_trans (ℓZ (P:=P)) (ℓTop (P:=P)); refine stallK D.κ D.unitK (wu P) wΨ (widthK N P.B) (Sour.vigor ..) D.Γ D.d uΨ.le μ I f.nn t.1 u D.positive.le (show 0≤ spanV P.B from Nat.cast_nonneg _) D.Γp.le D.tick D.bank ?_ hp D.collect
 intro i; rw [←parse,mul_zero,sub_zero,age_t]; exact lt_of_le_of_lt (add_le_add (f.first _) (mul_le_mul_of_nonneg_left (f.later _) (zero_le_one.trans D.unitK))) D.fundsG
lemma sustain (h: D.Bh μ I 1):D.Bh μ I 2:= {h with ok:=by norm_num, boot:=by unfold wu wΨ; linarith [P.exponent_pos]}
lemma ℓtime(t:D.Account I)(i:Seat N): tallB (urnL I) P.B (ρL P) i≤D.Sh:= (tall_m _ (fun X=> t.nn X ∅ (empty_subset _)) ℓε i).trans (t.first i)
end Docket
end YM.CF.Sour.Heath
