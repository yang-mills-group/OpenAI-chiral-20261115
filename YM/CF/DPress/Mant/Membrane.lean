import YM.CF.DPress.Mant.Wool
import YM.CF.Bloom.Screen
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Larch Bake Oise
variable
 {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{G:Ratio (mid N B) (mid P B)}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 (C:Tew W) {O:Shore0}{x:ℝ}
abbrev Tew.nom (C:Tew W) := |φnom C.i C.p C.pW.C|+1
namespace Tew
-- C before Lambda. track only arguments. assembly can impose C_r cap.Acc.
abbrev Prep (i p:ℕ)(w P w₀:ℝ) := wren_K i p * (4*(|P|+1)+rise_K i p w*(|φnom i p w₀|+1))+24
abbrev shade := Prep C.i C.p C.w C.Pav C.pW.C
abbrev ζCA := C.shade+1 -- >0. reference § eq:twoRAD
abbrev pay (C:Tew W)(a:ℝ) := C.ζCA * (R.L.val:ℝ)⁻¹ * a
abbrev master (C:Tew W) (O:Shore0) := C.pay O.δ
abbrev tiny (R:Patch) (x:ℝ) := dleaf R.L x
abbrev servant(x:ℝ) := C.pay (Tew.tiny R x)
lemma CEp : 0≤ C.CE:= add_nonneg zero_le_one (lucre ..)
lemma CBp : 0≤ C.CB :=by unfold CB rise_K mark_Q composeCost; positivity
lemma CRp (x:ℝ) : 0≤ C.CR x:= by unfold CR reserveT coin_n Nor.stilK; positivity
lemma CTp : 0 ≤ C.CT :=by unfold CT pack_Q strive_E composeCost; positivity
lemma solid : 0 < C.nom := add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
lemma warm : 0 < C.shade:=by change 0<C.CE*(4*(|C.Pav|+1)+C.CB*C.nom)+24; have he:= C.CEp; have hc:= C.CBp; have h:= C.solid; positivity
lemma horn : 0 < C.ζCA := add_pos C.warm zero_lt_one
lemma monoP : Monotone C.pay:= fun x y v=> mul_le_mul_of_nonneg_left v (mul_nonneg C.horn.le (by positivity))
lemma coin (O:Shore0): C.Dstar O=C.Pav*(R.L.val:ℝ)⁻¹* O.δ+O.D:=by unfold Dstar pace_Z costF gritY; field_simp
-- authorization subset. Money.κ.Better than ξ. do not coerce size for Z needed until universe.L
local notation "ιΩ"=> (R.L.val:ℝ)⁻¹
abbrev base(x:ℝ):= Tew.tiny R x
end Tew
open Tew
local notation "ιΩ"=> (R.L.val:ℝ)⁻¹
structure Dust (x:ℝ)(O:Shore0):Prop where
 year : Pony x C O
 tiny : 0<Tew.tiny R x
 strain : 4 * Tew.tiny R x ≤ O.δ
 penny : ∀ (b:ℝ),0≤b → C.φ x b ≤ C.nom * (R.L.val:ℝ)⁻¹ * b
 CARDp : O.D ≤ ιΩ*Tew.tiny R x
 CARDt : C.CR x * (6*O.Pt) ≤ ιΩ*Tew.tiny R x
variable {C}
namespace Dust
variable (p:Dust C x O)
include p
lemma coins : Tew.tiny R x ≤ O.δ:=by linarith [p.strain,p.tiny] -- name clash
lemma grant : 0< O.δ:= lt_of_lt_of_le p.tiny p.coins
lemma lease : 0<C.servant x:= mul_pos (mul_pos C.horn (by positivity)) p.tiny
lemma sail : C.servant x ≤ C.master O := C.monoP p.coins
lemma mentor : C.Dstar O ≤ (|C.Pav|+1)*ιΩ*O.δ:=by
 rw [C.coin]; apply (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C.Pav) (by positivity)) O.pos) (p.CARDp.trans (mul_le_mul_of_nonneg_left p.coins (show 0 ≤ ιΩ by positivity)))).trans_eq; ring
lemma ρp {D:ℝ}(v:0 ≤ D) : C.TΔ x O D ≤ (4*(|C.Pav|+1)+C.CB*C.nom)*ιΩ*D:=by
 have hd:= O.pos; have hδ:= p.grant; let Ωf:= εΔ O D; have hv:C.TΔ x O D ≤ Ωf*((|C.Pav|+1)*ιΩ* O.δ)+C.CB*(C.nom*ιΩ*D):= add_le_add (mul_le_mul_of_nonneg_left p.mentor (by unfold εΔ; positivity)) (mul_le_mul_of_nonneg_left (p.penny D v) C.CBp); refine hv.trans_eq ?_; unfold Ωf εΔ; field_simp
lemma reserve_p {D:ℝ}(v:0≤D): C.RΔ x O D ≤ C.shade*ιΩ*D:=by
 have ht: C.CR x * (6*(εΔ O D * O.Pt)) ≤ 4*(ιΩ*D):=by
    refine le_trans (b:= εΔ O D * (C.CR x*(6*O.Pt))) ?_ ?_ -- bad syntax
    · exact le_of_eq (by ring)
    have he:= O.pos; refine (mul_le_mul_of_nonneg_left (p.CARDt.trans (mul_le_mul_of_nonneg_left p.coins (show 0 ≤ ιΩ by positivity))) (show 0 ≤ εΔ O D by unfold εΔ; positivity)).trans_eq ?_; unfold εΔ; have hk:=p.grant; field_simp
 let A:=4*(|C.Pav|+1)+C.CB*C.nom; refine (add_le_add (show C.CE*C.TΔ x O D ≤ C.CE*(A*ιΩ*D) from mul_le_mul_of_nonneg_left (p.ρp v) C.CEp) ht).trans ?_; change _ ≤ (C.CE*A+24)*ιΩ*D; have he:0 ≤ ιΩ*D:=by positivity
 nlinarith only [he]
lemma wr_t : C.μ x O ≤ C.master O:=by
 let A:= (|C.Pav|+1)+C.CB*C.nom; have ht:C.μ x O ≤ C.CE*(A*ιΩ*O.δ)+ιΩ*O.δ:= by apply add_le_add _ (p.CARDt.trans (mul_le_mul_of_nonneg_left p.coins (by positivity))); apply mul_le_mul_of_nonneg_left _ C.CEp; refine (add_le_add p.mentor (mul_le_mul_of_nonneg_left (p.penny O.δ O.pos) C.CBp)).trans_eq ?_; unfold A; ring
 apply ht.trans; change _≤ (C.CE* (4*(|C.Pav|+1)+C.CB*C.nom)+24+1)*ιΩ* O.δ; let g:= (|C.Pav|+1); have hr:0 ≤ C.CE*g*(ιΩ * O.δ):= by unfold g; have hx:= C.CEp; have hi:= p.grant; positivity
 have hv:0≤ιΩ * O.δ:=by have hi:=p.grant; positivity
 unfold A; unfold g at hr; nlinarith only [hr,hv]
lemma lean_R : C.RΔ x O (Tew.tiny R x)+C.CR x*(6*O.Pt) ≤ C.servant x:= by refine (add_le_add (p.reserve_p p.tiny.le) p.CARDt).trans_eq ?_; unfold servant Tew.pay ζCA; ring -- tune trans_eq binding
end Dust
variable (O:ℝ→ Shore0){u:ℝ→ℝ}(q:Income0 C O u)(hw:∀ᶠ x:ℝ in atTop,4*Tew.tiny R x≤u x)
include hw q
lemma budgetline : ∀ᶠ x in atTop,Dust C x (O x):=by
 let Z(i):= (O i).Pt; let D(i):= (O i).D; let t(i):= C.CR i * (6* Z i); have ht: Litt R 2 t:= SupportP.beam_v (Nor.vale_u ..) (q.Pt.scale_l _)
 obtain ⟨i,t',v⟩:=glimp_T (R:=R)
 filter_upwards [q.Wish,eventually_ge_atTop i, tenor_Q ιΩ t ht (by positivity), tenor_Q ιΩ D (Litt.gain q.D) (by positivity), ample_η R C.i C.p C.pW.C C.πΩ C.α C.h C.uB (lt_min zero_lt_one (div_pos C.wt (by norm_num))),hw] with x t η hp l κu Uv; exact ⟨t,(v _ η).1,(q.stone x).symm ▸ Uv,κu,l,hp⟩
end YM.CF.Py.Kay
