import YM.CF.Moto.Shaft
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Weigh
import YM.CF.Moto.Plot
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
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
variable {d e η tW z g b c AW B':ℝ} {j k k' m n l:ℕ}
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
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> LeanV (Single Kx)
open Hove Oath
local notation "QΦ"=> Rock Kx
open Hove Haro Taxi
local notation "θn"=> (mid N B)
variable (U: InkD (mid N B)) (Φ:Scree.Hub (mid N B)) (o:Site (mid N B))(t:Φ.val.1=node o)(P₀:BudgetPoint)(hx:PressB P₀ Φ U v z) (w:1≤v)
variable (A:ℝ)(ht:DayT P₀.order A)(uA:0≤A)
local notation "KP"=> Φrap (mid N B) o 10
local notation "Hq"=> (KP)
local notation "TP"=> plateZ (node o) P₀ (tooth (Φ.val.1) P₀ U)
local notation "TU"=> crest_G P₀ o U
local notation "TΦ"=> crest_Y o U
local notation "QΨ"=> (jetsL o (orbitPH (U 1)))
variable (GG:Oath.Gala P₀.power P₀.order 100 x 3)(hz:1 ≤ radiusB x)(hv: P₀.threshold=temp x)(hK:20 < (More (mid N B)).val)(hk:3 ≤ (mid N B).val)(pK:1 ≤ P₀.power)
local notation "Vcφ"=> deck_K P₀.order P₀.power 10
local notation "Z0"=> crest_G P₀ o U
local notation "Z1"=> crest_Y o U
local notation "T_"=> (Z0+Z1)
local notation "Ψc"=> Taxi.lifeH U 1
-- build pressure.L. at new basis preserving weight4 on halo(++ FIXED). caloric
local notation "PΨ"=> cone_G P₀ o U
local notation "kΛ"=> (Φ.val.2 ∪ (KP).val.2)
local notation "Λξ"=> KP
local notation "ΩΦ"=> Ωbox o Φ 10
open Vow Bake Lilt Larch Rue
local notation "Kμ"=> Bake.lagE ΩΦ
local notation "YΣ"=> Bake.lagE Φ
local notation "Ωq"=> Bake.lagE Λξ
local notation "DΦ"=> Support (Domain N B)
local notation "H1"=> oV (constant_Y U)
abbrev portQ (D:DΦ):= Vow.flick (lagE Φ) (oV U) D - H1 - Vow.flick (lagE (Φrap (mid N B) o 10)) (oV (crest_G P₀ o U + crest_Y o U)) D
local notation "Zρ"=> (Vow.chasmR Kμ (portQ U Φ o P₀))
local notation "p0"=>P₀.threshold
lemma hike_X (v:Orbit (mid N B))(f:FleetS P₀.threshold v.1) : Vow.march P₀ YΣ (oV U) v= H1 v+Vow.march P₀ Ωq (oV T_) v+ Vow.march P₀ Kμ (oV PΨ) v+fuelV P₀ Zρ v:=by
 let X0:= ΩΦ; let W:= Kμ; let Yome:=YΣ; let D:=flags p0 v.1; let E:=Ωq; let h:=constant_Y U; rw [shade_t]; by_cases hk:Disjoint D W.val
 · rw [if_neg (show ¬fuelH _ _ from (not_not.mpr hk.symm)), march_f v f, march_f v f, march_f v f, if_pos hk, if_pos (Disjoint.mono_right (show Yome.val⊆ W.val from Finset.subset_union_left) hk),if_pos (Disjoint.mono_right (show E.val⊆ W.val from Finset.subset_union_right) hk)] -- order
   change U _=h v.1+(Z0 v.1+Z1 v.1)+(U v.1-h v.1-Z0 v.1-Z1 v.1)+0; abel
 rw [if_pos (show fuelH _ _ from fun p=> hk p.symm),Vow.march_f v f (Kμ),if_neg (show ¬Disjoint _ _ from hk)]
 have he(i:Aura (mid N B))(g:Copy (mid N B))(p:i.val⊆W.val): Vow.flick i g (D∩W.val) v=Vow.march P₀ i g v:=by
    unfold Vow.flick; rw [Vow.march_f v f]; split_ifs with t e q
    · rfl
    · obtain ⟨j,p',l⟩:= not_disjoint_iff.mp e; exact False.elim (Finset.disjoint_left.mp t (mem_inter.mpr ⟨p',p l⟩) l)
    · exact False.elim (t (Disjoint.mono_left inter_subset_left q))
    rfl
 unfold portQ; rw [Pi.sub_apply,Pi.sub_apply,show _=_ from (show flick _ (oV U) _ v= _ from he Yome (oV U) subset_union_left), he E (oV T_) (show E.val⊆ W.val from Finset.subset_union_right)]; abel -- tune
-- mask storage Canon grows one pre. Mask exponential supports post-L allowance since only *short*. αlinear no hull terms in Q repeated beyond.Path.
include hx w ht uA t hk hK hz hv GG pK
abbrev jewelX (P:BudgetPoint)(C z:ℝ):= chi_f P.order*z+chi_f P.order*z+chi_f P.order*(trotΦ P z C +tera_ρ P z)
lemma jewel_p (D:Support (Domain N B)): Medal P₀ (ΩΦ).val.2 D (portQ U Φ o P₀ D) v (jewelX P₀ A z):=by
 let h':= zero_le_one.trans w; let g:= part_U U Φ P₀ hx w; let H:= constant_Y U; let C:= chi_f P₀.order*z
 have hpYm: (YΣ).val⊆ (Kμ).val:= Finset.subset_union_left
 have hpξ: (Ωq).val⊆ (Kμ).val:= Finset.subset_union_right
 have hZ: Medal P₀ (ΩΦ).val.2 D (oV H) v C:=by
    let K:= vaneL H Φ ΩΦ P₀ v _ g hpYm t; let V:=rimR K h'; obtain ⟨v,p,q,z⟩:= (rimR g h').pays; exact ⟨V.toThemeR,v,p,fun i u Y m=>q (1,i.2) (by simpa only [sdiff_empty] using ping_f P₀ Φ.val.2) (empty_subset Y),z⟩ -- layout
 have hv:PressB P₀ KP T_ v (trotΦ P₀ z A+tera_ρ P₀ z):= prop_add _ _ ((wallet U Φ o t P₀ hx w A ht uA GG hz hv hK hk pK).1) (wheel_Y U Φ o t P₀ hx w GG hz hv pK)
 unfold portQ; rw [sub_eq_add_neg,sub_eq_add_neg]; exact ((flick_M YΣ Kμ hpYm h' (rimR hx h') D).plus hZ.negT).plus ((flick_M Ωq Kμ hpξ h' (rimR hv h') D).negT)
open Trees
variable (l':ℕ)(hL:coverNumber P₀.B Φ.val.2 ≤ l')(u:10 ≤ P₀.B)
local notation "z_"=> jewelX P₀ A z
local notation "YS"=> (Kprice P₀ z A)
include hL u
lemma fee_Q (k':ℕ) : coverNumber P₀.B (ΩΦ).val.2 ≤ coverNumber P₀.B Φ.val.2+1∧ (P₀.mass (ΩΦ).val.2 YS)≤ Real.exp (P₀.supportExponent) * P₀.mass Φ.val.2 YS:=by
 -- radius number requires intersections. anchor.O.
 let X:=ΩΦ; let T:= KP; let E:= (X).val.2; let F:= Φ.val.2
 have hu_t:node o∈ Φ.val.2:= t ▸ Φ.property
 have hp:coverNumber P₀.B E ≤ coverNumber P₀.B F+1 :=by
    apply le_trans (Corona.meets_sum hu_t (show node o∈ T.val.2 from (KP).property) P₀.B) (Nat.add_le_add_left ?_ _)
    exact (Corona.cover_mono (Corona.halo_mono u (Finset.Subset.refl ({node o}:Finset (Site (More (mid N B)))))) _).trans (by exact AnalyticBridge.CouplingShape.ballPaid ..) -- tune
 have hx':0≤ YS:= (Taxi.eraF _ _ (ripe_W U Φ o t P₀ hx w A (show _ from ht) uA GG hz hv hK hk pK).1 (zero_le_one.trans w) _ (ping_f P₀ E)).grade -- shadow ht!
 unfold BudgetPoint.mass; refine ⟨hp,?_⟩; set b:=P₀.supportExponent; rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ hx'; apply Real.exp_monotone
 calc b*(coverNumber _ E:ℝ)≤ b*((coverNumber P₀.B F+1:ℕ):ℝ):=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hp) P₀.exponent_pos.le
      _ = _:=by unfold F; push_cast; ring
end YM.CF.Moto
