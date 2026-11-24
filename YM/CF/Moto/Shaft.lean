import YM.CF.Moto.Plane
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
def constant_Y (F:InkD N):InkD N:=fun _=> hollow (lifeH F 1)
def cone_G (P: BudgetPoint)(u:Site (mid N B))(V:InkD (mid N B)):InkD (mid N B):= V-constant_Y V-crest_G P u V-crest_Y u V
-- build pressure.L. at new basis preserving weight4 on halo(++ FIXED). caloric
local notation "PΨ"=> cone_G P₀ o U
local notation "kΛ"=> (Φ.val.2 ∪ (KP).val.2)
local notation "Λξ"=> KP
abbrev Ωbox (o:Site (mid N B))(Φ:Scree.Hub (mid N B))(s:ℕ):Scree.Hub (mid N B):=⟨ (node o, Φ.val.2∪ (Φrap (mid N B) o s).val.2),mem_union_right _ (Φrap _ _ _).property⟩
local notation "ΩΦ"=> Ωbox o Φ 10
include hx w
lemma part_U : PressB P₀ Φ (constant_Y U) v z :=by
 let Z':= lifeH U 1; have he:=eraF _ _ hx (zero_le_one.trans w) 1 (ping_f P₀ _); let Y:ℝ:= z; have h₁: ‖Z'‖≤ z:= by simpa [Z'] using Prism.sig0 he -- tune signature; used crumb.Co.
 exact litho _ _ _ (fun _ _ _=> rfl) (fun _ _=> rfl) measurable_const z ((norm_nonneg _).trans h₁) (fun _ _=> Prism.hail h₁)
omit hx w
lemma vaneL(F:InkD N)(p q:Scree.Hub N)(P:BudgetPoint)(V x:ℝ)(t:PressB P p F V x)(h:p.val.2⊆ q.val.2)(v:p.val.1=q.val.1):PressB P q F V x:=by
 obtain ⟨e,a,b,c,w,h₁,h₂,h₃⟩:=t; exact ⟨fun _ _ t=> e _ _ (agrees_mono t (Finset.coe_subset.mpr h)),fun i=>(a i).lift (fun i p=> mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp p).2⟩),b,c,w,h₁,fun i p0=> (by specialize h₂ i (Vow.grow_b h p0); rw [v] at h₂; exact h₂),(by rw [←v]; exact h₃)⟩
abbrev Kprice(P:BudgetPoint)(z A:ℝ):= z+z+trotΦ P z A+tera_ρ P z
include hx w t ht uA hK hv pK GG hz hk
lemma ripe_W : PressB P₀ ΩΦ PΨ v (Kprice P₀ z A) ∧ lifeH PΨ 1=0 ∧ Haro.orbitPH ((constant_Y U) 1)=0 ∧ Moto.tooth (node o) P₀ PΨ=0 ∧ Hove.jetsL o (orbitPH (PΨ 1))=0:=by
 obtain ⟨hG,hY,Q,U',hΦ⟩:= wallet U Φ o t P₀ hx w A ht uA GG hz hv hK hk pK
 let g:=constant_Y U; let s:= cone_G P₀ o U; let ΦΩ:= ΩΦ; have hp: PressB P₀ ΦΩ U v z:= vaneL _ Φ _ _ v z hx (show Φ.val.2⊆_ from subset_union_left) t
 have hs:= part_U U Φ P₀ hx w; have he:PressB P₀ ΦΩ g v z:= vaneL _ Φ _ _ v z hs subset_union_left t
 have hq:=wheel_Y U Φ o t P₀ hx w GG hz hv pK
 let Lq:= vaneL _ Λξ ΦΩ P₀ v _ hq subset_union_right rfl; let Gq:= vaneL _ Λξ ΦΩ P₀ v _ hG subset_union_right rfl; let f:InkD (mid N B):= U-g
 let Wt(Φ X:InkD (mid N B))(A b:ℝ)(h:PressB P₀ ΦΩ Φ v A)(hh:PressB P₀ ΦΩ X v b):PressB P₀ ΦΩ (Φ-X) v (A+b):=by rw [sub_eq_add_neg]; exact Larch.prop_add _ _ h (Hope.ν_P hh (zero_le_one.trans w))
 let Hc:= Wt U g _ _ hp he; let x:= Wt f Z0 _ _ Hc Gq; have h0:orbitPH (g 1)=0:= hol_l _
 refine ⟨Wt _ _ _ _ x Lq,?_,h0,?_,?_ ⟩
 · have hp:Pastry.pane (U 1)-Pastry.pane (g 1)-Pastry.pane (Z0 1)-Pastry.pane (Z1 1)=0:=by rw [show Pastry.pane _=0 from (show Pastry.pane (Z1 1)=0 from hY _), show Pastry.pane (Z0 1)=0 from Q,show Pastry.pane (g 1)= _ from (show Pastry.pane (g 1)=Pastry.pane (U 1) from hullB _),sub_self,sub_self,sub_self]
   change panHom _ (U 1-g 1-Z0 1-Z1 1)=0; simp only [map_sub]; exact hp
 · let oP:=ΦΩ.val.1; have ht:oP=node o:=rfl; change Moto.tooth oP _ ((f-Z0)-Z1)=0; rw [hut_p x Lq (zero_le_one.trans w),hut_p Hc Gq (zero_le_one.trans w),show tooth oP P₀ f= _ from hut_p hp he (zero_le_one.trans w), show ΦΩ.val.1=node o from rfl, U']
   let hx(F:InkD (mid N B))(p:∀ i:Pane (mid N B), lifeH F i=lifeH F 1):tooth (node o) P₀ F=0:=by funext i j; unfold tooth; rw [show lifeH F ∘ increment 1=(fun _:tangD _=> lifeH F 1) from funext fun i=>p _, iteratedFDeriv_const_of_ne (by omega: (2:ℕ)≠0)]; rfl
   rw [hx g (fun _=>rfl), hx _ (fun i=>(hY _).trans (hY _).symm)]; abel
 unfold cone_G; rw [Pi.sub_apply,Pi.sub_apply,Pi.sub_apply,tail_K,tail_K,tail_K,show Haro.orbitPH (g 1)=_ from h0,show Haro.orbitPH (Z0 1)=0 from hol_l _, sub_zero,sub_zero,pub_eq,map_sub,←pub_eq,←pub_eq,hΦ,sub_self]
end YM.CF.Moto
