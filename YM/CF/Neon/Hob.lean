import YM.CF.Neon.Hick
import YM.CF.Rive.Lob
import YM.CF.Mew.Char
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Neon
open Py
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
variable{N P B:Side}{S_O:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S_O}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
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
variable {u_O Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
-- primary picture: rank 0 pressure (global scalar extracted separately), 3 PH weight and 4 derivatives, 4 radial. representation.H.
open Taxi Hope Mew
local notation "Θ"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
-- Total motion receipt ONE SOURCE. c offsets only constrained at singleton.Fo.Press.Priority. covariance later. mask pay separately.
variable (o:Site (mid N B)) (p0:BudgetPoint) (h ν :ℝ)
local notation "Tκ"=> Cube.node o
local notation "Cκ"=> (Φrap Θ o 10)
variable (L0:ℕ)(Vκ:ℝ)(Ψ: DayT p0.order Vκ)(uK:0 ≤ Vκ)
variable (Υ:Gala p0.power p0.order 100 x 3)(hu:10 ≤ p0.B)(hk:p0.threshold=temp x)(he:1 ≤ radiusB x)(hp:20 < (More (mid N B)).val)(hP:3 ≤ (mid N B).val)
open Rive
variable {ι:Type}[LinearOrder ι][Fintype ι]{α:Type}[DecidableEq α]{βe:Type}[NormedAddCommGroup βe][NormedSpace ℂ βe][CompleteSpace βe]
lemma husht_B(h:ι→ α)(V:Finset α)(f:Key ι→ βe)(p:Rive.Hush h V f)(q: River f)(u:List ι)(x:ι)(g:h x∉ V)(w:x∈u): tipI f u=0:=by -- βe mismatch Hush requires E Type
 have ht:Set.EqOn f (f∘dune x) (hill ι):=fun z t=> p _ t _ (dune_P x t) (fun i v=> (update_of_ne (a:=i) (a':=x) (fun e=>g (e ▸ v)) ..).symm)
 apply Eq.trans (lace_C u ht roots)
 induction u generalizing f with
 | nil=> simp at w
 | cons i u ih=>
    by_cases a:i=x
    · subst i; apply Eq.trans (lace_C u (f:=cutI (f∘dune x) x) (g:=fun _=>0) ?_ roots) (tip_0 u)
      intro z v; rw [← (mitt (q.stay x) v x).deriv]; have ht:(fun k:ℂ=> (f∘dune x) (Function.update z x k))=(fun _=> f (Function.update z x 0)):=funext fun u=>by change f (Function.update _ x 0)=_; simp; -- syntax
      change deriv (fun k=> (f∘dune x) (Function.update z x k)) _=_; rw [ht,deriv_const]
    have hx:x∈ u:=by simpa [a,Ne.symm a] using w
    let K:= cutI f i
    -- caution: `p=Hush` ensures f periodic when ALL out-cells but `cutI f i` may require Hush h V`? yes equality update interplay
    have hK:Hush h V K:=fun z v y t w=>integral_congr_ae (ae_of_all _ fun j=> by
       refine congrArg ((homeB j)⁻¹ • ·) (p _ (fill_I v i (homeC j)) _ (fill_I t i (homeC j)) ?_); intro k g; by_cases s:k=i; subst k; rw [update_self,update_self]; simpa only [update_of_ne s] using w k g)
    have he:Set.EqOn K (K ∘dune x) (hill ι):=fun z t=> hK _ t _ (dune_P x t) (fun i v=> (update_of_ne (a:=i) (a':=x) (fun e=>g (e ▸ v)) ..).symm)
    refine Eq.trans (lace_C u (dunk_C (f:=f) (i:=x) (Ne.symm a)) roots) (ih K hK (q.flow i) hx he) -- ABI. 
variable (F:Key ι→ Pax (mid N B))(hq:∀ i: Aura (mid N B),∀ V: Orbit (mid N B), River fun z=> F z i V)(S_P:ι→ Seat (mid N B)) (hv:∀ x:Aura (mid N B),Hush S_P x.val fun z=>F z x)
variable (vμ:ℝ)(U0:∀ z∈hill ι,Turf (F z))(Wp:∀ z∈hill ι,∃ C:Aura (mid N B)→ℝ,(∀ x:Aura (mid N B),Medal p0 x.val ∅ (F z x) h (C x))∧ ∀ i:Seat (mid N B),tallB C p0.B (p0.supportExponent+1+1) i ≤ vμ)
local notation "Pq"=> p0.supportExponent
variable (Tp:Ids (mid N B))(l_:List ι)(i0:ι)(tu: S_P i0=Cube.node o)(hT:1 ≤ h)
abbrev Kept(z:Key ι)(X:Scree.Hub (mid N B)):InkD (mid N B):= if X.val.1=node o then fun v=>F z (lagE X) (v,Tp) else 0
local notation "Eμ"=> Kept o F Tp
local notation "Dμ"=> (reserveT p0.power p0.order p0.B 2*vμ)
local notation "Iq"=> ((univ:Finset Η).filter (fun i:Η=>i.val.1=node o))
abbrev τI(i:Η)(v:Pane Θ):= tipI (fun z=> Eμ z i v) l_
abbrev τι(i: Aura Θ)(v:Orbit Θ):=tipI (fun z=> F z i v) l_
local notation "Zp"=> τI o F Tp l_
local notation "Vτ"=> τι F l_
include Wp hT U0
lemma mint_H(z:Key ι)(p:z∈hill ι): ForgeB (Eμ z) (filmK p0 (p0.supportExponent)) p0 h (fun _=>Dμ):=by
 obtain ⟨C,v,ht⟩:=Wp z p; let A:=p0.supportExponent 
 let H(i:Η):= if i.val.1=node o then fareX p0.B p0 i.val.2 * C (lagE i) else 0
 have hf(i:Η):Medal p0 i.val.2 ∅ (oV (fun s=> F z (lagE i) (s,Tp))) h (C (lagE i)):=by
    rw [←show F z (lagE i)=oV _ from funext fun a=> U0 z p _ _ _]; exact v (lagE i) -- tune
 have hs(i:Η):PressB p0 i (Eμ z i) h (H i):=by unfold Kept H; split; exact (hf i).preservesE Tp (zero_le_one.trans hT) _; exact Vale.rinse ..
 let R:=reserveT p0.power p0.order p0.B 2; have he:0 ≤ R:=by unfold R reserveT coin_n stilK; positivity
 refine ⟨⟨H,hs,fun i=>?_⟩⟩
 unfold filmK; simp_rw [ite_mul,zero_mul]; rw [← Finset.sum_filter]
 apply le_trans _ (mul_le_mul_of_nonneg_left (ht i) he); unfold tallB; rw [mul_sum]; let V:=univ.filter (fun x:Aura Θ=> i∈ x.val)
 let BZ:=univ.filter (fun x:Η=>i=x.val.1)
 rw [←sum_fiberwise_of_maps_to (s:=BZ) (t:=V) (g:=lagE) (fun j p=> mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2.symm ▸ j.property⟩)]
 apply sum_le_sum; intro j u; let Q:Η:=⟨(i,j.val),(mem_filter.mp u).2⟩; let F':=BZ.filter fun x:Η=>lagE x=j; have ht':lagE Q=j:=Subtype.ext rfl
 rw [sum_eq_single_of_mem (s:=F') Q (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,ht'⟩)]; swap; · intro v t q; have h:v=Q:=Subtype.ext (Prod.ext ((mem_filter.mp (mem_filter.mp t).1).2.symm) (congrArg Subtype.val (mem_filter.mp t).2)); exact False.elim (q h)
 have hu:0 ≤ C j:= (v j).wage (zero_le_one.trans hT)
 unfold H; split; swap; · rw [mul_zero]; exact mul_nonneg he (mul_nonneg hu (Real.exp_pos _).le)
 rw [ht']; let L:= (currency p0.B p0.supportExponent j.val); apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nor.coinPay p0 j.val 2 (by norm_num)) hu) (Real.exp_pos _).le).trans_eq; unfold Trees.currency; rw [show Q.val.2=j.val from rfl,show p0.supportExponent+1+1=p0.supportExponent+2 from (by ring),add_mul,Real.exp_add]; unfold R; ring
omit Wp hT U0
end YM.CF.Neon
