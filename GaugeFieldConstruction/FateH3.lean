import GaugeFieldConstruction.Bronc3
import GaugeFieldConstruction.Dickens3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open TableF TableF.Lenten TableF.Lenten.Layout
open Ladder3 Salt Levier Thera Urn Hest Sault Pastry Haro
open XGarden XGarden.MastTin SeasonH Branch Tenant Drapes Rill Nacre Broc SliceRoof
open XGarden.Shield
open Leaf
attribute [local instance] boreKSpace boreXN opCStarAlgebra
variable {R:Loom n}{k:ℕ}{t d a c e h:ℝ} 
variable (F:Elm n Unit d a c)(R:Loom n)(k:ℕ)(t:ℝ)
-- halves option. Cell width one.V orientation motion.
variable (X S D:Support (More n))(W:Orbit n)
local notation "Vx"=> uplift F R k D S t
local notation "Y"=> Single n
local notation "GL"=> LeanV (Single n)
variable (u:Roof n t d k R)(q:0<d)
variable (P:BudgetPoint)(o:Seat n)(Z:Paper n)(p:L3 n){g h T K e':ℝ} (v:Act3 (ArchQ F R k t P o p Z) P (cipherK k) h g)(r: TrackD (Py.KeyUp P) (Pach o) h Z e')(s:portable Z)
local notation "Aκ"=> ArchQ F R k t P o p Z
local notation "Yp"=> Pach o
local notation "Au"=> pay_A o F T h e'
local notation "tK"=> Hud K -- tune
variable (i:hud_T 7 K)(b:0≤T)(f:coinH K T)(pH:Hann P k t)(hv:1 ≤ h)
include r u q s i b f pH hv
variable {υ δ:ℝ}{J:ℕ}(hp:0<a)(hT:Tyrant k J δ a)(H:pure_Rim F)
local notation "Fι" p:max=> ArchQ F R k t P o p Z
local notation "Λ"=> pay_A o F T h e'
local notation "G"=> Support (More n)
local notation "R_h"=> rent δ
abbrev limb_Bill(p:SP3 n):=if imply3 o p then KernelLeg p F T h*rent δ (limbM k p) else 0
local notation "τ" x:max=> limb_Bill F k o (h:=h) (T:=T) (δ:=δ) x
abbrev Dobie(δ a k:ℝ)(J m:ℕ):ℝ:= Real.exp (δ*((m+m+45:ℕ):ℝ)^4)+ a * k -- J noise adjust
abbrev Epoch3ᵣ(T d a c δ:ℝ)(K M:ℕ):= Dobie δ (BudgetValve T d) (CrownBill c M) M K
abbrev RtHead:ℝ:= (49:ℝ)^4
include hp hT H
lemma dayLemb : (∑ V:Support (More n), τ (some V)) ≤ RtHead* Epoch3ᵣ T d a c δ k J / h^2:=by
 let S(V:Support (More n)):= Branch.rent δ (Lattice.halo (k+22) V); let b'(V:Support (More n)):= BillLeg V d T a c F * S V
 let D:= Epoch3ᵣ T d a c δ k J; let B:= BudgetValve T d
 have he:= hT.1; have hB:0≤B:=by unfold B BudgetValve DeskK composeCost; positivity
 have hu(y:Seat n): (∑ V:Support (More n) with y∈V, b' V) ≤ D:=by
    unfold b' BillLeg; simp_rw [add_mul,sum_add_distrib]; unfold D Epoch3ᵣ Dobie; apply add_le_add
    · rw [sum_eq_single {y}];
      · unfold pint3; rw [card_singleton,if_pos rfl,one_mul]; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ he.le; have h:(Lattice.halo (k+22) ({y}:Support (More n))).card ≤ (k+22+(k+22)+1)^4:=by simpa using (Corona.halo_size ({y}:Support (More n)) (k+22)) -- shape
        rw [show k+k+45=k+22+(k+22)+1 from (by omega)] -- tune 45 aspect
        exact_mod_cast h
      · intro l p n; unfold pint3; rw [if_neg (fun t=> n ?_),zero_mul]; obtain ⟨x,h⟩:=card_eq_one.mp t; have ht:y=x:= mem_singleton.mp (h ▸ (mem_filter.mp p).2); exact ht.symm ▸ h
      simp
    simp_rw[mul_assoc (BudgetValve ..),←mul_sum]; exact mul_le_mul_of_nonneg_left (LegendT k d a c F hp hT y) hB
 have hR:0≤ D:=by unfold D Epoch3ᵣ Dobie; change 0≤ _+B* _; exact add_nonneg (Real.exp_pos _).le (mul_nonneg hB (show 0≤ CrownBill c J from by unfold CrownBill; have h:=F.bank.posP; unfold Corona.Hive.yardZ; positivity))
 let KH:= (h^2)⁻¹; have hK:0≤ KH:= inv_nonneg.mpr (sq_nonneg _)
 have ht(v:Support (More n)): τ (some v) ≤ ∑ i∈Yp,(if i∈v then b' v*KH else 0):=by
    let L(i:Seat n):= if i∈v then b' v*KH else 0; have hp(i):0≤ L i:=ite_nonneg (mul_nonneg (mul_nonneg (Vegan3 F R k t v u q b) (Real.exp_pos _).le) hK) le_rfl
    unfold limb_Bill; split; swap; exact sum_nonneg fun i _=> hp i
    next g=> obtain ⟨y,v',p⟩:= Finset.not_disjoint_iff.mp (show ¬ Disjoint (Pach o) v from g); apply le_trans (a:= _) _ (single_le_sum (f:=L) (fun i _=> hp i) v')
             change BillLeg v d T a c F/h^2*(S v) ≤ _; unfold L; rw [if_pos p]; exact le_of_eq (by unfold b' KH; ring)
 apply (sum_le_sum (fun v _=> ht v)).trans; rw [sum_comm]
 let V0:=Pach o; refine le_trans (sum_le_sum (g:=fun _=>D*KH) (fun i v=>?_)) ?_
 · rw[←Finset.sum_filter,←sum_mul]; exact mul_le_mul_of_nonneg_right (hu i) hK
 rw [sum_const,nsmul_eq_mul]; have he:(V0.card:ℝ) ≤ RtHead:=by unfold RtHead; exact_mod_cast (show V0.card≤49^4 from (by simpa using Corona.halo_size ({o}:Support (More n)) 24))
 apply (mul_le_mul_of_nonneg_right he (mul_nonneg hR hK)).trans_eq; unfold KH D; ring
abbrev TPrice(T d a c δ h:ℝ)(k j:ℕ):= RtHead*Epoch3ᵣ T d a c δ k j/h^2
local notation "Wν"=> TPrice T d a c δ h k J
-- price root.K frame. pure p projection's weight not needed except all.
noncomputable def bareX (b:ℝ) := ∑ i:L3 n, if τPure i then 0 else pay_A o F T h e' i*rent b (pack3 k o i).val.2 -- bind
omit r u q s i b f pH hv hp hT H in
private lemma PQill {n:Side}(S T U:Support n)(b:ℝ)(h:0≤ b): rent b (S∪(T∪U)) ≤ rent b S * (rent b T * rent b U):=by
 unfold Branch.rent; rw[←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
 rw [←mul_add,←mul_add]; apply mul_le_mul_of_nonneg_left _ h; exact_mod_cast (card_union_le _ _).trans (Nat.add_le_add_left (card_union_le T U) _)
local notation "E0"=> Real.exp (δ*RtHead)
private lemma runLeg (i j:SP3 n): Λ (i,j)*rent δ (pack3 k o (i,j)).val.2 ≤ E0*7*e'*(τ i * τ j):=by
    have ht:=track_pos r; have hρ:R_h (Pach o)≤ E0:=by
       apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ hT.1.le; unfold RtHead; exact_mod_cast (show (Pach o).card ≤49^4 from by simpa using Corona.halo_size ({o}:Support (More n)) 24)
    have hl(X):0≤ KernelLeg X F T h:= Kp_h F R k t u q P pH ‹hud_T 7 K› b f hv X
    unfold pay_A; split
    next he=>
       let T0:= KernelLeg i F T h; let T1:=KernelLeg j F T h
       change T0*T1*7*e'*rent δ (Pach o∪ _)≤_
       rw [limb_Bill,if_pos he.1,limb_Bill,if_pos he.2]; -- worry rw ordering when i=j, not def
       have hx : 0 ≤ T0*T1*7*e':=mul_nonneg (mul_nonneg (mul_nonneg (hl _) (hl _)) (by norm_num)) ht
       let x:=limbM k i; let y:=limbM k j; let X:Support (More n)→ℝ:= R_h
       have hw:rent δ (pack3 k o (i,j)).val.2 ≤ E0* (X x* X y):= (PQill Yp x y δ hT.1.le).trans (mul_le_mul_of_nonneg_right hρ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
       apply (mul_le_mul_of_nonneg_left hw hx).trans_eq; change _= E0 *7*e'* (T0*X x*(T1*X y)); ring
    next hz=>
       have hm(X):0≤τ X:=ite_nonneg (mul_nonneg (hl _) (Real.exp_pos _).le) le_rfl
       rw[zero_mul]; exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (by norm_num)) ht) (mul_nonneg (hm _) (hm _))
-- pricing aggregate including only single pure.T uniform post h.S binding.
abbrev PressureL (T d a c δ h:ℝ)(k j:ℕ)(f:ℝ):ℝ:=Real.exp (δ*RtHead)*7*f*((1+TPrice T d a c δ h k j)^2)
abbrev Pressure_M (T d a c δ h:ℝ)(k j:ℕ)(f:ℝ):ℝ:= let Yx:=TPrice T d a c δ h k j; Real.exp (δ*RtHead)*7*f*(2*Yx+Yx^2)
def raw_cost3 (D:Factor3 n)(b p:ℝ):= p * rent b D.H.val.2
local notation "ω"=> PressureL T d a c δ h k J e'
local notation "ξ"=> Pressure_M T d a c δ h k J e'
local notation "Zν" x:max=> raw_cost3 (Fι x) δ (Λ x)
local notation "μρ"=> E0*7*e'
local notation "Wz"=>TPrice T d a c δ h k J
lemma billQ : (∑ v:L3 n, raw_cost3 (ArchQ F R k t P o v Z) δ (pay_A o F T h e' v))≤ PressureL T d a c δ h k J e' ∧ (∑ v:L3 n, if τPure v then 0 else raw_cost3 (ArchQ F R k t P o v Z) δ (pay_A o F T h e' v))≤ Pressure_M T d a c δ h k J e' :=by
 let L(x:SP3 n):= τ x; let A:= ∑ x:SP3 n,L x; let B:= ∑ x:Support (More n),L (some x); let C0:=μρ
 let α:=Wz
 let v0:L3 n:= (none,none); have V':L none=1:=by
    unfold L limb_Bill; rw[if_pos (show imply3 o none from True.intro)]; change 1*Real.exp (δ*((∅:Support (More n)).card:ℝ))=1; simp
 have hA:A=1+B:=by unfold A; rw [Fintype.sum_option,V']
 have he(p:L3 n): τPure p=true ↔ p=v0:=by
    constructor
    intro q; exact Prod.ext (Option.isNone_iff_eq_none.mp ((Bool.and_eq_true ..).mp q).1) (Option.isNone_iff_eq_none.mp ((Bool.and_eq_true ..).mp q).2)
    intro e; rw[e]; rfl -- tune
 let g(v:L3 n):= raw_cost3 (ArchQ F R k t P o v Z) δ (pay_A o F T h e' v)
 let R₀ (v:L3 n):= C0*(L v.1*L v.2); have Hs0: (∑ v:L3 n,R₀ v)= C0*((1+B)^2):=by
    unfold L3; rw[←hA]; unfold R₀; simp_rw [← Finset.mul_sum]; rw [Fintype.sum_prod_type]; simp_rw[←mul_sum,←sum_mul,pow_two]; rfl
 have mu: R₀ v0=C0:=by unfold R₀ v0; dsimp only; rw[V']; ring
 have hv₁ :0≤e':=track_pos r
 have hz:0≤ B:=sum_nonneg (fun j _=>ite_nonneg (mul_nonneg (Kp_h F R k t u q P pH i b f hv (some j)) (Real.exp_pos _).le) le_rfl) -- where helper
 have ht:B≤ α:= dayLemb F R k t u q P o Z r s i b f pH hv hp hT H -- shadow
 have hu:0 ≤ C0:= mul_nonneg (mul_nonneg (Real.exp_pos _).le (by norm_num)) hv₁
 have H'(v:L3 n):g v≤R₀ v:=by obtain ⟨x,v⟩:=v; exact runLeg F R k t u q P o Z r s i b f pH hv hp hT H _ _
 constructor
 · apply (sum_le_sum fun v _=>H' v).trans; rw [Hs0]; unfold PressureL; change C0*(_^2) ≤C0*((1+α)^2); gcongr
 let g'(v:L3 n):=if τPure v then 0 else R₀ v; have ht': (∑ v:L3 n,g' v)= C0*(2*B+B^2):=by
    have he':(∑ v:L3 n,R₀ v)=(∑ v:L3 n,(if v=v0 then R₀ v0 else 0))+ (∑ v:L3 n,g' v):=by rw [←Finset.sum_add_distrib]; refine sum_congr rfl fun v _=>?_ ; unfold g'; by_cases t:v=v0 <;> simp only [he,t,ite_true,add_zero,ite_false,↓reduceIte,zero_add]
    rw[mu,sum_ite_eq', if_pos (mem_univ _)] at he' --  -- tune unfolding ring.B.Caution macro.
    rw[Hs0] at he'; linarith only [he']
 apply (sum_le_sum (g:=g') (fun k _=>?_)).trans; swap
 · unfold g'; split; exact le_rfl; exact H' k
 rw[ht']; change C0*(2*B+B^2)≤C0*(2*α+α^2); gcongr
#print axioms billQ
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
