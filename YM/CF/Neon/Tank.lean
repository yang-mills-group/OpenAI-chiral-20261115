import YM.CF.Neon.Hick
import YM.CF.Coal.Vice
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t_aux z g A B':ℝ} {j k k' m n l:ℕ}
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
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
-- primary picture: rank 0 pressure (global scalar extracted separately), 3 PH weight and 4 derivatives, 4 radial. representation.H.
local notation "Xκ"=> mid N B
local notation "Ωp"=> RegBudget (mid P B)
open Mew Taxi Hope
-- process real gauge Yearn to K normalization. rooted support wave. Cost short C.P broad Vv post.Sector. 
variable (F:Pilot)(Z:Pluck R){H:Muster G S x d T}{W:GivenX V U}{q q':Chi}
variable {q0:ℝ}(Tp:Ids (mid N B))(Wt:Aura (mid N B)→ Copy (mid N B))(b v0 v':ℝ)(QΦ:Skate)(Pξ:ℂ)
variable (Vκ:ℝ)(Ψ: DayT X.p.order Vκ)(uc:0 ≤ Vκ)
variable (Υ:Gala X.p.power X.p.order 100 x 3)(hμ:10 ≤ X.p.B)(hK:X.p.B=radiusB x)(hk:X.p.threshold=temp x)(he:1 ≤ radiusB x)(hp:20 < (More (mid N B)).val)(hP:3 ≤ (mid N B).val)
-- stencil size cover
open Coal
variable (o:Site (mid N B))(h aK bF:ℝ)(hT:1 ≤ h)(F0:Pax (mid N B))(OpZ:Bool→Op (Single (mid N B)))(hq:X.p.order=i)(hX:X.p.power=p)(M: Muse_B (X:=X) (H:=H) (i:=i) (p:=p) (l:=l) h o aK bF OpZ F0)
variable (hi:OpZ false=0) -- opacity.Q.Vra
local notation "Zκ"=> ωK (H:=H) o
local notation "Xq"=> keep_A (H:=H)
local notation "ζρ"=> (Roc (mid P B) × Aura (mid N B))
local notation "Pζ"=> (Φrap (mid N B) o (10*((l+300)*radiusB x)))
local notation "Оп"=> (OpZ true)
local notation "PΨ"=> pay_Y (N:=N) (B:=B) (OpZ true)
local notation "Du"=> (deck_K i p (10*(l+300))*(Oath.stakeH i*h^2*Hove.paid_M o (OpZ true) p))
abbrev PKard(l:ℕ):ℕ:= (2*(10*(l+300))+1)^4
local notation "TLo"=> PKard l
variable (L0:ℕ)(pQ:(PKard l)^3 < L0)
include hK he
variable (l) -- l explicit changes ABI. remove
lemma moon_P : coverNumber X.p.B (Pζ).val.2 ≤ TLo:=by
 rw [hK]; unfold PKard; change coverNumber (radiusB x) (Lattice.halo _ _)≤ _; rw [← Nat.mul_assoc 10,two_mul]; exact Corona.tile _ _ _ he
omit hK he
local notation "Ek"=> Hove.jetsL o (Оп)
local notation "YP"=> (Real.exp (X.p.supportExponent*(PKard l:ℝ))* Du)
local notation "AY"=> (aK+(YP))
local notation "KP"=> (Real.exp ((X.p.supportExponent+1+1)*(PKard l:ℝ))* bF)
local notation "Tκ"=> (node o)
local notation "Kρ"=> Extr_h L0 X.p Vκ
variable {Fp:ℝ}
include M hT Ψ uc Υ hμ hK hk he hp hP hi pQ
#check moon_P
abbrev Pearl_ := pump_I X.p ({true}:Finset Bool) (fun _:Bool=>Pζ) (fun b=>pay_Y (N:=N) (B:=B) (OpZ b))
#check Pearl_
local notation "Ψη"=> Pearl_ (X:=X) (x:=x) l o OpZ
set_option maxHeartbeats 1050000 in
lemma pearl_X :∃ F K t, Ice L0 o X.p h (Δv X.p Vκ*YP) (Kρ*YP) YP (Ψη) F K t (0,Ek):=by
 have hq':= M.bend true; have ht':0 ≤ h:=zero_le_one.trans hT; have h0:0 ≤ Du:= (eraF _ _ hq' ht' 1 (ping_f _ _)).grade
 let I:=({true}:Finset Bool); let J(b:Bool):=Pζ; let U(b:Bool):= pay_Y (N:=N) (B:=B) (OpZ b); have ht(P:Bool)(pU:P∈I):PressB X.p Pζ (U P) h Du:=mem_singleton.mp pU ▸ hq'
 have hP': coverNumber X.p.B (Pζ).val.2 ≤ PKard l:= moon_P l hK he o
 have hv: (∑ iβ∈ I,X.p.mass (J iβ).val.2 Du)≤YP:=by rw [show I={true} from rfl,sum_singleton]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hP') X.p.exponent_pos.le)) h0
 have hh: chose L0 X.p Pζ:= lt_of_le_of_lt (Nat.pow_le_pow_left hP' _) pQ
 let T':= hand_W o X.p h I J U (fun _=>Du) YP (fun b p=> ht b p) (fun i _=>rfl) hT hv L0 Vκ Ψ uc Υ hμ hk he hp hP
 let GΦ:= Eφ o X.p I J U L0; let GΨ:= Eκ o X.p I J U L0
 let L:= I; have htI:firth X.p L0 I J={true}:=filter_true_of_mem fun _ _=>hh
 have heG:GΦ=0:=by
    unfold GΦ Eφ; rw [htI,sum_singleton]; funext a b; unfold Moto.tooth; rw [show Taxi.lifeH (U true)=(fun _: Pane Xκ=>0) from funext fun i=>bail_m _ _]; change iteratedFDeriv ℝ 2 (fun _:tangD Xκ=>(0:ℂ)) _ _=0; rw [iteratedFDeriv_const_of_ne (by omega:(2:ℕ)≠ 0)]; rfl
 have heΨ:GΨ= Ek:=by unfold GΨ Eκ U; rw [htI,sum_singleton,hail_K]
 let s:= Eφ o X.p I J U L0; let uΨ:=Eκ o X.p I J U L0; have hv:s = 0:=heG; have hΞ:uΨ= Ek:=heΨ; have hx:∃ F K t,Ice L0 o X.p h (Δv X.p Vκ*YP) (Kρ*YP) YP (Ψη) F K t (s,uΨ):=⟨_,_,_,T'⟩; exact hv ▸ hΞ ▸ hx
open Vow
lemma shaft_P(k:Orbit (mid N B)): (∑ z:Bool,Vow.march X.p (lagE Pζ) (oV (pay_Y (OpZ z))) k)= (Ψη k):=by
 unfold Pearl_ pump_I; rw [sum_singleton,Fintype.sum_bool,hi,show (pay_Y (N:=N) (B:=B) 0: InkD Xκ)=0 from ?hp,show Vow.march X.p (lagE Pζ) (oV (0:InkD Xκ)) k=0 from ?h,add_zero]; case hp=>
       let P:=(0:Op (Single Xκ)); let F:= pay_Y (N:=N) (B:=B); have ht:= φ_add (N:=N) (B:=B) P P; rw [show P+P=P from add_zero _] at ht; exact add_left_cancel (show F P+F P=F P+0 from ht.symm.trans (add_zero _).symm)
 case h=> unfold Vow.march; split; exact rfl; rfl
lemma theta_B: ∃ G K Tv GΦ GΨ, Ice L0 o X.p h (Δv X.p Vκ*(AY)) (Kρ*(AY)+KP) AY (coldE X.p F0) G K Tv (GΦ,GΨ) ∧ ‖GΦ‖ ≤ aK ∧ ‖GΨ-Ek‖*h^2 ≤(2*peka_H X.p.power)*aK:=by
 let D:=Zκ; let Ko:=Xq; obtain ⟨Ev,ψ,Az,hx,v,u,hY,h_W⟩:= M.well; let P':= lagE Pζ
 have hu0(i)(p:i∈ D):(Ko i).val.1=node o:= (mem_filter.mp p).2
 let Z:= hand_W o X.p h D Ko Ev Az aK u hu0 hT hY L0 Vκ Ψ uc Υ hμ hk he hp hP
 obtain ⟨FΨ,KΨ,TΨ,hp'⟩:= pearl_X l Vκ Ψ uc Υ hμ hK hk he hp hP o h aK bF hT F0 OpZ M hi L0 pQ
 let Hψ:=Ice.plan_ADD o L0 Z hp' (zero_le_one.trans hT)
 have hP': coverNumber X.p.B (Pζ).val.2 ≤ PKard l:= moon_P l hK he o
 have hs:0≤ bF:= (hx.1 P').trans_eq (Pi.single_eq_same ..)
 let R0:=X.p.supportExponent+1+1
 have hpz(K':Seat (mid N B)): tallB (Pi.single P' bF) X.p.B (X.p.supportExponent+1+1) K' ≤ KP:=by
    unfold tallB; by_cases hx:K'∈P'.val
    · rw [sum_eq_single_of_mem P' (mem_filter.mpr ⟨mem_univ _,hx⟩),Pi.single_eq_same,mul_comm]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hP') (by positivity [X.p.exponent_pos]))) hs; intro j _ g; rw [Pi.single_eq_of_ne g,zero_mul] -- syntax positivity
    rw [sum_eq_zero]; exact mul_nonneg (Real.exp_pos _).le hs; intro j g; rw [Pi.single_eq_of_ne (fun t:j=P'=>hx (t ▸ (mem_filter.mp g).2)),zero_mul]
 have hv:= Ice.hike_P o X.p h L0 Hψ hx (show SparF o X.p (Pi.single P' bF) L0 from (fun i h=> by
    by_cases y:i=P'; swap; · exact False.elim (h (Pi.single_eq_of_ne y _))
    subst i; exact ⟨hP'.trans (le_trans ((Nat.le_self_pow (by omega) _).trans pQ.le) (Nat.le_add_right ..)),(Pζ).property⟩)) KP hpz v (coldE X.p F0) ?p
 case p=>
    intro k v; change coldE X.p F0 k=(pump_I X.p D Ko Ev k+ _) +fuelV X.p ψ k; rw [←h_W k v,shaft_P l Vκ Ψ uc Υ hμ hK hk he hp hP o h aK bF hT F0 OpZ M hi L0 pQ]; rfl
 let K':= (quest_B o X.p h D Ko Ev Az aK u hu0 hT hY (firth X.p L0 D Ko) (filter_subset ..))
 rw [mul_add (Δv X.p Vκ),mul_add (Extr_h L0 X.p Vκ) aK YP]
 let W:= Eφ o X.p D Ko Ev L0; let Ep:= Eκ o X.p D Ko Ev L0; refine ⟨_,_,_,W+0,Ep+Ek,hv,?_,?_⟩
 · rw [add_zero]; exact K'.1
 rw [add_sub_cancel_right]; exact K'.2
end YM.CF.Neon
