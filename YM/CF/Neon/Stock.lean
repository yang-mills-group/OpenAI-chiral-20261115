import YM.CF.Neon.Lam
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
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
-- primary picture: rank 0 pressure (global scalar extracted separately), 3 PH weight and 4 derivatives, 4 radial. representation.H.
local notation "Yκ"=> mid P B
local notation "Xκ"=> mid N B
local notation "Ωp"=> RegBudget (mid P B)
local notation "θp"=> (Y.p)
local notation "HF"=> Scree.Hub (mid P B)
local notation "Пρ"=> S.patch.L.val
local notation "Pr"=> Roc (mid P B)
open Taxi Hope
variable (o: Site (mid P B))(E1:RegBudget (mid P B))(OG:RegBudget (mid P B))(X0:Dome)(Aζ:Skate)(Q:ℝ)(h:ℝ)
local notation "Δo"=> Cube.node o
local notation "ZK"=> Φrap Yκ o 10
local notation "C_"=> (ZK)
local notation "κr"=> ((ZK,true):Roc Yκ)
local notation "Vζ"=> G_κ θp o OG E1
local notation "EΛ"=> θG (Y:=Y) o OG Aζ
local notation "ZΛ"=> vRΦ (Y:=Y) o OG Aζ
local notation "ZΩ"=> vRψ (Y:=Y) o E1 OG Aζ
local notation "νv"=> ωX (OG ZK)
local notation "V_o"=> ((↑Y.p.order:ℝ)+1)
local notation "PhZ" z:max=> (Moto.hrζ θp z 1)
local notation "PhA:" z:max=> (Moto.trotΦ θp z A)
local notation "Φp" x:max=> (Moto.rotζ θp x)
variable (A) (hu:A≥0) (wQ:Taxi.DayT Y.p.order A)
variable (Fκ Gκ: Scree.Hub (mid P B)→ℝ)
local notation "Ων"=> Ψy o θp · Fκ A
local notation "fκ" x:max=> (Ψy o θp x Fκ A)
variable (hx:∀ i,PressB Y.p i (E1 i) h (Fκ i)) (h0:1 ≤ h)(hv: IncX primeU OG Y.p h 1)(hK:∀ i,CapZ Y.p (Fκ i) A)(zP:20 < (More (mid P B)).val) (u0:Short S Y.p (Φrap (mid P B) o 10).val.2)
variable (Vq:Axon S.patch.L.val o Y.p E1 h Q (Aζ,X0))
local notation "Pu"=> (Sauce θp A)
variable (pZ:∀ v:Site (Domain P B),(∑ i:Scree.Hub (mid P B), if v=i.val.1 then Y.p.mass i.val.2 (Fκ i) else 0)≤ Q)
local notation "TT"=> (Pu*Q)
local notation "PE" i:max=> (eno_b Y i)
local notation "cΨr"=> (PE ZΩ)
local notation "cΦr"=> (PE ZΛ)
local notation "ZΨ|" i:max=> (if i.2 then (fκ i.1) else 0)
local notation "ΛZ"=> (clan_X true (cΨr))
local notation "D'"=> (dawn_D S Y.p)
local notation "SΦ" b:max=> StackL (clan_X b (cΨr)) D'
local notation "ThQ"=> FaceP (Y:=Y) A o Fκ
open Hove Tap
local notation "XP"=> SΦ true
lemma wake_X (U:Scree.Hub Xκ)(o:Site Xκ)(t:U.val.1=node o)(F_: InkD Xκ)(P:BudgetPoint)(g:PressB P U F_ h a)(p:0≤ h):paid_M o (orbitPH (F_ 1)) P.power*h^2 ≤ 2*a:=by
 obtain ⟨V,u,K,z⟩:=g.worth; exact pinM o U _ V u t (Haro.ortho_l U F_ V (K _)) p a z
lemma sleep_E : ∀ i: HF, (i.val.1≠ node o→ ZΩ i=0) ∧ clan_X true (PE ZΩ) i= ZΩ i∧ clan_X false (PE ZΩ) i=0:=by
 intro X; refine ⟨fun q=>?_ ,rfl,rfl⟩; have he:X≠ZK:=fun z=>q (z ▸ rfl); rw [vRψ,if_neg he,if_neg q]
lemma orbit_0(K:Side):orbitPH (0: Cipher K)=0:=by ext i j; simp_rw [Haro.orbitPH,Matrix.of_apply,Prism.port_eq]; split; exact rfl; exact mul_zero _
lemma void_Z : SΦ false=0:=by
 unfold StackL; apply sum_eq_zero; intro b p; rw [(sleep_E (Y:=Y) o E1 OG Aζ b).2.2]; apply orbit_0 -- tune sleep implicit
local notation "νΨ"=> (νv • X0)
include hx h0 hv zP hu wQ pZ Vq hK u0
lemma craft_L (i:HF): fκ i ≥0:=mint_Q _ o E1 OG X0 Aζ Q h hu wQ _ hx h0 hv hK zP u0 Vq pZ i
lemma score_Ψ : Hove.jetsL o (SΦ true)= νΨ ∧ paid_M o (SΦ true) Y.p.power*h^2 ≤ 2*(Pu*Q):=by
 let J:= SΦ true; have p(i:HF):= tone_X _ o E1 OG X0 Aζ Q h hu wQ _ hx h0 hv hK zP u0 Vq i
 have hμ:= zero_le_one.trans h0; have hz :=lump_L _ o E1 OG X0 Aζ Q h hu wQ Fκ hx h0 hv hK zP u0 Vq pZ Δo; have ht(i):= craft_L _ o E1 OG X0 Aζ Q h hu wQ _ hx h0 hv hK zP u0 Vq pZ i
 let L(i:HF):= Y.p.mass i.val.2 (Ψy o Y.p i Fκ A)
 have he:(∑ i:HF,if Δo=i.val.1 then L i else 0)=∑ i:HF,L i:=by
    refine sum_congr rfl fun i h=>?_ ; by_cases q:Δo=i.val.1; rw [if_pos q]; unfold L; rw [if_neg q,Ψy,if_neg (Ne.symm q)]; exact (mul_zero _).symm
 let f(x:HF):=Haro.orbitPH (ZΩ x 1); let s:=D'; have hq:SΦ true=∑ i∈ s, f i:= rfl
 have hg:(∑ i∈ s, L i) ≤ Pu*Q:= (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>mul_nonneg (Real.exp_pos _).le (ht _))).trans ((Eq.le he.symm).trans hz)
 rw [hq]; constructor
 · rw [pub_eq,map_sum]; simp_rw [←pub_eq]; rw [sum_eq_single_of_mem ZK (mem_filter.mpr ⟨mem_univ _,u0⟩)]; rw [show jetsL o _=_ from (p ZK).2.2.2 u0 |>.2.2,if_pos rfl]; intro i q z; unfold f; rw [show jetsL _ _=_ from ((p i).2.2.2 ((mem_filter.mp q).2)).2.2, if_neg z]
 have hc(P:Finset HF):paid_M o (∑ i∈ P,f i) Y.p.power≤ ∑ i∈ P,paid_M o (f i) Y.p.power:=by
    induction P using Finset.induction with
    | empty=> simp only [sum_empty]; unfold paid_M paidX; simp [Hove.pinF,Function.uncurry]
    | insert i v t u=> rw [sum_insert t,sum_insert t]; exact (paidp_sum ..).trans (add_le_add le_rfl u)
 apply le_trans (mul_le_mul_of_nonneg_right (hc _) (sq_nonneg _)); rw [sum_mul]; apply le_trans ?_ (mul_le_mul_of_nonneg_left hg (by norm_num)); rw [mul_sum]; refine sum_le_sum fun j _=>?_
 by_cases tj:j.val.1= Δo
 · exact (wake_X h j o tj _ θp (p j).1 hμ).trans (mul_le_mul_of_nonneg_left (tonne_ge _ _ _ (ht _)) (by norm_num))
 rw [show f j=0 from ?_]; swap; · unfold f; rw [(sleep_E (Y:=Y) o E1 OG Aζ j).1 tj]; exact orbit_0 ..
 have he:paid_M o 0 Y.p.power=0:=by unfold paid_M paidX; simp [Hove.pinF,Function.uncurry]
 rw [he,zero_mul]; exact mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le (ht j)) -- tune
-- output inclusion Knot receipt sum TRUE over coarse aligned. 
lemma spark_X (X:Site (Domain N B))(p':S.ratio.parent Δo=X) : (∑ i:Pr with S.ratio.parent i.1.val.1=X, Y.p.mass i.1.val.2 (ThQ i))≤ Pu*Q :=by
 have hx0:=lump_L _ o E1 OG X0 Aζ Q h hu wQ _ hx h0 hv hK zP u0 Vq pZ Δo; apply le_trans ?_ hx0; rw [sum_filter,Fintype.sum_prod_type]; apply sum_le_sum; intro k _; rw [Fintype.sum_bool]; simp only [FaceP,Bool.false_eq_true,ite_false,ite_true,BudgetPoint.mass,mul_zero,ite_self,add_zero]
 by_cases p:k.val.1=Δo
 · simp_rw [if_pos (show Δo=k.val.1 from p.symm),p,p',ite_true]; exact le_rfl
 simp [Ψy, p,Ne.symm p] -- tune
omit hx h0 hv zP hu wQ pZ Vq hK u0
lemma soar_Q(i:Pr)(q: actionZ (PE ZΩ) i ≠0)(P':Site (Domain N B))(p':S.ratio.parent Δo=P'): S.ratio.parent i.1.val.1=P':=by
 unfold actionZ at q; split at q; swap; · exact False.elim (q rfl)
 by_contra h; exact q ((sleep_E (Y:=Y) o E1 OG Aζ _).1 (fun z=>h (congrArg S.ratio.parent z |>.trans p'))) -- binder._
lemma nil_P(i:Pr)(z:i≠κr): actionZ (PE ZΛ) i=0:=by unfold actionZ; split; rename_i v; change (ZΛ i.1)=0; rw [vRΦ,if_neg (show i.1≠ ZK from fun h=>z (Prod.ext h v))]; rfl
end YM.CF.Neon
