import YM.CF.Coal.Vice
import YM.CF.Moto.Band
import YM.CF.Moto.Kearn
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
abbrev ArcΦ:= Skate × Dome
def pillar(o: Site (mid N B))(X:InkD (mid N B))(P:BudgetPoint):ArcΦ:= (tooth (node o) P X,Hove.jetsL o (orbitPH (X 1)))
structure Axon (L:ℕ)(o:Site (mid N B))(p:BudgetPoint)(F:RegBudget (mid N B))(h v:ℝ)(X:ArcΦ):Prop where
 vest:IncX primeU F p h v
 site(i:Scree.Hub (mid N B))(g:i.val.1≠Cube.node o): F i=0
 flair(i:Scree.Hub (mid N B))(g:Moto.chose L p i): Taxi.lifeH (F i) 1=0∧ pillar o (F i) p=(if i=Φrap (mid N B) o 10 then X else 0)
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
abbrev pup_Q (x:HF) (i:RegBudget Yκ): Prop := x.val.1=Cube.node o
abbrev G_κ (p:BudgetPoint)(o:Site Yκ)(F0 F: RegBudget Yκ)(x:HF):InkD Yκ := -- note unused p o
 F x * foot_ (F0 x)
local notation "Vζ"=> G_κ θp o OG E1
abbrev θG := Moto.plateZ Δo Y.p ((ωX (OG (Φrap Yκ o 10))) • Aζ)
local notation "EΛ"=> θG (Y:=Y) o OG Aζ
abbrev vRψ (i:HF): InkD Yκ := if i= Φrap Yκ o 10 then Hope.linen θp i (G_κ θp o OG E1 i- θG (Y:=Y) o OG Aζ) else if i.val.1=node o then Hope.linen θp i (G_κ θp o OG E1 i) else 0
abbrev vRΦ(i: HF): InkD Yκ:= if i=Φrap Yκ o 10 then Hope.linen θp i (θG (Y:=Y) o OG Aζ) else 0
local notation "ZΛ"=> vRΦ (Y:=Y) o OG Aζ
local notation "ZΩ"=> vRψ (Y:=Y) o E1 OG Aζ
local notation "νv"=> ωX (OG ZK)
abbrev Ψy(o:Site Yκ)(P:BudgetPoint)(x:HF)(g:HF→ℝ)(A:ℝ):ℝ:= if x.val.1=node o then Moto.rotζ P (hrζ P (g x) 1+ Moto.trotΦ P (hrζ P (g x) 1) A) else 0
local notation "V_o"=> ((↑Y.p.order:ℝ)+1)
local notation "PhZ" z:max=> (Moto.hrζ θp z 1)
local notation "PhA:" z:max=> (Moto.trotΦ θp z A)
local notation "Φp" x:max=> (Moto.rotζ θp x)
variable (A) (hu:A≥0) (wQ:Taxi.DayT Y.p.order A)
abbrev CapZ(P:BudgetPoint)(x A:ℝ):Prop:= let C:=hrζ P x 1 + Moto.trotΦ P (hrζ P x 1) A; ((P.order:ℝ)+1)* C≤1/4 ∧ rotζ P C ≤1
lemma cap_L (P:BudgetPoint)(u:0≤A)(s:ℝ)(z:CapZ P s A)(p:e≤ s): CapZ P e A:=by
 let G(t:ℝ):= hrζ P t 1; let c:=G 1; let V:= trotΦ P 1 A; have h0:0≤c:=by unfold c G hrζ; positivity
 have h:0≤V:=by unfold V trotΦ tollV; have hκ:= AnalyticBridge.VerifiedReset.pair_nonneg SU.group P; positivity
 have hl(t:ℝ):G t+trotΦ P (G t) A=(c+V*c)*t:=by
    unfold V G c G trotΦ hrζ tollV; ring
 change ((P.order:ℝ)+1)*(G s+trotΦ P (G s) A)≤1/4 ∧ rotζ P (G s+trotΦ P (G s) A)≤1 at z; change ((P.order:ℝ)+1)*(G e+trotΦ P (G e) A)≤1/4∧ rotζ P (G e+trotΦ P (G e) A)≤1; rw [hl] at z; rw [hl]; have a:= mul_le_mul_of_nonneg_left p (add_nonneg h0 (mul_nonneg h h0)); refine ⟨(mul_le_mul_of_nonneg_left a (by positivity)).trans z.1, le_trans ?_ z.2⟩; unfold rotζ; gcongr
-- tan projection. at auxiliary X.K. s.mass.W. Control Expo.IR.
variable (Fκ Gκ: Scree.Hub (mid P B)→ℝ)
local notation "Ων"=> Ψy o θp · Fκ A
local notation "fκ" x:max=> (Ψy o θp x Fκ A)
variable (hx:∀ i,PressB Y.p i (E1 i) h (Fκ i)) (h0:1 ≤ h)(hv: IncX primeU OG Y.p h 1)(hK:∀ i,CapZ Y.p (Fκ i) A)(zP:20 < (More (mid P B)).val) (u0:Short S Y.p (Φrap (mid P B) o 10).val.2)
variable (Vq:Axon S.patch.L.val o Y.p E1 h Q (Aζ,X0))
lemma tonne_ge (P: BudgetPoint)(U:Scree.Hub N)(x:ℝ)(h:0≤x):x≤ P.mass U.val.2 x:= le_mul_of_one_le_left h (Real.one_le_exp (mul_nonneg P.exponent_pos.le (Nat.cast_nonneg _)))
lemma ζ_geP (s:ℝ)(vB:0 ≤ A)(p:0≤ s):0≤ PhA:s:=by unfold Moto.trotΦ Taxi.tollV; have hκ:= AnalyticBridge.VerifiedReset.pair_nonneg SU.group θp; positivity
local notation "λc" x:max=> (Φp ((PhA:(PhZ x))+(PhZ x))) -- order plus reverse
include hx h0 hv hu wQ hK Vq zP u0
lemma tone_X(i:HF): PressB θp i (ZΩ i) h (fκ i) ∧ PressB θp i (ZΛ i) h (fκ i)∧(∀ w:Pane Yκ,pingS Y.p.threshold i.val.2 w→ (exp (ZΩ i w) -1)+(exp (ZΛ i w) -1)= Vζ i w) ∧ (Short S θp i.val.2→ lifeH (ZΩ i) 1=0∧ tooth i.val.1 θp (ZΩ i)=0∧ jetsL o (orbitPH (ZΩ i 1))=(if i= (Φrap Yκ o 10) then νv • X0 else 0)):=by
 have h':=hx i; have h2:= zero_le_one.trans h0
 let L(i:HF):=hrζ θp (Fκ i) 1
 have hH(i:HF):PressB θp i (OG i) h 1:=by
    obtain ⟨G,hG,t⟩:=hv.weight; have hρ(i):= (Taxi.eraF _ _ (hG i) h2 1 (ping_f θp i.val.2)).grade
    apply hi_p (hG _); refine (tonne_ge θp i (G i) (hρ i)).trans ?_; have hh:=t i.val.1; rw [←Finset.sum_filter] at hh; exact (Finset.single_le_sum (fun j _=> (hρ j).trans (tonne_ge θp j (G j) (hρ j))) (show i∈ univ.filter (fun j:HF=>i.val.1=j.val.1) from mem_filter.mpr ⟨mem_univ _,rfl⟩)).trans hh
 let W(i):=virtue_w (hx i) (hH i) h2
 have hV:(Vζ i)=(E1 i)*foot_ (OG i):=rfl
 have uL(i:HF):0 ≤ L i:= (eraF _ i (W i) h2 1 (ping_f θp i.val.2)).grade
 have hp(i:HF):0 ≤ trotΦ Y.p (L i) A:=ζ_geP _ _ hu (uL i) -- tune
 have hk(i:HF)(p:i.val.1=Δo):V_o*(L i+ PhA:(L i))≤1/4 ∧ Φp (L i+PhA:(L i)) ≤1∧ 0 ≤ fκ i :=by
    have he:= hK i; unfold Ψy; rw [if_pos p]; refine ⟨he.1,he.2,?_⟩; unfold rotζ; exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (add_nonneg (uL _) (hp i)))
 -- AC Canonical surgery.
 by_cases hi:i=ZK
 · subst i; let P':= ZK; let S_κ:=L P'; let E0:=G_κ Y.p o OG E1 P'; obtain ⟨hA,hΨ⟩:= Vq.flair P' u0; have ht:tooth P'.val.1 θp (E1 P')=Aζ:=by rw [if_pos rfl] at hΨ; exact congrArg Prod.fst hΨ
   have hx':plateZ P'.val.1 θp (tooth P'.val.1 θp E0)= θG (Y:=Y) o OG Aζ:= congrArg (plateZ P'.val.1 θp) ((stake_s0 h' (hH P') h2 hA).2.1.trans (congrArg (νv • ·) ht))
   let Z' :=tour_V h' (hH P') h0 A wQ hu (show Lattice.halo 2 {P'.val.1}⊆ P'.val.2 from Corona.halo_mono (by norm_num: (2:ℕ)≤ 10) (Subset.refl _)) hA zP
   have ht':0 ≤ V_o:=by positivity
   obtain ⟨hz,hv,u⟩:= hk P' rfl
   have hz1:PhA:(L P')≤ L P'+PhA:(L P'):=le_add_of_nonneg_left (uL _)
   obtain ⟨T,Po,U,W⟩:= Z' ((mul_le_mul_of_nonneg_left hz1 ht').trans hz) hz ((show rotζ θp (PhA:(L P'))≤ _ from mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz1 ht') (by positivity)).trans hv) hv
   have hp: ZΩ P'=Hope.linen θp P' ((E1 P')*foot_ (OG P')- plateZ P'.val.1 θp (tooth P'.val.1 θp E0)):=by rw [vRψ,if_pos rfl,hx']
   have hb: ZΛ P'=Hope.linen θp P' (plateZ P'.val.1 θp (tooth P'.val.1 θp E0)):=by rw [vRΦ,if_pos rfl,hx']
   change PressB θp P' (ZΩ P') h (fκ P') ∧ PressB θp P' (ZΛ P') h (fκ P')∧(∀ i:Pane Yκ,pingS Y.p.threshold P'.val.2 i → exp (ZΩ P' i)-1+(exp (ZΛ P' i)-1)= Vζ P' i) ∧ (Short S θp P'.val.2→ lifeH (ZΩ P') 1=0∧ tooth P'.val.1 θp (ZΩ P')=0∧ jetsL o (orbitPH (ZΩ P' 1))=(if P'= (C_) then νv • X0 else 0)) -- use one
   rw [hp,hb,Ψy,if_pos rfl]
   refine ⟨U.paid,hi_p T.paid (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz1 ht') (by positivity)),fun v p=>?_,fun _=>⟨U.drop,U.jewel,?_⟩⟩
   · rw [Po.loaded _ p, T.loaded _ p]; exact sub_add_cancel ..
   rw [if_pos rfl,W,pub_eq,map_smul,← pub_eq]; rw [if_pos rfl] at hΨ; exact congrArg (fun z=> νv • (z:ArcΦ).2) hΨ
 unfold Ψy vRψ vRΦ; rw [if_neg hi,if_neg hi]; by_cases hg:i.val.1=Δo; swap
 · rw [if_neg hg, if_neg hg,hV,Vq.site i hg,zero_mul]
   refine ⟨Vale.rinse _ _ _,Vale.rinse _ _ _,fun _ _=>?_,fun _=>?_⟩; · simp
   -- stillQ tooth computed at its own root; tooth zero all
   rw [if_neg hi]; refine ⟨rfl,?_,(stillQ o Y.p).2.2⟩
   funext ℓ u; change iteratedFDeriv ℝ 2 (fun _: tangD Yκ=>(0:ℂ)) 0 _=0; rw [iteratedFDeriv_const_of_ne (by omega:(2:ℕ)≠ 0)]; rfl
 obtain ⟨p1,p2,e⟩:= hk i hg
 rw [if_pos hg, if_pos hg, hV]; let O:= (E1 i)* foot_ (OG i)
 have hb:0 ≤ V_o:=by positivity
 have ht:L i≤ L i+PhA:(L i):=le_add_of_nonneg_right (hp i)
 let Pk:= herve (W i) h0 ((mul_le_mul_of_nonneg_left ht hb).trans p1) ((show rotζ θp (L i)≤ _ from mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hb) (by positivity)).trans p2)
 refine ⟨hi_p Pk.paid (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hb) (by positivity)),hi_p (Vale.rinse i θp h) (by simpa only [Ψy,hg,if_pos] using e),fun v p=>?_,fun p=>?_ ⟩ -- tune hg simpa if_true
 · rw [Pk.loaded _ p]; simp
 obtain ⟨a,q⟩:= Vq.flair _ p
 rw [if_neg hi]; rw [if_neg hi] at q
 obtain ⟨he,w,k⟩:= stake_s0 h' (hH i) h2 a; obtain ⟨b,t,e⟩:= Pk.mute he
 refine ⟨b, t.trans (w.trans (by rw [hg, show tooth Δo θp _=0 from congrArg Prod.fst q,smul_zero])),?_⟩; rw [e,k,pub_eq,map_smul,←pub_eq,show jetsL o (orbitPH (E1 i 1))=0 from congrArg Prod.snd q,smul_zero]
end YM.CF.Neon
