import YM.CF.Neon.Stock
import YM.CF.Hype.Yom
import YM.CF.Mew.Pot
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
abbrev SparF(o:Site (mid N B))(P:BudgetPoint)(q:Aura (mid N B)→ℝ)(L:ℕ):Prop:=∀ i:Aura (mid N B),q i≠0 → coverNumber P.B i.val ≤ L+1∧ Cube.node o∈ i.val
structure Ice (L:ℕ)(o:Site (mid N B))(P: BudgetPoint)(h Eμ Kμ Cμ:ℝ)(F:Copy (mid N B))(K_:RegBudget (mid N B))(Kv:Cusp (mid N B))(t:ℂ)(X:ArcΦ): Prop where
 axle: Axon L o P K_ h Eμ X
 phase: ‖t‖≤ Cμ
 stout:∀ x: Aura (mid N B), Cube.node o∉ x.val→ Kv x=0 -- tune
 grant:∃ q:Aura (mid N B)→ℝ,Anuk Kv q P h∧(∀ i:Seat (mid N B),tallB q P.B (P.supportExponent+1+1) i ≤ Kμ) ∧ SparF o P q L
 wear(U:Orbit (mid N B)): FleetS P.threshold U.1→ F U=t • (1:Cipher Θ)+exponentL P K_ U.1+ fuelV P Kv U
local notation "Tκ"=> Cube.node o
local notation "Cκ"=> (Φrap Θ o 10)
variable {ι:Type*}[DecidableEq ι]
variable (I:Finset ι)(D:ι→ Scree.Hub (mid N B))(E_:ι→InkD (mid N B))(W_:ι→ℝ)(dP:ℝ)
variable (u:∀ i∈I,PressB p0 (D i) (E_ i) h (W_ i)) (g_:∀ i∈ I,(D i).val.1=Cube.node o)(ht:1 ≤ h)(V':(∑ i∈I,p0.mass (D i).val.2 (W_ i)) ≤dP)
variable (L0:ℕ)(Vκ:ℝ)(Ψ: DayT p0.order Vκ)(uK:0 ≤ Vκ)
variable (Υ:Gala p0.power p0.order 100 x 3)(hu:10 ≤ p0.B)(hk:p0.threshold=temp x)(he:1 ≤ radiusB x)(hp:20 < (More (mid N B)).val)(hP:3 ≤ (mid N B).val)
local notation "Ω"=> (firth p0 L0 I D)
local notation "Lρ"=> Eφ o p0 I D E_ L0
local notation "ζp"=> Eκ o p0 I D E_ L0
local notation "PΨ"=> (Tκ)
local notation "ΘC"=> (Z_b o p0 I D E_ L0)
local notation "TP" i:max=> crest_G p0 o (E_ i)
local notation "TΦ" i:max=> crest_Y o (E_ i)
abbrev ρH(i:ι):InkD Θ:= TP i+ TΦ i
local notation "F_"=> (ρH o p0 E_)
local notation "Vτ"=> sunY I (box_L o p0 I D L0) (εL o p0 I D E_ L0)
local notation "Yρ"=> conY o p0 I D E_ L0
local notation "A'"=> Real.exp p0.supportExponent * |Kprice p0 1 Vκ|
local notation "Sκ"=> ((1+ Real.exp p0.supportExponent* |Kprice p0 1 Vκ|)*dP)
local notation "V_q"=> sunY Ω (fun _:ι=>Cκ) F_
abbrev silver_P: RegBudget Θ:= sunY Ω (fun _:ι=>Cκ) F_
local notation "Zρ"=> silver_P o p0 I D E_ L0
local notation "Qρ"=> hypeE E_ Ω
local notation "Wμ"=> (|jewelX p0 Vκ 1| *Real.exp ((p0.supportExponent+1+1)*(L0+1:ℝ))*dP)
def glowP (p:BudgetPoint)(V:ℝ):ℝ:= 1+ Real.exp p.supportExponent * |Kprice p 1 V|
local notation "Γ"=> p0.B
include u g_ ht V' Υ hu hk he hp hP Ψ uK
private lemma V_pk (P:BudgetPoint): 1 ≤ P.power:=by -- include P? check
 have hx:=P.power_ge; omega
local notation "Wσ"=> (fun i:ι=> Kprice p0 (W_ i) Vκ)
local notation "ΔX"=> (Real.exp p0.supportExponent * |Kprice p0 1 Vκ| *dP)
local notation "KΦ"=> (Cκ)
lemma river_W(i:ι)(v:i∈ I):PressB p0 Cκ (F_ i) h (Kprice p0 (W_ i) Vκ)∧lifeH (F_ i) 1=0∧ pillar o (F_ i) p0= pillar o (E_ i) p0:=by
 let K:1 ≤ p0.power:= Nat.le_trans (by decide) p0.power_ge
 obtain ⟨hz,hv,hg,hT,H⟩:= wallet (E_ i) _ o (g_ i v) p0 (u i v) ht Vκ Ψ uK Υ he hk hp hP K
 have hU:= wheel_Y (E_ i) _ o (g_ i v) p0 (u i v) ht Υ he hk K; let A:= (TP i); let B':= (TΦ i)
 have h0:= zero_le_one.trans ht; have hs:= (eraF _ _ (u i v) h0 _ (ping_f p0 _)).grade
 let j:= Θ; have hp:pillar o (A+B') p0=(tooth Tκ p0 A,jetsL o (orbitPH (B' 1))):=by
    refine Prod.ext ?_ ?_
    · let T:= (Cκ).val.1; change tooth T p0 (A+B')=tooth T p0 A; let Vt: PressB p0 Cκ (A+B') h _:= prop_add p0 Cκ hz hU
      have ht: tooth T p0 A = tooth T p0 (A+B')-tooth T p0 B':=by nth_rw 1 [← add_sub_cancel_right A B']; exact hut_p Vt hU h0
      apply Eq.symm; refine ht.trans ?_; rw [show tooth T p0 B'=0 from ?_,sub_zero]; funext x y; unfold Moto.tooth; rw [show lifeH B'=(fun _:Pane j=>0) from funext hv]; change iteratedFDeriv ℝ 2 (fun _:tangD _=>(0:ℂ)) _ _=0; rw [iteratedFDeriv_const_of_ne (by omega:(2:ℕ)≠ 0)]; rfl
    change jetsL o (orbitPH ((A+B') 1))=jetsL o (orbitPH (B' 1)); apply congrArg; let Q':= orbitPH (A 1); have h0:Q'=0:=hol_l _; have hm:= tail_K ((A+B') 1) (A 1); rw [show (A+B') 1-A 1=B' 1 from add_sub_cancel_left _ _,show orbitPH (A 1)=0 from h0,sub_zero] at hm; exact hm.symm
 refine ⟨hi_p (prop_add _ _ hz hU) (show _ ≤ Kprice p0 (W_ i) Vκ from ?_), ?_, hp.trans (Prod.ext hT H)⟩
 · unfold Kprice; linarith
 change Pastry.pane (A 1+B' 1)=0; rw [hull_sum,show Pastry.pane (A 1)=0 from hg, show Pastry.pane (B' 1)= 0 from hv _,add_zero]
omit u g_ ht V' Υ hu hk he hp hP Ψ uK
lemma Pill_F (U:Scree.Hub Θ)(F T:InkD Θ)(p:PressB p0 U F h d)(v:PressB p0 U T h g)(ht:0≤ h): pillar o (F+T) p0=pillar o F p0+pillar o T p0:=by
 refine Prod.ext ?_ ?_
 · funext i j; unfold pillar; have ht:Taxi.lifeH (F+T) ∘ increment 1= Taxi.lifeH F ∘ increment 1+Taxi.lifeH T ∘ increment 1:=rfl; change iteratedFDeriv _ _ _ _ _= tooth _ _ F i j+tooth _ _ T i j; rw [ht,iteratedFDeriv_add_apply (heatP p (by assumption)) (heatP v (by assumption))]; rfl -- shadow p var
 change jetsL o (orbitPH ((F+T) 1)) = jetsL o (orbitPH (F 1))+ jetsL o (orbitPH (T 1)); have hm:= tail_K ((F+T) 1) (T 1); rw [show (F+T) 1-T 1=F 1 from add_sub_cancel_right _ _] at hm; rw [show orbitPH ((F+T) 1)=_ from ((eq_sub_iff_add_eq).mp hm).symm,pub_eq,map_add,←pub_eq,←pub_eq] -- tune Lean Eq
lemma Pill_0(P:BudgetPoint): pillar o (0:InkD Θ) P=0:= by have ht:= stillQ o P; exact Prod.ext ht.2.1 ht.2.2
lemma α_sum(F:ι→ InkD Θ)(p:∀ i∈I,PressB p0 Cκ (F i) h (W_ i))(ht:0 ≤ h): pillar o (∑ i∈I,F i) p0=∑ i∈I,pillar o (F i) p0:=by
 induction I using Finset.induction with
 | empty=> rw [sum_empty,sum_empty]; exact Pill_0 ..
 | insert i X t u=>
    have hv(j)(v:j∈ X):= p j (mem_insert_of_mem v); rw [sum_insert t,sum_insert t,Pill_F _ _ _ _ _ _ (p i (mem_insert_self ..)) (prop_sum X _ _ _ h Cκ hv) ht, u hv]
lemma Axon_add {E' F':RegBudget (mid N B)}{z z':ArcΦ}{h u v:ℝ} (p:Axon L0 o p0 E' h u z)(q: Axon L0 o p0 F' h v z')(ht:0 ≤ h): Axon L0 o p0 (E'+F') h (u+v) (z+z'):=by
 obtain ⟨A,u,w⟩:= p.vest.weight; obtain ⟨C,k,v⟩:=q.vest.weight
 refine ⟨Larch.add_v p0 _ _ p.vest q.vest,fun i r=>?_,fun i r=>?_⟩
 · rw [Pi.add_apply,p.site i r,q.site i r,add_zero]
 obtain ⟨x,H⟩:= p.flair i r; obtain ⟨y,hb⟩:= q.flair i r; refine ⟨?_,?_⟩
 · change Pastry.pane (E' i 1+F' i 1)=0; rw [hull_sum,show Pastry.pane (E' i 1)=0 from x, show Pastry.pane (F' i 1)=0 from y,add_zero]
 rw [Pi.add_apply,Pill_F _ _ _ _ _ _ (u _) (k _) ht,H,hb]; split_ifs; rfl; exact add_zero _
include u g_ ht V' Υ hu hk he hp hP Ψ uK
lemma ray_Φ : Axon L0 o p0 Zρ h ΔX (Lρ,ζp):=by
 let P(i)(p):=river_W _ _ _ _ _ _ _ dP u g_ ht V' Vκ Ψ uK Υ hu hk he hp hP i p -- match I→input ABI.
 let l(i):= Kprice p0 (W_ i) Vκ; have h0:=zero_le_one.trans ht; have hf(i)(p:i∈ I):= (P i p).1; have hz(i)(p:i∈ I):0 ≤ l i:= (eraF _ _ (hf i p) h0 1 (ping_f p0 _)).grade; have ht'(i)(p:i∈I):0 ≤ W_ i:= (eraF _ _ (u i p) h0 1 (ping_f p0 _)).grade
 let L:= Ω; have H':Ω⊆ I:=filter_subset ..
 refine ⟨feat_v Ω (fun _=> Cκ) F_ l p0 (ΔX) (fun i p=>hf i (H' p)) ?_, fun i v=> ?_, fun i _=>?_⟩
 · intro x; let M:= Real.exp p0.supportExponent * |Kprice p0 1 Vκ|; have he:0 ≤ M:=mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
   have hc:coverNumber p0.B (Cκ).val.2 ≤ 1:=by -- Corona basic
      exact (Corona.cover_mono (Corona.halo_mono hu (Subset.refl {Tκ})) _).trans (AnalyticBridge.CouplingShape.ballPaid ..)
   let A:=(Ω).filter (fun i : ι=> (Cκ).val.1=x)
   apply le_trans ?_ (mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (s:=A) (f:=fun i=>p0.mass (D i).val.2 (W_ i)) ((filter_subset ..).trans (show Ω⊆I from H')) (fun i p _=>mul_nonneg (Real.exp_pos _).le (ht' i p))).trans V') he); rw [Finset.mul_sum]; refine sum_le_sum fun i p=>?_
   have h:i∈ I:= H' (mem_filter.mp p).1; unfold BudgetPoint.mass; apply le_trans (mul_le_mul_of_nonneg_right (Real.exp_monotone (show p0.supportExponent* (coverNumber Γ (Cκ).val.2:ℝ) ≤ p0.supportExponent from (by exact mul_le_of_le_one_right p0.exponent_pos.le (by exact_mod_cast hc)))) (hz i h)); unfold l; rw [k_η,mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul ((le_abs_self _)) (tonne_ge p0 _ _ (ht' _ h)) (ht' _ h) (abs_nonneg _)) (Real.exp_pos _).le
 · unfold silver_P sunY; apply sum_eq_zero; intro j p; have hp:= (mem_filter.mp p).2; subst i; exact False.elim (v rfl)
 by_cases p:i=Cκ
 · subst i; rw [if_pos rfl]; unfold silver_P sunY; rw [Finset.filter_true_of_mem (p:=fun _=>(Cκ)=(Cκ)) (fun _ _=>rfl)]; refine ⟨?_,?_⟩
   · change Pastry.pane ((∑ i∈ L,F_ i) 1)=_; rw [Finset.sum_apply]; change panHom _ _=0; rw [map_sum]; exact sum_eq_zero fun i p=> (P i (H' p)).2.1 -- tune
   rw [α_sum _ _ _ L l F_ (fun i p=> hf i (H' p)) h0]; change _= (Lρ,ζp); refine Prod.ext ?_ ?_ -- tune avoid simp over Lℓ
   · rw [Prod.fst_sum]; exact sum_congr rfl fun i p=> congrArg Prod.fst (P i (H' p)).2.2
   rw [Prod.snd_sum]; exact sum_congr rfl fun i p=> congrArg Prod.snd (P i (H' p)).2.2
 rw [show Zρ i=0 from ?_,if_neg p]; swap; · unfold silver_P sunY; refine sum_eq_zero fun j h=>False.elim (p (mem_filter.mp h).2.symm)
 exact ⟨rfl,Pill_0 ..⟩
end YM.CF.Neon
