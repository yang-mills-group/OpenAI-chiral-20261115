import SatinThinPetal

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


open StressFlux AnalyticBridge.VerifiedReset
open Rate Pitching Focus
attribute [-instance] instDecidableEqLex
variable {N B n:Side}
def bare_P (A:ℝ):= Real.exp 1* Moto.trotΦ HI 1 A
variable (L:Side)(P:BudgetPoint)(q h A b:ℝ)
lemma cloth_price (e:20 < (More (mid N B)).val) (f:10 ≤ P.B)(p:P.order=6)(w:P.power=2)(r:P.supportExponent=1)(t:DayT 6 b)(u:0≤b)(ho:0 ≤ h)(hq:0≤q)(v:bare_P b ≤ A)(o:Site (mid N B)): Axon L.val o P (cloth_E P q o) h (A*q) (PointSk q):=by
 let Q:= Φrap (mid N B) o 10; let Z:= q • mainSlot; let V:= plateZ (node o) P Z; let E:= cloth_E P q o; let j:= trotΦ P q b
 have hp:Real.exp P.supportExponent * trotΦ P q b ≤ A*q:= by
    rw [show trotΦ P q b=trotΦ HI q b from tV_c _ _ p w b q,r]; refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right v hq); unfold bare_P trotΦ Taxi.tollV; ring
 have he:halo 2 {node o}⊆ Q.val.2:= Corona.halo_mono (by norm_num) (Subset.refl _); have hv:‖Z‖=q:=by unfold Z; rw [norm_smul,slotNorm, mul_one,Real.norm_of_nonneg hq]
 have hh (i k:PlaqAxes):‖Z i k‖ ≤ q:= (norm_le_pi_norm (Z i) k).trans ((norm_le_pi_norm Z i).trans hv.le)
 have hPp: PressB P Q V h j:=champ P Z Q (p.symm ▸ t) u he hh
 refine turf_A _ _ _ _ _ _ _ hp ⟨⟨⟨Pi.single Q j, ?_,?_⟩,fun _ p=>False.elim p⟩,?_,?_⟩
 · intro i; by_cases m:i=Q; · subst i; unfold cloth_E; simp_rw [Q, Pi.single_eq_same]; exact hPp
   unfold cloth_E; rw [Pi.single_eq_of_ne m, Pi.single_eq_of_ne m]; exact Vale.rinse ..
 · intro i; rw [sum_eq_single Q]; swap; · intro k _ h; split; rw [Pi.single_eq_of_ne h]; simp [BudgetPoint.mass]; rfl
   swap; · simp
   have hκ:= Roots.gradeE _ _ hPp ho; rw [Pi.single_eq_same]; split; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (show P.supportExponent*(coverNumber P.B Q.val.2:ℝ) ≤ P.supportExponent from mul_le_of_le_one_right P.exponent_pos.le (by exact_mod_cast (Corona.cover_mono (Corona.halo_mono f (Subset.refl {node o})) _).trans (AnalyticBridge.CouplingShape.ballPaid ..)))) hκ; exact mul_nonneg (Real.exp_pos ..|>.le) hκ
 · intro i u; exact Pi.single_eq_of_ne (fun h:i=Q=>u (h ▸ rfl)) ..
 intro i x; by_cases g:i=Q; swap; · unfold cloth_E; rw [Pi.single_eq_of_ne g,if_neg g]; exact ⟨rfl,Pill_0 ..⟩
 subst i;  unfold cloth_E; simp only [Q, Pi.single_eq_same,ite_true]; obtain ⟨k,k'⟩:= suit_l P Z Q ho (p.symm ▸ t) u he hh e (show Verc Z from fun i j=> by unfold Z; simp only [Pi.smul_apply]; exact congrArg _ (slotV i j))
 refine ⟨k,Prod.ext k' ?_⟩; change jetsL _ _=0; rw [show orbitPH (V 1)= _ from hol_l _, pub_eq,map_zero] -- tune
variable {I J: Type} [Fintype I][Fintype J][LinearOrder I][LinearOrder J]
lemma fixedE_zero (n:Side): FixedE (n:=n) P h 0 0:= ⟨fun _=>0, fun _=> Vale.rinse ..,by simp⟩
lemma fixedF_zero (n:Side): FixedF (n:=n) P h 0 0:= ⟨fun _=>0, fun _=> Vale.rinsed ..,by simp⟩
lemma ink_zero (u:0 ≤ A)(n:Side): IncX primeU (0:RegBudget n) P h A:= by
 obtain ⟨⟨g,c,f⟩,r⟩:= (Vale.lye (c:=n) primeU P h).1; exact ⟨⟨g,c,fun i=> (f _).trans u⟩,r⟩
lemma dark_zero (u:0 ≤ A)(n:Side): Dark primeU (0:ForceBudget n) P h A:= by
 obtain ⟨⟨g,c,f⟩,r⟩:= (Vale.lye (c:=n) primeU P h).2; exact ⟨⟨g,c,fun i=> (f _).trans u⟩,r⟩
-- Topic always faces for gap 0
lemma cloth_nil (x:Site n): cloth_E P 0 x=0:=by
 unfold cloth_E; rw [zero_smul, show plateZ _ P 0= _ from ?_,Pi.single_zero]
 exact funext fun i=>by rw [plateZ]; simp [kerP,counter,AnalyticBridge.VerifiedReset.quad]; exact (zero_smul ℂ (1:Cipher _)) -- tune use plate_core instead
local notation "Ω"=> mid N B
local notation "Λh"=> Key (Article I)
def clothSet (P:BudgetPoint)(q:ℝ):Fin 2→ Topic n:= fun i=> cloth_topic P (readFee q i)
variable (X:GramM (mid N B))(σ:I→ Site (mid N B))
abbrev normInk (i: Article I):= cloth_E P (readFee q (layer i)) (treeO σ i)
def clothTable (z:Key (Article I)) : RegBudget (mid N B):= ∑ i:Article I,z i • normInk P q σ i
local notation "T"=> clothTable P q σ
local notation "K"=> normInk P q σ
lemma limb_sum (S:J→RegBudget n)(z:ℂ)(i:J): (∑ j:J,update (0:Key J) i z j • S j)=z • S i:=by
 rw [sum_eq_single_of_mem i (mem_univ _),update_self]; exact fun j _ x=> by rw [update_of_ne x]; exact zero_smul ..
lemma cloth_first (i:Article I): νTip T i=K i:=by
 funext x y; change tipI _ _=(K i) x y; unfold clothTable; simp_rw [Finset.sum_apply,Pi.smul_apply]
 let G(j:Article I)(z:Λh):= Mew.pine {j} z • ((K j) x y)
 refine (Eq.trans ?_ (show (∑ j:Article I, tipI (G j) [i])=(K i) x y from ?_))
 · rw [show (fun z:Λh=> ∑ j:Article I, z j • K j x y)=fun z=>∑ j:Article I,G j z from funext fun z=>sum_congr rfl fun j _=>by simp only [G,Mew.pine,prod_singleton]]; exact (tip_bank _ G (fun j _=>lift_b _ _)).2 _
 rw [sum_eq_single i]; · unfold G; rw [tip_tape _ (by simp)]; simp
 · intro j _ v; unfold G; rw [tip_tape _ (by simp)]; simp [Ne.symm v]
 simp
variable (p:∀ x:Site (mid N B), Axon L.val x P (cloth_E P q x) h (A/8*q) (PointSk q)) (v:0 ≤ h)(w:1 ≤ h)(a:0 ≤ A)(e:0<q)
local notation "VY"=> fun i: Article I=> PointSk (readFee q (layer i))
include p a e
lemma cloth_I(i:Article I) : Axon L.val (treeO σ i) P (K i) h (A/8*q) (VY i):=by
 rw [recover_art i]; generalize layer i=j; generalize host i=i; fin_cases j
 · change Axon _ _ _ (cloth_E _ (readFee q 0) _) _ _ (PointSk (readFee q 0)); rw [(read_up q).1]; exact p _
 change Axon _ _ _ (cloth_E _ (readFee q 1) _) _ _ (PointSk (readFee q 1)); rw [(read_up q).2,cloth_nil P,point_zero]; exact turf_A _ _ _ _ _ _ _ (by positivity) (nothing_X ..)
include w
lemma cloth_page (vp:Very_Ψ σ X.p.B)(xp:X.p=P) : Bulletin L X σ T 0 h 2 (4*A) (A/8) q (clothSet P q) ∧ PanoramaBill P h (2*q⁻¹) q (2*A) T (0:Key (Article I)→ForceBudget Ω):=by
 let p':= cloth_I L P q h A σ p a e; let f(i:Article I):= ((p' i).vest); have hb:0 ≤ A/8*q:=by positivity
 have hh(i:Article I): emberTip (0:Key (Article I)→ForceBudget Ω) i=0:=funext₂ fun _ _=> Mew.tip_0 _
 refine ⟨⟨⟨⟨?_,rfl⟩,fun i x y z=> ?_,fun i y=>?_,fun i x y z=> rfl,fun i y=> differentiable_const _,fun i x=>?_⟩,fun z h=>?_,fun i=>?_ ⟩,fun z u=>?_⟩
 · unfold clothTable; simp only [Pi.zero_apply,zero_smul, sum_const_zero]
 · simp only [clothTable,Finset.sum_apply,Pi.smul_apply]; refine Finset.sum_congr rfl fun j _=>?_
   by_cases v:(K j i=0); · rw [v,smul_zero,smul_zero]
   have h:= of_not_not (mt ((p' j).site i) v); rw [z j (show (Cube.node ∘ treeO σ) j∈ i.val.2 from (show node (treeO σ j)∈i.val.2 from h ▸ i.property))]
 · simp_rw [clothTable,Finset.sum_apply,Pi.smul_apply]; exact Differentiable.fun_sum fun j _=> (show Differentiable ℂ (fun z:Λh=> z j) from differentiable_apply j).smul (differentiable_const _)
 · rw [cloth_first P,hh]; exact ⟨limb_sum ..,(smul_zero x).symm⟩
 · 
   refine ⟨?_,xp.symm ▸ dark_zero P _ _ (by positivity) _⟩
   have he:= lean_C X (treeO σ) 2 w L K VY (double_force σ X.p vp) (fun i=>xp.symm ▸ p' i) z h hb; apply Provides.liftE _ X _ _ he; push_cast; linarith only [hb]
 · rw [cloth_first P,hh]; exact ⟨xp.symm ▸ p' i,cloth_owns ..⟩
 refine ⟨∑ i:Article I,z i • K i,0,(0:ForceBudget Ω),0,(add_zero _).symm, (add_zero (0:ForceBudget Ω)).symm, ?_, (fixedF_zero P h _).more (by positivity), ink_zero P h q e.le _, dark_zero P h q e.le _⟩
 refine (sum_FixedE K (fun _=>A/8*q) z (fun i=> Axon_fixedE (p' i) (zero_le_one.trans w))).more ?_; refine (Finset.sum_le_sum (g:=fun _=> (2*A)) (fun i _=> ((mul_le_mul_of_nonneg_right (u i) hb).trans ?_))).trans_eq ?_; · rw [show 2*q⁻¹*(A/8*q)=2*(A/8) by field_simp]; linarith
 rw [sum_const, nsmul_eq_mul, card_univ, mul_comm]
end YM.CF.QuadClock
