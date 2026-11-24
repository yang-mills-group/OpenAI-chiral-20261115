import YM.CF.Vp929.Canon.Gnaw
import YM.CF.Vp929.Pre.Livery
import YM.CF.Neon.Stock
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace TestW
open Fir
open SU Bloch Tap
variable {n L:Side} {M:Male} {j:ℕ} {q C d a b v A t:ℝ}
variable {F:RegBudget n}{P:BudgetPoint}{s:Finset (Scree.Hub n)} (vS:liveB s)
local notation "E0"=> Op (Single n)
local notation "E2"=> SpinIdx × SU.Slot
local notation "WW" u:max=> heroP u
local notation "Ψ"=> StackL F s
local notation "μX"=> (1:Pane n)
local notation "ρX"=> spar j M (1:Pane n)
open Salt Vow Bake Larch Cycle929
local notation "Hz"=> Scree.Hub n
local notation "k_"=> L.val
-- exact Utrue PressB chop
abbrev massH(P:BudgetPoint):Finset (Scree.Hub n):=univ.filter fun i:Hz=>coverNumber P.B i.val.2 ≤1
def rightS(P:BudgetPoint)(F:RegBudget n):RegBudget n:=fun i => if i∈massH P then restK (F i) else 0
local notation "S_"=> rightS P
abbrev shaveL(P:BudgetPoint) : RegBudget n→ₗ[ℝ] RegBudget n := {
 toFun:= rightS P
 map_add' := fun a b=> by
    funext i x; simp only [rightS,Pi.add_apply]; by_cases h:i∈ massH P; · simp only [h,if_true]; exact map_add (peekL 2) _ _
    simp [h]
 map_smul' := fun a b=> by
    funext i x; simp only [rightS,Pi.smul_apply]; by_cases h:i∈massH P; · simp only [h,if_true]; exact map_smul (peekL 2) _ _
    simp [h] }
private lemma rest_p {i:Hz}{A:InkD n}(s:PressB P i A a b): PressB P i (restK A) a b:=by
 obtain ⟨x,v,t,j,G,u,T,w⟩:=s; refine ⟨fun i j p=>congrArg (wage_Q 2) (x _ _ p),fun i=>worthS 2 _ _ (v i), (peek_P 2).measurable.comp t,fun i v=>?_,G,u,fun i p j=>?_,w⟩
 · simp only [restK,Function.comp_apply,j]; exact pose_U ..
 simp only [restK,Function.comp_apply,price_X]; split; exact T i p j; exact hail (by rw [norm_zero]; exact u j)
lemma shave_p (F:RegBudget n)(g:IncX Utrue F P a b)(p:1 ≤ a) : IncX Utrue (rightS P F) P a b:=by
 obtain ⟨w,G,u⟩:=g.weight; let W(i:Scree.Hub n):= if i∈massH P then w i else 0; have hv(i): PressB P i (rightS P F i) a (W i):=by unfold rightS W; split; exact rest_p (G i); exact Vale.rinse ..
 refine ⟨⟨W,hv,fun i=>le_trans ?_ (u i)⟩,fun x y U h X i=>?_⟩
 · apply sum_le_sum; intro i _; split; swap; exact le_rfl
   apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; unfold W; split; exact le_rfl; exact grit_p P (G i) (zero_le_one.trans p)
 unfold rightS; by_cases t:X∈massH P; all_goals have q: moveHub x X∈massH P↔ X∈massH P:= by simp only [massH,mem_filter,true_and,mem_univ]; rw [show coverNumber P.B (moveHub x X).val.2= _ from glow_q x P.B X.val.2]
 · rw [if_pos (q.mpr t), if_pos t]; unfold restK; simp only [Function.comp_apply,g.face x y U h X i]; exact pose_U ..
 rw [if_neg (mt q.mp t),if_neg t]; exact (map_zero _).symm
lemma shaveC {F:RegBudget n}:∀ i:Hz,∀ V:Pane n,wage_Q 2 (S_ F i V)=S_ F i V:=by
 intro i v; apply pimp_Q; intro x; rw [price_X]; split; rfl
 next t=>
           unfold rightS; split
           next h=> simp [restK,price_X,t]
           next h=> exact (by change (0:ℂ)=0; rfl)
lemma orbit_wage (Z:Cipher n): orbitPH (wage_Q 2 Z)=orbitPH Z:=by
 ext a b; change portB _ _ _= portB _ _ _; simp only [Prism.port_eq]; split; rfl
 next i=> rw [price_X]; simp;
lemma shave_stack (F:RegBudget n)(p:massH P⊆s): StackL (rightS P F) s=StackL F (massH P):=by
 unfold StackL; rw [←sum_subset p ?_]; swap; · intro i h x; rw [rightS,if_neg x]; exact Neon.orbit_0 _
 apply sum_congr rfl; intro i v; rw [rightS,if_pos v]; exact orbit_wage _
variable (T:Scree.Hub n→Scree.Hub n)(p:Extension L.val P n T)
abbrev warpled :RegBudget n→ₗ[ℝ] RegBudget n := {
 toFun:= warp_E T
 map_add' := fun x y=>by funext i; unfold warp_E sunY; simp only [Pi.add_apply,sum_add_distrib]
 map_smul':= fun t x=>by funext i; unfold warp_E sunY; simp only [Pi.smul_apply, RingHom.id_apply, smul_sum] }
private lemma flown (k:Aura n)(x:Support (More n))(p q:Copy n): Vow.flick k (p+q) x= Vow.flick k p x+Vow.flick k q x:= by unfold Vow.flick; split; rfl; exact (add_zero _).symm
abbrev crestLedL (k:ℕ)(P:BudgetPoint): RegBudget n→ₗ[ℝ] Cusp n := {
 toFun:= ridge_Q P k T
 map_add':= fun a b=>by
    unfold ridge_Q soot_T; rw [←sum_add_distrib]; refine sum_congr rfl fun i _=>?_ ; funext j V; let u:= lagE (T i); unfold stroke chasmR; by_cases he:j= (lagE∘ T) i; · subst j; simp only [Pi.add_apply,Pi.single_eq_same,Function.comp_apply]; rw [show oV (a i+b i)=oV (a i)+oV (b i) from rfl,flown,flown]; abel
    simp_rw [Pi.add_apply,Pi.single_eq_of_ne he, Pi.zero_apply,add_zero]
 map_smul':= fun t x=>by
    have heS(k:Aura n)(x:Support (More n))(p: Copy n):Vow.flick k (t•p) x=t • Vow.flick k p x:=by unfold Vow.flick; split; rfl; exact (smul_zero _).symm
    unfold ridge_Q soot_T; rw [show RingHom.id ℝ t=t from rfl,smul_sum]; apply sum_congr rfl; intro i _; funext j V; unfold stroke chasmR; by_cases he:j=(lagE∘ T) i; · subst j; simp only [Pi.smul_apply,Pi.single_eq_same,Function.comp_apply]; rw [show oV (t • x i)= t • oV (x i) from rfl,heS,heS]; exact Eq.symm (smul_sub ..)
    simp_rw [Pi.smul_apply,Pi.single_eq_of_ne he, Pi.zero_apply,smul_zero] }
abbrev NetX (P:BudgetPoint) : RegBudget n→ₗ[ℝ] RegBudget n:= shaveL P - (writP.comp (warpled T)).comp (shaveL P)
abbrev NetY (P:BudgetPoint)(L:ℕ) : RegBudget n→ₗ[ℝ] Cusp n:= -(writY.comp (crestLedL T L P) |>.comp (shaveL P))
local notation "Xv"=> NetX T P F
local notation "Zv"=> (S_ F)
local notation "Wv"=> (writ_E (warp_E T (S_ F)))
local notation "Pv"=> (writ_K (ridge_Q P k_ T (S_ F)))
local notation "Yv"=> NetY T P L.val F
local notation "Π"=> Cash.prominence P
abbrev profitX (b:ℝ)(P:BudgetPoint)(L:ℕ):ℝ:= b+wren_K P.order P.power*(Real.exp (P.supportExponent*mstar L)*b)
abbrev profitY (b:ℝ)(P:BudgetPoint)(L:ℕ):= pack_Q P.order * Extension.wagon L P.order (Cash.prominence P) P.B b

include p
omit vS
open QuiltB
lemma realizeX (pO: 4 ≤ L.val)(pU:IncX Utrue F P a b)(hv:1 ≤ a)(R:PathData SU.group)(c:Clip) : Piece P a R c Xv Yv 0 (profitX b P L.val) (profitY b P L.val)∧ Ionic P L.val Xv∧ StackL Xv (treeΘ P L.val)=StackL F (massH P):=by
 let Sh:= treeΘ (X:=n) P L.val; let G:= Wv; let A:=Zv; let K:=Pv; have ht(i:Hz)(p':i∈Sh) : Xv i=Zv i:=by change Zv i- Wv i= _; rw [p.oldS _ i ((mem_filter.mp p').2),sub_zero]
 have h0:=zero_le_one.trans hv; have h:= shave_p F pU hv; obtain ⟨hk,zz⟩:= budTwo (F:=T) (L:=L.val) (Q:=P) (X:=Zv) shaveC
 have hC:= p.convoy _ _ h h0; have hp':0 ≤ Π:=by unfold Cash.prominence; linarith [P.exponent_pos]
 have hτ := p.canopy _ _ h h0 hp'; let BV:= cup_R P _ hC (Eq.symm hk ▸ zero_r) h0
 refine ⟨⟨by simpa only [show Xv=Zv+(-1:ℝ) • Wv from (by rw [neg_smul,one_smul]; exact sub_eq_add_neg ..),abs_neg,abs_one,one_mul] using (addT P h (Fixed.Voltage.crestV P Utrue BV (-1))),?_ , ?_,?_⟩,?_ ,?_⟩
 · change Packed P a _ (-Pv) _; simpa only [profitY,neg_smul,one_smul,abs_neg,abs_one,one_mul] using wagePack (anyTwoYear hτ zz h0) (-1)
 · change ZealQ (-Pv); simpa only [neg_smul,one_smul] using zeal_r (stead_m (ridge_Q P L.val T (S_ F))) (-1)
 · intro i v; change exponentL P (Zv-Wv) _+fuelV P (-Pv) i=moldV n (0* _); let e:= brewNo p h i v
   rw [zero_mul,map_zero,show -Pv=(0:Cusp n)-Pv from (zero_sub _).symm, fuel_η,prizes0, show exponentL P (Zv-Wv) i.1=exponentL P Zv i.1-exponentL P Wv i.1 from eq_sub_of_add_eq (by rw [←Larch.ripe_H P i,sub_add_cancel]) ,←e]; abel
 · intro i u t; rw [ht i (mem_filter.mpr ⟨mem_univ _,t⟩)]; have q:pot (n:=n) ∅ ∘ (Zv i)=fun _=>0:=by funext x; change crumb (Zv i x).val _=0; rw [←(shaveC i x),price_X]; norm_num
   refine ⟨congr_fun q (1:Pane n),fun y z a b=>?_⟩
   rw [show pot (n:=n) ∅ ∘ (Zv i) ∘ increment 1=(fun _=>0) from funext fun x=>congr_fun q _, iteratedFDeriv_const_of_ne (by omega : (2:ℕ) ≠ 0)]; first|rfl|skip
 refine Eq.trans (show StackL Xv Sh= StackL Zv Sh from sum_congr rfl (fun i q=> by rw [ht i q])) (shave_stack F (fun i v=>teal n P _ pO i (mem_filter.mp v).2))
end TestW
end Test
end YM.CF.Py.Rate
