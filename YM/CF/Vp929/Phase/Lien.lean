import YM.CF.Pso.Tide
import YM.CF.Vp929.Match.Pickup
import YM.CF.Beau.Merc
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
namespace Cycle929
open Py.Rate Mew
open scoped Mew ComplexConjugate
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
abbrev Logic (P:BudgetPoint)(h:ℝ)(F:RegBudget n→ E):Prop:= ∀ f:E→L[ℝ]ℝ,f ∘ F∈ accounts (DuesQ Utrue P h) Census
local notation "𝒯"=> RegBudget n
variable {A B: RegBudget n→ E}{S:Set ℂ}
namespace Logic
lemma asset (f:Logic P h A)(g:E→L[ℝ]ℝ):Accountable (DuesQ Utrue P h) Census (g∘A):=f g
protected lemma plus (f:Logic P h A)(g:Logic P h B):Logic P h (fun x=> A x+B x):=by intro k; convert (accounts (DuesQ Utrue P h) Census).add_mem (f k) (g k) using 1; exact funext (fun x=> map_add ..)
protected lemma sub (f:Logic P h A)(g:Logic P h B):Logic P h (fun x=> A x-B x):=by intro k; convert (accounts (DuesQ Utrue P h) Census).sub_mem (f k) (g k) using 1; exact funext (fun x=> map_sub ..)
protected lemma comp (u:E→L[ℝ]F)(f:Logic P h A): Logic P h (fun x=> u (A x)):=fun v=>f (v.comp u)
protected lemma zero:Logic P h (fun (_:RegBudget n)=> (0:E)):=by intro u; rw [show u ∘ (fun _=> (0:E))=(0:RegBudget n→ℝ) from funext fun _=>map_zero u]; exact zero_mem _
lemma earnings (hF:Logic P h A)(F G: 𝒯)(v:Enough (DuesQ Utrue P h) F)(u: Enough (DuesQ Utrue P h) G): A (F-G)=A F-A G:= SeparatingDual.eq_iff_forall_dual_eq (R:=ℝ)|>.mpr (fun g=> ((hF.asset g).receipt _ _ v u).trans (map_sub ..).symm)
lemma appears (F:RegBudget n→ℝ)(v:F∈accounts (DuesQ Utrue P h) Census): Logic P h F:=by
 intro u; have he: u ∘ F= u 1 • F:=by funext x; change u (F x)=u 1*F x; rw [mul_comm]; exact (map_smul u (F x) 1 |>.symm |> fun ht=> (congrArg u (mul_one (F x)).symm).trans ht.symm)
 rw [he]; exact Submodule.smul_mem _ _ v
lemma dormant (F:Logic P h A): A 0=0:=by
 let B:Enough (DuesQ (n:=n) Utrue P h) 0:= ⟨_,(Vale.lye Utrue P h).1⟩; simpa using F.earnings _ _ B B
lemma travel {G:ℂ→Pair 𝒯}(q:Valid (DuesQ Utrue P h) Census S G)(u:Logic P h A):Form S (fun z=>(A (G z).1,A (G z).2)):= fun g=> (u.asset g).liable _ _ q
protected lemma ballot {ι:Type*}(s:Finset ι)(M:ι→RegBudget n→E)(t:∀ i∈s,Logic P h (M i)):Logic P h fun x=>∑ i∈s,M i x:=by induction s using Finset.induction_on with| empty=>simp_rw [sum_empty]; exact Logic.zero| insert i s k ih=>simp_rw [sum_insert k]; exact (t i (mem_insert_self ..)).plus (ih fun j p=>t j (mem_insert_of_mem p))
protected lemma tune (f:Logic P h A)(x:ℝ) : Logic P h fun z=> x • A z:= f.comp (x • ContinuousLinearMap.id ℝ _)
lemma flex (p:Logic P h A)(t:∀ z : 𝒯, Enough (DuesQ Utrue P h) z→ B z=A z): Logic P h B:=by
 intro g; refine ⟨fun x y a b=>?_ , fun S F q=>?_ ⟩
 · unfold Function.comp; obtain ⟨u,v⟩:=a; obtain ⟨m,p'⟩:=b; have hp: DuesQ Utrue P h (x-y) (u+m) := by simpa [sub_eq_add_neg] using Ione.addT P v (Fixed.Voltage.crestV P Utrue p' (-1))
   rw [t (x-y) ⟨_,hp⟩,t x ⟨_,v⟩,t y ⟨_,p'⟩]; exact (p.asset g).receipt _ _ ⟨_,v⟩ ⟨_,p'⟩
 exact ((p.asset g).liable S F q).congr fun z h=> by simp only [probing,Function.comp_apply,t _ (q.minted h).1,t _ (q.minted h).2]
end Logic
open Logic
variable (U0:Scree.Hub n)(u: 1 ≤h)
lemma itemQ (v: Pane n) : Logic P h (fun T:RegBudget n=> T U0 v):= by intro x; exact ⟨fun a b _ _=>map_sub x _ _,fun S F q=>((q.2.1 U0 v).form q.1) x⟩
include u
lemma flow_hess (g:ℂ→L[ℝ]ℝ)(v w:tangD n): Logic P h (fun T:RegBudget n=> logHessian (g ∘ Taxi.lifeH (T U0)) v w):=by
 let j!:Fin 2→tangD n:=![v,w]; let F(U:RegBudget n):= g (iteratedFDeriv ℝ 2 (Taxi.lifeH (U U0) ∘ increment 1) 0 j!)
 have e:= registered U0 u (1:Pane n) (ping_f P U0.val.2) ∅ 2 (show 2 ≤ P.order from (show 2 ≤6 from by norm_num).trans P.order_ge) j! g
 have E:F∈accounts (DuesQ Utrue P h) Census:=Portfolio.redeem (fun x:RegBudget n=>x U0) (fun T u' p=>ask_piece u T p U0) (fun _ _ t=> t U0) (fun x y=>rfl) e
 apply Logic.flex (appears F E); intro x h; obtain ⟨a,h⟩:=h; change iteratedFDeriv ℝ 2 (g∘ Taxi.lifeH _ ∘ increment 1) 0 _ = F x; rw [g.iteratedFDeriv_comp_left (i:=2) (f:=Taxi.lifeH _ ∘ increment 1) (profit (ask_piece u x h U0) (zero_le_one.trans u)) le_rfl]; rfl
end Cycle929
end YM.CF.Beau
