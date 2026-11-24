import YM.CF.Beau.Chair
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
variable {F G:InkD n}{X₀:Scree.Hub n}
local notation "Gm" F:max=> (Taxi.lifeH F ∘ increment 1)
local notation "Op"=> X₀.val.1
lemma profit(p:PressB P X₀ F h a)(u:0≤ h): ContDiffAt ℝ ((↑(2:ℕ): WithTop ℕ∞)) (Taxi.lifeH F ∘ increment 1) 0:= (Taxi.eraF _ _ p u 1 (ping_f P _)).paid.of_le (Nat.cast_le.mpr ((by norm_num: (2:ℕ)≤6).trans P.order_ge))
lemma spark_c (t: spark Op F)(v: spark Op G)(hf:ContDiffAt ℝ ((↑(2:ℕ):WithTop ℕ∞)) (Gm F) 0)(hg:ContDiffAt ℝ ((↑(2:ℕ):WithTop ℕ∞)) (Gm G) 0): spark Op (F+G):=by
 refine ⟨(map_add ..).trans (by rw [t.1,v.1,zero_add]),fun x y a b=>?_⟩ -- syntactic goal
 rw [show pot (n:=n) ∅ ∘ (F+G)∘increment 1=(pot ∅ ∘ F ∘ increment 1)+(pot ∅ ∘ G ∘ increment 1) from funext fun i=>map_add .., iteratedFDeriv_add_apply (show ContDiffAt ℝ ((↑(2:ℕ):WithTop ℕ∞)) (pot ∅ ∘ F ∘ increment 1) 0 from hf) (show ContDiffAt ℝ ((↑(2:ℕ):WithTop ℕ∞)) (pot ∅ ∘ G ∘ increment 1) 0 from hg)]; simp only [_root_.add_apply,t.2 _ _ a b,v.2 _ _ a b,zero_add] -- indent
lemma spark_g (t: spark Op F)(hf:ContDiffAt ℝ ((↑(2:ℕ):WithTop ℕ∞)) (Gm F) 0)(x:ℝ): spark Op (x • F):=by
 refine ⟨((map_smul (pot ∅) x (F 1))).trans (by rw [t.1,smul_zero]),fun i y a b=>?_ ⟩
 rw [show pot (n:=n) ∅∘ (x • F) ∘ increment 1= x • (pot ∅ ∘ F ∘ increment 1) from funext fun i=> map_smul (pot ∅) x (F (increment 1 i)),iteratedFDeriv_const_smul_apply (i:=2) (show ContDiffAt ℝ ((↑(2:ℕ):WithTop ℕ∞)) (pot ∅ ∘ F ∘ increment 1) 0 from hf),_root_.smul_apply, t.2 _ _ a b,smul_zero] -- syntax
variable {i j: RegBudget n}{γ d' :ℝ}{P':BudgetPoint}{L:ℕ}
lemma gala_k {p: PressB P X₀ F h c}(u: spark Op F): spark Op (sage_L F):=by
 have hp: pot ∅ ∘ sage_L F= pot ∅ ∘ F:=funext fun y=> by change crumb (wage_Q 0 _).val _= _; rw [price_X,if_pos card_empty]; rfl
 refine ⟨Eq.trans (congrFun hp 1) u.1,fun x y t v=>?_ ⟩; change iteratedFDeriv ℝ 2 ((pot ∅ ∘ sage_L F) ∘ increment 1) 0 _= _; rw [hp]; exact u.2 _ _ t v
lemma night_k (p:Ionic P L i)(w:0 ≤ h)(v:IncX (fun _=>False) i P h b)(s:ℝ): Ionic P L (s • i):=by obtain ⟨f,t,v⟩:=v.weight; intro X u g; exact spark_g (X₀:=X) (p X u g) (profit (t X) w) s
lemma wage_add (p:Ionic P L i)(t:Ionic P L j)(v:IncX (fun _=>False) i P h a)(u: IncX (fun _=>False) j P h b)(h0:0≤h) : Ionic P L (i+j):=by obtain ⟨f,e,k⟩:=v.weight; obtain ⟨f',e',k'⟩:=u.weight; intro X l h; exact spark_c (X₀:=X) (p X l h) (t X l h) (profit (e X) h0) (profit (e' X) h0)
variable (U:Scree.Hub n→ InkD n)(u:Scree.Hub n→ℝ)(V:Scree.Hub n→ Scree.Hub n)
lemma add_Z{ι:Type*}[DecidableEq ι](S:Finset ι)(p:ι→ InkD n)(C:ι→ℝ)(v:∀ i∈ S,spark Op (p i))(q:∀ i∈ S,PressB P X₀ (p i) h (C i))(s:0≤h): spark Op (∑ i∈ S,p i):=by
 induction S using Finset.induction_on with
 | empty => rw [sum_empty]; exact Beau.none_q _
 | insert i S t ih=> rw [sum_insert t]; have hv'(r)(h:r∈ S):r∈insert i S:=mem_insert_of_mem h; exact spark_c (X₀:=X₀) (v _ (mem_insert_self ..)) (ih (fun j k=>v j (hv' j k)) (fun j k=>q j (hv' _ k))) (profit (q i (mem_insert_self ..)) s) (profit (prop_sum S p C P h X₀ (fun j k=>q j (hv' _ k))) s)
-- Norm.P:Aeros. reconstructed at same strict τ
lemma root_t{K':Finset (Dwell n)→ℝ}(v:∀ U,BedP P U F X₀ K')(p:spark Op F)(t:PressB P X₀ F h a): Siete.Acceptance P X₀.val.2 X₀.val.1 (fun V=>crumb (F V).val ∅) (K' ∅):=⟨fun U l=>v U l ∅, X₀.property,p.1,p.2,fun i j p=>congrArg (pot ∅) (t.term i j p),fun x g=> Eq.trans (congrArg (pot ∅) (t.gaugeV _ _)) (Pastry.center_b ..), (pot ∅).continuous.measurable.comp t.measureV⟩
end YM.CF.Beau
