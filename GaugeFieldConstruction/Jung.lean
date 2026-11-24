import GaugeFieldConstruction.Moab
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 55000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
variable {x:ℝ} {P:BudgetPoint}{N:Side}{E I A D:Type}[Fintype I][LinearOrder I][Fintype A]
variable [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
-- cover stronger.Need L µ.Power. Budget raise h? Path h fixed. Bind
open Py.Riant TableF Lenten Lenten.Layout Fren -- tune
variable (o:I→Site N) {U:Finset I→ A→D→ E} (X:Cornea A D E N) {F:Finset I→ E}{a b c V h:ℝ}{m:ℕ}{J:Finset (Finset I)}
lemma W_silk (p:Ledges X o U)(i: A)(u:D)(q:X.valid i u): let U'(z:Key I):= WritV o U z i u; Hush o (X.Φ i) U' ∧ River U':=by
 intro U'; let R:= realm_C o; let A(x:Key I):=Fluid o (fun j=>U j i u) x; have he:U'=A:=by funext i; unfold U' WritV; simp_rw [Finset.sum_apply]; rfl
 rw [he]; refine ⟨fun x v y t h=>?_, (tip_bank R _ (fun i _=>lift_b i _)).1 ⟩
 unfold A Fluid; refine sum_congr rfl (fun j s=>?_); by_cases ht:U j i u=0; dsimp only; rw [ht,smul_zero,smul_zero]; exact congrArg (· • U j i u) (show Mew.pine j x=Mew.pine j y from prod_congr rfl (fun i₀ t=>h i₀ ((p _ _ q j ht).2 i₀ t)))
 -- need i:I for pine_e? read
lemma ArcU_value {T:Type}[AddCommMonoid T][Module ℂ T](F:Finset I→ T):WritV o F 0=F ∅:=by
 unfold WritV; rw [sum_eq_single (∅:Finset I) ?_ ?_]; · unfold Mew.pine; rw [prod_empty,one_smul]
 · intro j _ p; rw [charm_D j p,zero_smul]
 intro v; exact False.elim (v (mem_filter.mpr ⟨mem_univ _,by simp⟩))
-- BookT eval finite $pow.Res$. No need hill_F. 
lemma SB_eval (p:BookT X U m J a b c)(V: Mew.Key I)(h:∀ i,‖V i‖≤ b) : ShelfK X (∑ i∈ J, Mew.pine i V • U i) m a c :=by
 obtain ⟨F,H,u⟩:=p; refine ⟨fun A=> ∑ i∈ J,b^i.card* F i A,?_,?_⟩
 · intro i; rw [Finset.sum_apply]; let d(j:Finset I):= b^j.card * F j i; let E(j):=(Mew.pine j V) • (U j i)
   have ht(j)(t:j∈J):X.Lux i (E j) (d j):=by
      apply X.widen _ _ _ _ (X.coin _ _ _ (H _ t _) (Mew.pine j V)); have hx: ‖Mew.pine j V‖≤b^j.card:=by unfold Mew.pine; rw [norm_prod]; exact (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>h _)).trans (le_of_eq (prod_const ..))
      exact mul_le_mul_of_nonneg_right hx (X.posG _ _ _ (H j t _))
   have hs(T:Finset (Finset I))(p:T⊆ J):X.Lux i (∑ j∈T,E j) (∑ j∈T,d j):=by
      induction T using Finset.induction_on with
      | empty=>rw [sum_empty,sum_empty]; exact X.zero i _ (fun _ _=>rfl)
      | @insert x T w ih=>rw [sum_insert w,sum_insert w]; exact X.add _ _ _ _ _ (ht _ (p (mem_insert_self ..))) (ih fun y t=>p (mem_insert_of_mem t)) -- order dots before args
   exact hs _ Subset.rfl
 intro x; refine le_trans (le_of_eq ?_) (u x); simp_rw [mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [mul_left_comm]
variable (V1:Finset I→RegBudget N)(V2:Finset I→ForceBudget N)(Y: GramM N)(σ:I→Seat N)
abbrev CurtainP (F:Finset I→ RegBudget N)(V: Key I):= if V∈hill I then WritV σ F V else 0
abbrev CurtainK (F:Finset I→ ForceBudget N)(V: Key I):= if V∈hill I then WritV σ F V else 0
abbrev Flank_P (σ:I→Seat N)(F:Finset I→ RegBudget N)(K:RegBudget N)(x:Key I): RegBudget N:=K+ CurtainP σ F x
abbrev Flank_K (σ:I→Seat N)(F:Finset I→ ForceBudget N)(K:ForceBudget N)(x:Key I): ForceBudget N:= K+ CurtainK σ F x
structure Journal1 (p:BudgetPoint)(w:0<h)(σ:I→ Seat N)(V:Finset I→ RegBudget N)(U:Finset I→ ForceBudget N)(a b f:ℝ):Prop where
 fil :BookT (SecX (KeyUp p) w.le N) V p.B (realm_C σ) a b f
 high:BookT (SecK p w.le N) U p.B (realm_C σ) a b f
 rite:Ledges (SecX (KeyUp p) w.le N) σ V
 right:Ledges (SecK p w.le N) σ U
 root:V ∅=0 ∧ U ∅=0
-- $4/3$. Intend p Arc. E uses anchor O. define K. F f. budget.Organization.Call
lemma thawE (F:RegBudget N)(w:0≤h)(he: ShelfK (SecX (KeyUp P) w N) F P.B P.supportExponent a)(p:P.power=2): IncX primeU F P h a:=by -- don't specialize Y
 obtain ⟨C,t,u⟩:=he; refine ⟨⟨C,fun i=> Hope.smallerP p (t i) w,fun i=>?_⟩,fun i p=>p.elim⟩
 rw [←sum_filter]; refine le_trans ?_ (u i); let A:=P.supportExponent; -- relation support.Book.
 apply sum_le_sum_of_subset_of_nonneg
 · intro j t; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp t).2.symm ▸ j.property⟩
 intro j x y; exact mul_nonneg (Real.exp_pos _).le ((SecX _ w _).posG _ _ _ (t _)) -- tune
lemma thawK (F:ForceBudget N)(w:0≤h)(he:ShelfK (SecK P w N) F P.B P.supportExponent a): Dark primeU F P h a:=by
 obtain ⟨C,t,u⟩:= he; refine ⟨⟨C,t,fun i=>?_⟩,fun i p=>p.elim⟩; rw [←sum_filter]; exact u _ -- tune
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
