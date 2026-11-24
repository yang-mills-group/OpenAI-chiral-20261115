import YM.CF.BPress.Pine.Breeze
/- Eq:B-PfC sum over decorated labels. Group with Palmer, fits contour-free theorem part. Pairing *sign* and zero of non-matches/repeats implemented through genuine Pfaffian tested on exterior strings, only geometry projection for power. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Ursell Palmer Fock Pastry Pf EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable {B J:Type}[Fintype B][DecidableEq B][Fintype J][DecidableEq J] {Y:Type}[DecidableEq Y][Fintype Y]{F:Branch.Field Y}
open Palmer Push.AbsoluteSums.Gas
namespace Story
variable {D:EdgeD I B Y F}(S:Story J D)(b:B→ℝ)(w:J→ℝ) (K:B→ℂ)(u:J→ℂ)
variable {μ σ C e γ χ:ℝ} {m:Side} (H:Sole F m)(g:Enorm D (σ+σ) C b)(t:Cash S.base (fun i=> ahead S (w i) i (1+C)) ((μ+μ)+(μ+μ)) e)(s:Stakes m μ χ)
lemma readW (A:Finset S.Drone)(K':B→ℂ)(u':J→ℂ) (P:Seal Y)(h:A.biUnion S.fort⊆ P)(e:∀ i,S.base i ⊆ P→u i=u' i)(q:∀ i,D.look i ⊆P→K i=K' i): S.totalW K u A=S.totalW K' u' A:=by
 have ht(i)(t:i∈A):S.fort i ⊆P:= (subset_biUnion_of_mem _ t).trans h; unfold totalW; split; next v=> apply congrArg₂ _ (prod_congr rfl (fun i p=> e _ ((S.base_sub i).trans (ht i p)))); apply congrArg; apply prod_congr rfl; exact fun i p=> globe D _ _ K K' (fun x q'=>q _ (q'.trans (subset_union_right.trans (ht i p)))) -- tune eq(Class) choices
 next v=> rfl
abbrev report := logL (Cover S.fort) (fun i=> totalW S K u i.val)
abbrev taxes := cash (Cover S.fort) (fun i=> ∏ t∈ i.val,blue S b w t)
def table := ∑ i:Finset J,totalU S K u i
lemma readR (T:Seal Y)(K':B→ℂ)(u':J→ℂ)(p:∀ i,S.base i ⊆ T→u i=u' i)(q:∀ i,D.look i ⊆T→K i=K' i): report S K u T=report S K' u' T:= η_reader _ _ _ _ fun i h=> readW S K u _ K' u' T h p q
lemma tape_nill(T:Seal Y): report S K (fun _=>0) T=0:=by
 unfold report; rw [show (fun i=> S.totalW K (fun _=>0) i.val)=(fun _:BranchC (S.fort) =>0) from ?_, log_idle]; funext i; unfold totalW; split; swap; · rfl
 obtain ⟨p,u⟩:=i.property.1; rw [prod_eq_zero u rfl]; simp
-- meas/cost joint. all uses in Bounded histories can specialize. Some read term domains only saturated in VolumeB-phase.
@[fun_prop] lemma continuous_green (i:I)(v:Option (D.Prec i)) : Continuous (fun K=>green D K i v):= by cases v; exact continuous_const; next h=> apply Continuous.subtype_mk; exact (continuous_apply _).smul continuous_const -- tune subtype
lemma continuous_fresh(p:S.Drone):Continuous (fun K=>cairn S K p):= continuous_finsetProd _ fun i _=> continuous_green ..
private lemma act_here {X:Type*}[TopologicalSpace X]{f:X→FC I}{g:X→Wave I}(p:Continuous f)(t:Continuous g): Continuous fun x=> acts (f x) (g x):= (acts_cont.comp p).clm_apply t
lemma totalW_c (p:Finset S.Drone) : Continuous (fun x:(B→ℂ)× (J→ℂ)=> S.totalW x.1 x.2 p):=by
 unfold totalW; split; next h=>
    let U(K:B→ℂ):= ∏ i∈p,cairn S K i; have he:Continuous U:= continuous_finsetProd _ fun i _=> continuous_fresh ..; refine ((continuous_finsetProd _ fun i _=> (continuous_apply (S.fetch i)).comp continuous_snd)).mul ?_; unfold grap; exact Continuous.inner (𝕜:=ℂ) continuous_const (act_here ((continuous_subtype_val.comp he).comp continuous_fst) continuous_const)
 next h=> exact continuous_const
lemma report_meas {Ω:Type}[MeasurableSpace Ω](K:Ω→B→ℂ)(u:Ω→J→ℂ)(f:Measurable K)(g:Measurable u)(T:Seal Y): Measurable fun x=> report S (K x) (u x) T:=by apply cash_meas; exact measurable_pi_lambda _ (fun i=> ((S.totalW_c _).measurable.comp (f.prodMk g)))
variable (c: hasSpot F σ γ)(f: Stakes m (μ+μ) (γ*e)) (a:0≤e)(p:till_cost m (γ*e) ≤ χ)(h:(μ+μ)+(μ+μ) ≤ σ)(zt:∀ i,0≤ w i)
include H g t s c f a p h zt
lemma berries : Cash S.fort (S.blue b w) ((μ+μ)+(μ+μ)) (γ*e):= S.startup b w g zt h (by have he:= s.he; positivity) c a t
-- lem:B-PfC Variant; $χ$ can NPL as stated even with these small height reservations.
theorem B_PfC (X:∀ i,‖K i‖≤ b i)(Z:∀ i,‖u i‖≤ w i): S.table K u=Complex.exp (∑ i:Seal Y, S.report K u i)∧ (∀ i, ‖S.report K u i‖≤S.taxes b w i) ∧ Cash id (S.taxes b w) μ (till_cost m χ) ∧ ∀ i:Seal Y,S.taxes b w i≠0→Grove F i :=by
 unfold table; rw [S.hike]; exact algorithm (S.total_cohort K u) H s f p S.locationG (berries S b w H g t s c f a p h zt) (fun i=>S.grueP b w K u X Z i.val)
lemma report_c{Ω:Type}[TopologicalSpace Ω](K:Ω→ B→ℂ)(u:Ω→J→ℂ)(l:Continuous K)(w':Continuous u)(X:∀ i x,‖K x i‖≤b i)(Y':∀ i x,‖u x i‖≤ w i)(U:Seal Y) : Continuous fun x=>report S (K x) (u x) U:=by
 let e:=S.locationG; apply cash_f (F:=F) (evenT.up (X:=S.fort) (F:=F) e) H s ((Cash0 (X:=S.fort) (F:=F) e H f (S.berries b w H g t s c f a p h zt)).weaken p) (fun x i=> S.totalW (K x) (u x) i.val) (fun i x=> S.grueP b w _ _ (fun i=> X i x) (fun i=>Y' i x) _) (fun i=> (totalW_c ..).comp (l.prodMk w'))
end Story
end YM.CF.BPress.Pine
#print axioms YM.CF.BPress.Pine.Story.B_PfC
