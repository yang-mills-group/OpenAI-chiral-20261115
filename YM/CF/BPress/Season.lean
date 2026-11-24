import YM.CF.BPress.Measure
import YM.CF.BPress.Age.Fawn
/-!
 # B pressure theorem, purchase and scope.

 The prechoice strengthenings in `Age` prove main attainable on MeterQ directly.
 Estimator holds on _any_ such histories, including horizons with other provisions.
 No comparison lemma yet in this assertion (purchasing on compatible comparator options
 needs the other arc/Menu for that choice). This chapter and VolumeB result
 use **any** such arc -- see also the general `Sage` assertion applicable unchanged.
 Sage_tuning interface makes export ready for arcs with HoldsUC etc.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BPress
open Function Finset Set MeasureTheory Filter Lattice RG Precision Pressure Push.SectorMeasure
open Cube Py Vale Vale.Grace Paige Scree Skye Fixed Dial Spire SU Wilson Locale Calendar Calendar.Around
open Engine Before Between LocalH Next.SectorChange Hazel Net Honey Fief
open scoped Topology BigOperators Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m s B:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K R L} {d x h p c:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} {J:Robes Mstar V W}
variable (V) (p) (P: Before V p) (v:LocalRatio L)
-- write explicit timing (take $J$ Robes from comparison options BEFORE h). select any seam margin $z≥3*l_B$. output true quantifier Day gain.
include v in
lemma sage_tuning (A:d≤ P.dcap)(tP:p ≤ W.pearl.q)(J:Robes Mstar V W)(z:ℕ): ∃ (X:P.Between d J.n)(E:Earning X), z ≤ X.collar ∧ ∃ D:Day E, ∀ᶠ h:ℝ in atTop, ∀ᶠ x:ℝ in atTop, Sage D h x:=by
 obtain ⟨U,w⟩:= P.between J.n z d A; obtain ⟨E⟩:= escape U tP; obtain ⟨T⟩:= empire E v; exact ⟨U,E,w,T,(eventually_ge_atTop (height E)).mono fun i p=> purchase_day T A tP p⟩

-- nonempty both purchase & entire input with arbitrarily large seam and sides, TRUE unbounded cutoff horizon.Any funnel.Pop.Time. strengthening with cofinal x intact. Kernel choice resonance not included.VClip. includes e_guard and $coffer controls.Weight.Palette.G$. cP ≤1 not used budget.
theorem main_prechoices : ∃ (K:Teller group)(L:ChartRatio group)(n:ℕ),LocalRatio L∧ K.j=4∧ K.top.clip.direct≤1 ∧ ∀ (R:Patch), n≤R.L.val→ R.J=4→∃ (V: Grace K R L) (T:Acorn.Repair K.j)(k:ℕ), 1≤ k ∧ ∀ B':ℕ, k≤B'→∃ (e p:ℝ)(P:Before V p), 0<e ∧ 0<p ∧ e≤ P.dcap ∧ ∀ q:Chi,∀ d:ℝ, 0<d→ d≤e→ ∃ (U:Grasp V.U (R.L^B') d)(W:GivenX V U)(Mstar:Side) (J:Robes Mstar V W), U.baseline≤T.d ∧ J.k≤ J.roomX ∧ p=W.pearl.q ∧ ∀ z:ℕ, ∃ (X:P.Between d J.n)(E:Earning X)(D:Day E), z≤ X.collar∧ ∀ᶠ h:ℝ in atTop,∃ (N:ℕ)(R0 δ:ℝ→ℝ), 1 ≤ h ∧ sizeK R.L 2 R0 ∧ Chill_v δ ∧ ∀ u:ℝ, ∃ (x:ℝ)(H:Month x 1 6 2 N V W), u<x∧Sage D h x∧ MeterQ V 1 2 6 N J q h R0 δ x H:=by
 obtain ⟨K,L,h,g,l,c,n,V⟩:= interval_pC 4 6 2 1 (by norm_num) (by norm_num) (by norm_num) (by decide) one_pos; refine ⟨K,L,n,g,h,l,fun R p t=>?_⟩; obtain ⟨V,T,i,H⟩:=V R p t; refine ⟨V,T,i+1,by omega,fun B r=>?_⟩; obtain ⟨e,p,w,h,Y⟩:=H B (by omega); obtain ⟨P⟩:= before V w; refine ⟨min e P.dcap,p,P,lt_min h P.d_pos,w,min_le_right ..,fun q d h k=>?_⟩; obtain ⟨U,W,M,J,e,t,d',Z⟩:=Y q d h (k.trans (min_le_left ..)); refine ⟨U,W,M,J,t,d',e.symm,fun y=>?_⟩ -- check reorder W.pearl.q etc
 obtain ⟨X,E,v,D,H⟩:= sage_tuning V p P g (k.trans (min_le_right ..)) e.symm.le J y; refine ⟨X,E,D,v,?_⟩; filter_upwards [Z,H,eventually_ge_atTop (1:ℝ)] with h z h' v; obtain ⟨N,d,t⟩:=z; obtain ⟨Q,F,G,r,Y,h₁,h₂,h₃,A⟩:= t 0; refine ⟨N,Q,r,v,Y,h₃,fun u=>?_⟩; obtain ⟨y,l⟩:= eventually_atTop.1 h'; obtain ⟨x,t,H,x'⟩:= A (max u y); exact ⟨x,H,(le_max_left ..).trans_lt t,l x ((le_max_right ..).trans t.le),x'⟩ -- tune unused h¹

-- verify one can obtain such R and Chi. Then Admit and D.Appear use Sage.scope. History families at every such X use span_size.
lemma largePatch (n:ℕ): ∃ R: Patch,n ≤ R.L.val∧ R.J=4:=by
 let p:=2*(n+1)+1; exact ⟨⟨⟨p, by unfold p; omega⟩,4,le_rfl,by change 3≤p; unfold p; omega, ⟨n+1,rfl⟩⟩,by change n≤p; unfold p; omega,rfl⟩
example : Nonempty Chi:= ⟨Chi.canonical⟩
end YM.CF.BPress
#print axioms YM.CF.BPress.B_main
#print axioms YM.CF.BPress.main_prechoices
#print axioms YM.CF.BPress.Sage.B_hit
#print axioms YM.CF.BPress.Sage.tall -- production
#print axioms YM.CF.BPress.Sage.scope -- layout existence
#print axioms YM.CF.BPress.span_size -- horizon existence
