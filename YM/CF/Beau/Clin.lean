import YM.CF.Beau.Lunge
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
variable(P:BudgetPoint)(T:RegBudget n)(A:Scree.Hub n→ℝ)(Γ:ℝ) (L:ℕ)(hG:DayT P.order Γ)(p:0≤Γ)(hv:1 ≤ h)
local notation "U'"=> chipT P L A
variable (v:∀ X:Scree.Hub n,PressB P X (T X) h (chipT P L A X))(t:Pant T)(hw:60 < (More n).val)(h6:6≤P.B)(g:∀ i:Skye.Seat n,(∑ j:Scree.Hub n with j.val.1=i,P.mass j.val.2 (chipT P L A j)) ≤x)
abbrev Coil(T:RegBudget n):RegBudget n:= sunY univ stateT (mowR T)
abbrev fee_l(P:BudgetPoint)(Γ:ℝ):ℝ:= |inS P Γ| * Real.exp (81*P.supportExponent)
local notation "E"=> Coil T
local notation "η"=> P.supportExponent
local notation "ρx"=> (fee_l P Γ*x)
local notation "Tt"=> threshold
include hG p hv v t hw h6 g
lemma polo_B : IncX (fun _=>False) E P h ρx ∧ Ionic P L E ∧∀ V:Orbit n,exponentL P E V.1=∑ X:Scree.Hub n, CoatL T P V X:=by
 have hz:=zero_le_one.trans hv; let f(i):=inS P Γ * chipT P L A i; have he(i): PressB P (stateT i) (mowR T i) h (f i):= crescent T _ v hz hG p
 have hy(i): 0 ≤ chipT P L A i:= Beau.grit_p P (v i) hz
 refine ⟨feat_v univ stateT (mowR T) f P _ (fun i _=> he i) (fun i=>?_),fun i a b=> add_Z (P:=P) (X₀:=i) _ _ f ?_ ?_ hz, fun V=>release_v univ stateT (mowR T) P V⟩
 · refine le_trans ?_ (mul_le_mul_of_nonneg_left (g i) (by unfold fee_l; positivity)); rw [Finset.mul_sum]; change (∑ j:Scree.Hub n with j.val.1=i, P.mass (villa j) (f j)) ≤ _; apply sum_le_sum; intro j _; have he:P.mass (villa j) (f j)= inS P Γ * P.mass (villa j) (U' j):= mul_left_comm ..; have hp':= hy j
   rw [he,fee_l, mul_assoc |inS P Γ|]; exact mul_le_mul (le_abs_self _) (latch_K P (U' j) hp' _ h6) (mul_nonneg (Real.exp_pos _).le hp') (abs_nonneg _)
 · intro j y; have h:=rootB T j t v hz hG p hw (by rw [← (mem_filter.mp y).2] at a; exact a); rw [← (mem_filter.mp y).2]; exact ⟨h.mute,h.muteT⟩ -- costly
 intro j y; exact (mem_filter.mp y).2 ▸ he j
lemma feel : P.threshold^2*|lureC (realH T)| ≤ ‖Complex.reCLM‖ * x:=by
 have hz:=zero_le_one.trans hv
 exact cash_b T t v hz hw x fun i=> (sum_le_sum (fun j _=>P.loMass _ _ (grit_p P (v _) hz))).trans (g i)
lemma ton_P: 0≤x:=by
 have hz:=zero_le_one.trans hv; exact (sum_nonneg (fun i _=>mul_nonneg (Real.exp_pos _).le (grit_p P (v i) hz))).trans (g 0)
abbrev voids(T:RegBudget n): Cusp n:= ∑ i:Scree.Hub n, pamE T i
abbrev horn_v(P:BudgetPoint)(L:ℕ)(Γ:ℝ):ℝ:= |blazeP P Γ 1| * Real.exp ((P.supportExponent+1+1)*(L+ (81:ℕ):ℝ)) -- annotation
abbrev belt_K(P:BudgetPoint)(L:ℕ)(Γ:ℝ):ℝ:= ((hinge_P P.B L+hinge_P P.B L+1)^4:ℕ)* horn_v P L Γ
abbrev artV(i:Scree.Hub n)(V:Aura n):ℝ:= if V=pur (stateT i) then blazeP P Γ (U' i) else 0
local notation "sA"=> (∑ i:Scree.Hub n,artV P A Γ L i)
lemma mob_l : Thr (voids T) sA P h:=by
 intro i D; unfold voids; rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_apply]; -- third pays
 apply Medal.sumP; intro j _; unfold pamE chasmR artV; split; · rename_i y; rw [y,Pi.single_eq_same]; exact Taxi.pearlZ T j v (zero_le_one.trans hv) hG p D
 rename_i q; rw [Pi.single_eq_of_ne q]; exact Vow.Medal.zeroT
lemma costU(o: Skye.Seat n):tallB sA P.B (η+1+1) o ≤ belt_K P L Γ*x:=by
 let Z:= univ.filter fun j:Aura n=>o∈j.val; let J:= artV P A Γ L; let r:=η+1+1; let Y:=∑ j:Hz, J j; unfold tallB; simp_rw [Finset.sum_apply,sum_mul]; rw [sum_comm]; let q:= hinge_P P.B L; let T' :=univ.filter fun j:Hz=> chute P L j ∧ o∈ villa j; let C (j : Hz):= U' j
 let U:Site (More n):=o; let V:=halo q {U}; let H:=horn_v P L Γ; have hH:0 ≤ H:=by unfold H horn_v; positivity
 have hu:0 ≤ x:=ton_P P T A Γ L hG p hv v t hw h6 g
 have hp(i):0 ≤ C i:= grit_p P (v i) (zero_le_one.trans hv)
 let A₀(i:Hz):ℝ:= ∑ j∈Z, artV P A Γ L i j *currency P.B r j.val
 have he(i:Hz)(q:i ∉ T'): A₀ i=0:=by
    refine sum_eq_zero (fun j y=>?_); unfold artV; split; swap; exact zero_mul _
    rename_i z'; unfold chipT; rw [if_neg (show ¬chute P L i from fun g=>q (mem_filter.mpr ⟨mem_univ _,g,show o∈(pur (stateT i)).val from z' ▸ (show o∈j.val from (mem_filter.mp y).2)⟩)), blazeP]; simp [liteV,composeCost,tollV] -- tune
 have ht(i:Hz)(y:i∈ T'): A₀ i ≤ H * C i:=by
    let S:= pur (stateT i); have hz:o∈ S.val:= (mem_filter.mp y).2.2; have hx:chute P L i:= (mem_filter.mp y).2.1
    unfold A₀; rw [sum_eq_single S]; rotate_left
    · intro j u t; unfold artV; rw [if_neg t,zero_mul]
    · exact fun g=>False.elim (g (mem_filter.mpr ⟨mem_univ _,hz⟩))
    unfold artV; rw [if_pos (show S= _ from rfl)]
    have hQ:blazeP P Γ (U' i)=blazeP P Γ 1*C i:=by unfold C blazeP Taxi.liteV composeCost tollV; ring
    have vQ:0≤η+1+1:=by have h:=P.exponent_pos; positivity
    have hV: coverNumber P.B (villa i) ≤ L+81:=by
       let k:=coverNumber P.B i.val.2; have ht:k^3 < L:=hx; apply (crop_p P i (by simpa using h6)).trans; suffices k≤L from Nat.add_le_add_right this _
       by_cases h:1 ≤ k; exact ((pow_one k).symm.trans_le (pow_le_pow_right₀ h (show 1≤3 by decide))).trans ht.le
       omega
    rw [hQ]; unfold H horn_v
    calc
       _ ≤ (|blazeP P Γ 1| * C i)*Real.exp ((η+1+1)*((L:ℝ)+81)):=mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (hp i)) (Real.exp_monotone (mul_le_mul_of_nonneg_left (show (coverNumber P.B (villa i):ℝ) ≤ L+81 from (by exact_mod_cast hV)) vQ)) (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (hp i)) -- mul_le_mul instead.
       _ = _ := by push_cast; ring
    -- order?
 change ∑ i:Hz,A₀ i ≤ _; rw [←sum_subset (subset_univ T') (fun i _=>he i)]; refine (sum_le_sum ht).trans ?_
 have hz(i:Skye.Seat n): (∑ j ∈ T' with j.val.1=i,C j) ≤x:=by apply (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (subset_univ _)) (fun j _ _=>hp _)).trans; exact (sum_le_sum (fun j _=>P.loMass _ _ (hp _))).trans (g i)
 rw [← mul_sum,←sum_fiberwise_of_maps_to (g:=fun i:Hz=>i.val.1) (s:= T') (t:=V) (fun i h=> ?_)] -- tune
 · calc
      _ ≤ H*(V.card*x) :=mul_le_mul_of_nonneg_left ((sum_le_sum fun i _=> hz i).trans_eq (by simp)) hH
      _ ≤ _:=by
         have he: V.card≤(q+q+1)^4:= (Corona.halo_size {U} q).trans_eq (by simp); unfold belt_K
         have hp: H*(V.card*x) ≤ (((q+q+1)^4:ℕ):ℝ)*(H*x):=(mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) hu) hH).trans_eq (mul_left_comm ..); exact hp.trans_eq (mul_assoc ..).symm
 exact halo_spec.mpr ⟨U,mem_singleton_self _,(separation_comm _ _).trans_le (reachX P L i (mem_filter.mp h).2.1 U (mem_filter.mp h).2.2 h6)⟩
end YM.CF.Beau
