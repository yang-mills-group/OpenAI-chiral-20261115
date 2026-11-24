import YM.CF.Stax.Render
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z:Aura n→ℝ)
variable {M:Orbit n→Aura n→ FC (Dwell n)}(T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> Cadre.chip (cribR z) r
local notation "Qd"=> nutL K F
local notation "Nd"=> nutL (cribR z) r
variable (w:0≤h)
open PowerSeries
-- total.Enforced majorant. Batt.Instant α.Gen anchored n0. One PS evaluate.
abbrev rem_X (X: VX)(D:Support (More n)): Copy n:=Vow.lasting P X.val D (fun i:ℕ=> coeff i (Qd X D))
abbrev birthL (X: VX)(D:Support (More n)): Copy n:=if D=∅ then K X ∅ X 1 else 0
abbrev lamp (X:VX)(D:Support (More n)): Copy n:=F X D+birthL K X D+rem_X (P:=P) F K X D
abbrev δWeight(γ: VX→ ℝ)(X:VX)(D:Support (More n)):ℝ:= if D=∅ then γ X else 0
variable (V:Orbit n)(p:FleetS P.threshold V.1)
local notation "Θ"=> flags P.threshold V.1
variable (w':1≤h)
include T w' hF
lemma aptL (X:VX)(D:Support (More n))(u:D⊆X.val):Fray P h δ X D (birthL K X D) (δWeight z X D):=by
 unfold birthL δWeight; split; next v=> rw [v]; exact (FrayCast True.intro)
 exact ⟨Medal.zeroT,fun i p=>False.elim (p rfl)⟩
where FrayCast(T_:True):Fray P h δ X ∅ (K X ∅ X 1) (z X):=by simpa only [mul_one] using T.plays X ∅ (empty_subset _) X (subset_refl _) 1 1 (show Fray P h δ X ∅ 1 1 from ⟨Medal.oneT,fun i x=>by simp [Lattice.halo]⟩)
lemma rem_K (X:VX)(D:Support (More n))(u:D⊆ X.val)(t:Aqua (Nd X D)): Fray P h δ X D (rem_X (P:=P) F K X D) (hitU (Nd X D)):=by
 let V(i):= deck F r hF K z T (zero_le_one.trans w') X D u i; refine ⟨Vow.vaut (fun i=> (V i).merit) t.of_norm w',fun i f=>?_⟩; unfold rem_X Vow.lasting zenS at f; split_ifs at f with g; swap; exact False.elim (f rfl)
 by_contra p; apply f; have hu(n:ℕ): coeff n (Qd X D) i=0:=by by_contra t; exact p ((V n).loaf i t)
 simp_rw [hu,tsum_zero]
omit T w' hF
variable {A:Type*}[NormedCommRing A][CompleteSpace A]
lemma leanF (z:A):Aqua (PowerSeries.C z)∧ hitU (PowerSeries.C z)=z:=by
 unfold Aqua hitU; simp_rw [coeff_C]; constructor; exact summable_of_ne_finset_zero (s:={0}) (fun i h=>by rw [if_neg (show i≠0 from fun t=> h (Finset.mem_singleton.mpr t)),norm_zero]); rw [tsum_eq_single 0]; simp; intro i v; rw [if_neg v]
lemma zeno(z:A):Aqua (PowerSeries.mk (R:=A) fun n:ℕ=> if n=1 then z else 0)∧ hitU (PowerSeries.mk (R:=A) fun n:ℕ=>if n=1 then z else 0)=z:=by unfold Aqua hitU; simp_rw [coeff_mk]; constructor; exact summable_of_ne_finset_zero (s:={1}) (fun i h=>by rw [if_neg (show i≠1 from fun t=> h (Finset.mem_singleton.mpr t)),norm_zero]); rw [tsum_eq_single 1]; simp; intro i v; rw [if_neg v]
lemma inking(Z r:A)(P U: PowerSeries A)(p:P=C Z+ PowerSeries.mk (fun x=>if x=1 then r else 0)+U)(g:Aqua U):hitU P=Z+r+hitU U:=by
 obtain ⟨w,l⟩:= (leanF Z).1.sip (zeno r).1; rw [p,(w.sip g).2,l,(leanF Z).2,(zeno r).2]
include T w' hF
lemma cell(X:VX)(D:Support (More n))(x:Aqua (Nd X D))(p:D⊆ X.val):Fray P h δ X D (lamp (P:=P) F K X D) (hitU (N X D)):=by
 rw [inking (r X D) (δWeight z X D) _ (Nd X D) ?_ x]; swap
 · nth_rw 1 [park D (cribR z) _ _ (by simp [cribR])]; congr 2; ext i; simp only [coeff_mk,cribR,mul_one]; unfold δWeight; split_ifs <;> tauto -- tune see Amb
 let V:= rem_K F r hF K z T w' X D p x; let L:= aptL F r hF K z T w' X D p
 refine ⟨((hF _ _ p).merit.plus L.merit).plus V.merit,fun i w=>?_⟩; by_contra f; obtain hv|hv:= eq_or_ne (F X D i) 0; swap; · exact f ((hF X D p).loaf i hv)
 obtain hl|hl:= eq_or_ne (birthL K X D i) 0; swap; · exact f (L.loaf i hl)
 apply f; apply V.loaf; unfold lamp at w; simp only [Pi.add_apply,hv,hl,zero_add] at w; exact w
include p
lemma saveK (X:VX)(D:Support (More n))(u:D=Θ∩ X.val)(t:Aqua (Nd X D)):hitU (cumQ F K V P X)=lamp (P:=P) F K X D V:=by
 have hx:D⊆ X.val:=u.symm ▸ inter_subset_right; have hu:= fair F r hF K z T V p w' X D u
 let W':=fL (Qd X D) V; have hR:Aqua W':=by
    unfold W' Aqua; simp_rw [fP]; apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (t.of_norm); intro i; exact (deck F r hF K z T (zero_le_one.trans w') _ _ hx i).merit.capF w' V hu
 have he:rem_X (P:=P) F K X D V= hitU W':=by unfold rem_X Vow.lasting zenS; rw [if_pos (hates hu)]; unfold hitU W'; simp_rw [fP]
 unfold lamp; rw [Pi.add_apply,Pi.add_apply,he]; refine inking _ _ _ W' ?_ hR -- tune
 apply PowerSeries.ext; intro i; unfold cumQ; rw [←u,fP]; nth_rw 1 [Cadre.park _ _ _ _ T.start]; rw [map_add,map_add,map_add,map_add,coeff_C,coeff_C,coeff_mk,coeff_mk,Pi.add_apply,Pi.add_apply,show coeff i W'=_ from fP V (Qd X D) i]; unfold birthL; split_ifs <;> first|tauto|simp_all
end YM.CF.Stax
