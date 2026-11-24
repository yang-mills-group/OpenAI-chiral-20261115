import YM.CF.Mica.Roc
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
variable (R E:RegBudget n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
abbrev tray_H(r:ℕ):ℝ:=(fare_T 0:ℝ)*strive_E r
abbrev horse_E(k:ℕ)(v:Aura n→ℝ):=plight_C n • (tray_H k • (∑ s:Sweep n,zeal_F s v))
lemma raise_L (v:Aura n→ℝ)(P:BudgetPoint)(p:Larch.Anuk K v P h)(hx:0≤h): Larch.Anuk (writ_K (fun i D=>flavor_t (K i D))) (horse_E P.order v) P h:=by
 let E:= ∑ s:Sweep n,zeal_F s v; have hu:0≤tray_H P.order:= by unfold tray_H strive_E composeCost; positivity
 refine ⟨smul_nonneg (envy n).le (smul_nonneg hu (sum_nonneg fun s _ i=>p.1 (moldA s i))),fun i D x p'=>?_⟩
 unfold horse_E; rw [Pi.smul_apply,Pi.smul_apply, smul_eq_mul,smul_eq_mul, Finset.sum_apply,mul_sum]; let J:= ∑ s:Sweep n,force_V s (fun i D=>flavor_t (K i D))
 have hf(s:Sweep n): Medal P i.val D (force_V s (fun i D=>flavor_t (K i D)) i D) h (tray_H P.order * zeal_F s v i):=by
    let T:=moldA s i; let X:= actY s D; let W:= K T X; have ht:X.Nonempty:=map_nonempty.mpr x; have hQ:X ⊆ T.val:= map_subset_map.mpr p'
    change Medal P i.val D (turn_V s (flavor_t W)) h _;  exact (by rw [tray_H,mul_assoc]; exact boom_K P i.val D s (p.2 T X ht hQ) hx)
 have hk:=Medal.sumP univ (fun s:Sweep n=> force_V s (fun i D=>flavor_t (K i D)) i D) _ (fun i _=>hf i)
 let Z:= hk.rum (plight_C n); rw [Real.norm_of_nonneg (envy n).le] at Z; unfold writ_K; rw [Pi.smul_apply,Pi.smul_apply,Finset.sum_apply,Finset.sum_apply]; exact Z
variable(v:Aura n→ℝ)
lemma strait_G (u:∀ i:Seat n,tallB v k a i≤c)(l:ℕ)(o:Seat n): tallB (horse_E l v) k a o≤tray_H l*c:=by
 have hp:0≤ tray_H l:=by unfold tray_H strive_E composeCost; positivity
 unfold horse_E; rw [tall_s,tall_s]; have hx:tallB (∑ i:Sweep n,zeal_F i v) k a o=∑ i:Sweep n,tallB (zeal_F i v) k a o:=by unfold tallB; simp_rw [Finset.sum_apply,sum_mul]; exact sum_comm
 rw [hx]; have ht(i:Sweep n): tallB (zeal_F i v) k a o≤c:=by apply le_trans _ (u ((boxA i).symm o)); exact le_of_eq (by rw [←call_Q (k:=k) i v ((boxA i).symm o), Equiv.apply_symm_apply])
 refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=>ht i)) hp) (envy n).le) ?_; simp only [sum_const,card_univ,nsmul_eq_mul]; rw [mul_left_comm, feed]
end YM.CF.Ione
