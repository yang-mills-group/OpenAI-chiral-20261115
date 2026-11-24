import YM.CF.Vp929.Phase.Teller
import YM.CF.Vp929.Canon.Macy
import YM.CF.Moto.Shaft
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
set_option quotPrecheck false
open Cycle929 Larch Bake Salt
variable {n:Side}{L:ℕ}{Q:BudgetPoint}{A h a c d:ℝ}
local notation "D'"=> RegBudget n
local notation "H"=> Scree.Hub n
local notation "Γ_"=> (H→H)
abbrev warp_E (F:H→ H)(A:D'):RegBudget n:=sunY univ F A
local notation "Sh"=> univ.filter (shortHub (n:=n) Q L)
abbrev ridge_Q (Q:BudgetPoint) (L:ℕ)(F:H→ H)(A:D'):Cusp n:=soot_T (univ.filter (shortHub (n:=n) Q L)) lagE (lagE∘F) (lagE∘F) (fun i=>oV (A i))
variable {F:Scree.Hub n→ Scree.Hub n} (p:Extension L Q n F)
namespace Extension
local notation "σ"=> Lag
local notation "δ"=> (mstar L)
include p
lemma settle (A:D') (V:Orbit n)(u: Rue.FleetS Q.threshold V.1): exponentL Q (warp_E F A) V.1+fuelV Q (ridge_Q Q L F A) V= exponentL Q A V.1:=by
 unfold warp_E ridge_Q exponentL;
 change exponentL Q (sunY _ _ _) _+_= ∑ i:H,numbE Q.threshold i.val.2 (A i) V.1; rw [release_v]; simp_rw [numb_b]; unfold soot_T; rw [Vow.tunes, sum_filter,← sum_add_distrib]; refine sum_congr rfl fun i _=>?_
 split; exact amends V _ _ _ (p.fill i).2 (Subset.refl _) (fun _ _=>rfl) u; next e=> rw [add_zero,p.held i e]
lemma convoy (F0:Sweep n→Prop)(A:RegBudget n)(u:IncX F0 A Q h c)(hs:0≤h) : IncX primeU (warp_E F A) Q h (Real.exp (Q.supportExponent*δ)*c) :=by
 obtain ⟨k,z,K⟩:=u.weight; let Γ:=Real.exp (Q.supportExponent*δ); have he(i:H):0 ≤ k i:= Beau.grit_p Q (z i) hs
 refine feat_v univ _ _ k Q _ (fun i _=> Moto.vaneL _ _ _ _ _ _ (z i) (p.fill i).2 (p.fill i).1) fun i=>?_
 have hg(j:H): (F j).val.1=i ↔ i=j.val.1:=((p.fill j).1 ▸ eq_comm)
 rw [sum_filter]; apply le_trans _ (mul_le_mul_of_nonneg_left (K i) (Real.exp_pos _).le); rw [Finset.mul_sum]; refine sum_le_sum fun j _=>?_
 by_cases hq:i=j.val.1
 · rw [if_pos hq,if_pos ((hg j).2 hq)]
   by_cases h:shortHub Q L j
   · refine le_trans (b:= Γ * k j) ?_ (mul_le_mul_of_nonneg_left (Q.loMass _ _ (he j)) (Real.exp_pos _).le); exact le_of_eq (by unfold BudgetPoint.mass; rw [p.cap j h])
   rw [p.held j h]; exact le_mul_of_one_le_left (mul_nonneg (Real.exp_pos _).le (he _)) (Real.one_le_exp (mul_nonneg Q.exponent_pos.le (by positivity)))
 rw [if_neg hq,if_neg (mt (hg j).mp hq),mul_zero]

abbrev yard (L:ℕ):=10*mstar L+3
abbrev wagon (L:ℕ)(K:ℕ)(θ:ℝ)(B:ℕ)(k:ℝ):= Larch.shine_C (yard L) θ*(Larch.tet_B (yard L) B*(Vow.chi_f K*k))
lemma rider {i:H}(h:shortHub Q L i) : (F i).val.2⊆Lattice.halo (yard L*Q.B) {i.val.1}:=by
 intro j v; refine halo_spec.mpr ⟨_,mem_singleton_self _,?_⟩; rw [(p.fill i).1]; apply (Corona.extent _ Q.B (F i).property v).trans; rw [p.cap i h]; unfold yard; have hp:= Q.B_pos; nlinarith only [hp,Nat.zero_le (mstar L),Nat.mul_le_mul_left (mstar L) (show 1 ≤ Q.B from hp)]
lemma canopy (F0:Sweep n→Prop)(A:RegBudget n)(u:IncX F0 A Q h c)(hs:0≤h)(hv:0≤d) : Packed Q h d (ridge_Q Q L F A) (wagon L Q.order d Q.B c):=by
 obtain ⟨k,z,K⟩:=u.weight; let D:=ridge_Q Q L F A; let Ψ(i:H):=Vow.chi_f Q.order*k i; let G:=fun i:H=>oV (A i)
 let W:= Sh; have e(i)(h:i∈W):shortHub Q L i:= (mem_filter.mp h).2; have t(i:H): Vow.Medal Q i.val.2 ∅ (G i) h (Ψ i):= rimR (z i) hs; have ht(i:H): (0:ℝ) ≤ k i:= Beau.grit_p Q (z i) hs
 have h'(o:Skye.Seat n):∑ j∈ W with j.val.1=o,Ψ j ≤ Vow.chi_f Q.order*c:=by
    unfold Ψ; rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ (spicy_f _); have hh:= (K o); refine le_trans ?_ hh; rw [sum_filter,sum_filter]; refine sum_le_sum fun i _=>?_
    by_cases t:i.val.1=o;
    · rw [if_pos t.symm]; split; · exact Q.loMass _ _ (ht i)
      exact mul_nonneg (Real.exp_pos _).le (ht _)
    simp [t,Ne.symm t]
 refine ⟨span_W W (lagE ∘ F) Ψ,Larch.amulet W (@Bake.lagE n) (lagE ∘ F) (lagE ∘ F) G Ψ (fun i _=> (p.fill i).2) (fun _ _=>Subset.refl _) (fun i _=>t i) (fun i _=> rimR (Moto.vaneL _ _ _ _ _ _ (z i) (p.fill i).2 (p.fill i).1) hs) hs,fun i=>?_⟩

 exact Larch.pump (F:=G) W Bake.lagE (lagE∘ F) Ψ (fun i _=> t i) hs (fun j:H=>j.val.1) d _ hv (fun j h=> p.rider (e j h)) h' i Q.B_pos
lemma oldSelf (A:RegBudget n) (i:H)(p0:shortHub Q L i): warp_E F A i=0:=sum_eq_zero (fun j h=>by have he:=(mem_filter.mp h).2; exact False.elim ((p.lands j) (he.symm ▸ p0)))
lemma oldS (A:RegBudget n) (i:H)(p0:shortHub Q L i): writ_E (warp_E F A) i=0:=by
 funext x; unfold writ_E; simp only [Pi.smul_apply, Finset.sum_apply]; change plight_C n • (∑ j:Sweep n,suit_Y j⁻¹ _) = (0:Cipher n); rw [sum_eq_zero,smul_zero]; intro j _; rw [p.oldSelf A _ ((dawnZ Q L j i).1 p0)]; exact map_zero _
end Extension
end Test
end YM.CF.Py.Rate
