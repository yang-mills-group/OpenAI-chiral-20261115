import GaugeFieldConstruction.Gospels
import GaugeFieldConstruction.Ixi
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
variable {N:Side}{X: Force N}{F: Cusp N} {K:ℕ}{p:BudgetPoint}{h:ℝ}
variable (G:Cusp N) (q:∀ X:Aura N,∀ D⊆X.val,∃ C:ℝ,Stax.Fray p h K X D (F X D) C)
include q
lemma pay_halo (g:budgetR (Vow.glowV F G) X ≠0): Lattice.halo K (extraD X)⊆X.val.1.val.2:=by
 let D:=extraD X; let A:=lordD X
 have he:¬∀ Y:Orbit N,budgetR (Vow.glowV F G) X Y=0:=fun f=>g (funext f); push Not at he; obtain ⟨V,e⟩:=he
 have hx: D⊆ A.val:= X.property.2
 have hk: Vow.glowV F G A D V ≠0:=fun v=>e (by change bassH _ • Vow.glowV F G _ _ _=0; rw [v,smul_zero])
 unfold Vow.glowV Palot.mintF at hk; rw [if_pos hx,Finset.sum_apply] at hk; obtain ⟨T,u,g⟩:=exists_ne_zero_of_sum_ne_zero hk
 rw [gear_v] at g; split at g; swap; · exact False.elim (g rfl)
 rename_i u; intro i y; obtain ⟨j,w,h⟩:= halo_spec.mp y; obtain ⟨a,v,b⟩:= deck_r A T hx u j w
 have hp: F a (D∩a.val) V ≠0:=by intro z; apply g; rw [Pi.mul_apply,Finset.prod_apply,prod_eq_zero v z,zero_mul]
 obtain ⟨C,p⟩:= q a (D∩a.val) inter_subset_right
 exact (stun_v A T u a v).2 ((p.loaf _ hp).1 (halo_spec.mpr ⟨j,b,h⟩))
omit q
variable {I:Type}[LinearOrder I][Fintype I]{σ:I→ Seat N}{W:Key I→ForceBudget N}(k:Π j:I,I→ℂ)
lemma tipK_halo (h:∀ x∈hill I,∀ i:Force N, W x i≠0→ Lattice.halo K (extraD i)⊆i.val.1.val.2)(Y:Finset I)(p:Bus2 W σ k Y X ≠ 0)(u:∀ i:Force N,∀ x,River (fun z=> W z i x)) : Lattice.halo K (extraD X)⊆X.val.1.val.2:=by
 by_contra hK; have he(z: Key I)(v:z∈hill I): W z X=0:=by by_contra t; exact hK (h z v X t)
 apply p; funext i; unfold Bus2; by_cases x:Y∈realm_C σ; · rw [fluid_Z _ _ _ (u X i) _ x]; exact (rer σ k _ (fun j v=>(lace_C j (g:=fun i=>0) (fun y g=>(congrFun (he y g) i)) roots).trans (tip_0 _))).trans (women ..) -- tune lambda shadows
 unfold streamArc; rw [if_neg x]; rfl
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
