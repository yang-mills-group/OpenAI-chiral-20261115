import YM.CF.Rive.Muck
import YM.CF.Pso.Pick
import YM.CF.Ione.Pose
import YM.CF.Ione.Lean
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Rive
open Mew Ione
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
open Vow Larch Rue Push.AbsoluteSums Trees Ursell
-- two readings; sum-bound tail with varying witnesses at fixed price
variable{C:Type}[Fintype C][LinearOrder C] (Vb:Mew.Key C→ Pax n) (P:BudgetPoint)
variable (hp1:1≤h)(g:∀ x:Aura n,∀ y,River (fun z:Key C=> Vb z x y)){B:ℕ}{δ S a q:ℝ} (X:Mew.Key C→ Aura n→ℝ)(u:0 ≤ a)(s:∀ i∈hill C,Ready Palot.stern B (X i) a S δ q) (o:∀ i∈hill C,∀ x, Medal P x.val ∅ (Vb i x) h (X i x)) (qh:0 ≤ q)(qt:q<1)
include u g hp1 o s qh qt
open Bake Gas
lemma lore_Y(i:Aura n)(y:Orbit n) : River (fun i' : Key C=> FeeD P (Vb i') i y):=by
 by_cases v:visible P i.val ∅ y.1; swap; · have he(z): FeeD P (Vb z) i y=0:=if_neg v; simp_rw [he]; exact zeroR _
 let f(z:Key C)(p:Clusters (Aura n)):= sta (Vb z) i 0 p y
 let L(z:Key C)(m p:ℕ):= funge i (Vb z) m p y; let Z(z:Key C)(p:ℕ):= L z 0 p
 obtain ⟨j,k⟩:=i.property; obtain ⟨V,w,t⟩:=(show visible P i.val ∅ y.1 from v); let K:=(V,y.2); have hV0:= w; rw [sdiff_empty] at hV0
 have ht(z:Key C):FeeD P (Vb z) i y= ∑' p:ℕ,Z z p:=if_pos v
 have hs(j):River fun z=>Z z j:=by
    unfold Z L funge; simp_rw [Finset.sum_apply]; refine tick_sum _ _ (fun k _=>?_); let p:Clusters (Aura n):=⟨j,k⟩
    change River (fun z=>sta (Vb z) i 0 p y); unfold sta; split; swap; exact zeroR _
    unfold guava; simp_rw [Pi.smul_apply,Finset.prod_apply]; exact bScale _ (cost_R _ _ (fun a _=>g _ _)) (coefficient gRule p.2/(p.1+1).factorial) -- tune
 have hp(z)(hy:z∈hill C)(m):0 ≤ spanD i (X z) m :=tsum_nonneg (fun p=>(ponder i p hp1 (o z hy) m).wage (zero_le_one.trans hp1))
 have hx(z:Key C)(hy:z∈hill C)(m:ℕ): ‖Z z m‖ ≤ spanD i (X z) m:=by
    have hh: Summable (sepV (X z) i m):= glomM i (s z hy) u; have h(j:ℕ):0 ≤ (∑' k:Tuple (Aura n) j, sepV (X z) i m ⟨j,k⟩):=tsum_nonneg fun p=>(ponder i _ hp1 (o z hy) m).wage (zero_le_one.trans hp1)
    let c(z:Key C)(p):= ∑ l:Tuple (Aura n) p, (sepV (X z) i m ⟨p,l⟩); have he: c z m ≤ spanD i (X z) m:=by rw [spanD,hh.tsum_sigma]; rw [show c z m= ∑' j:Tuple (Aura n) m,sepV (X z) i m ⟨m,j⟩ from (tsum_fintype _).symm]; exact Summable.le_tsum hh.sigma m (fun u h'=>h u)
    refine le_trans ?_ he; change ‖funge i (Vb z) 0 m y‖ ≤_; unfold funge; rw [Finset.sum_apply]; apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=> ?_; let p:Clusters (Aura n):=⟨m,j⟩; have ht:sta (Vb z) i 0 p=sta (Vb z) i m p:=by unfold sta; rw [show p.1=m from rfl]; simp
    change ‖sta (Vb z) i 0 p y‖≤ _; rw [ht,(ponder i p hp1 (o z hy) m).same y K t (fun _ _=>rfl)]; exact (ponder i p hp1 (o z hy) m).capF hp1 K w
 have hc(z:Key C)(hy:z∈hill C)(m:ℕ): ‖Z z m‖ ≤ q^m*(S*(1-q)⁻¹):=by
    refine (hx z hy m).trans ?_; let w(y:Aura n):=spanD y (X z) m * Trees.currency B a y.val
    have hx:spanD i (X z) m≤w i:= le_mul_of_one_le_right (hp z hy m) (Real.one_le_exp (mul_nonneg u (Nat.cast_nonneg _)))
    have hc':w i≤ S*q^m*(1-q)⁻¹:=(single_le_sum (f:=w) (fun j' _=> mul_nonneg (tsum_nonneg (fun p=>(ponder j' p hp1 (o z hy) m).wage (zero_le_one.trans hp1))) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ i,k⟩)).trans (thinX (s z hy) u j m)
    exact (hx.trans hc').trans_eq (by ring)
 simp_rw [ht]; exact bill_t _ hs ((summable_geometric_of_lt_one qh qt).mul_right _) (fun z p i=>hc z p i)
end YM.CF.Rive
