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
open Vow Larch Rue Push.AbsoluteSums Trees Ursell
-- two readings; sum-bound tail with varying witnesses at fixed price
variable{C:Type}[TopologicalSpace C] (Vb:C→ Pax n) (P:BudgetPoint)
abbrev PointF {C:Type}[TopologicalSpace C] (F:C→ Pax n):Prop:=∀ i:Aura n,∀ y:Orbit n,Continuous (fun z=>F z i y)
abbrev Saw_F {C:Type}[TopologicalSpace C] (F:C→ Pax n)(P:BudgetPoint):Prop:=∀ i:Aura n,∀ y:Orbit n,pingS P.threshold i.val y.1 → Continuous (fun z=>F z i y)
abbrev PointK {C:Type}[TopologicalSpace C] (F:C→ Vow.Cusp n):Prop:= ∀ i:Aura n,∀ D:Support (More n),∀ y:Orbit n,Continuous (fun z=>F z i D y)
abbrev Saw_K {C:Type}[TopologicalSpace C] (F:C→ Vow.Cusp n)(P:BudgetPoint):Prop:=∀ i:Aura n,∀ D⊆ i.val,∀ y:Orbit n,pingS P.threshold (i.val\D) y.1 → Continuous fun z=>F z i D y
variable (hp1:1≤h)(g:Saw_F Vb P){B:ℕ}{δ S a q:ℝ} (X:C→ Aura n→ℝ)(u:0 ≤ a)(Q:∀ i,X i = X i)(v:∀ i,X i ≥0)(s:∀ i,Ready Palot.stern B (X i) a S δ q) (o:∀ i,∀ x, Medal P x.val ∅ (Vb i x) h (X i x)) (qh:0 ≤ q)(qt:q<1)
include u g hp1 o s qh qt
open Bake Gas
lemma lore_B : PointF (fun i=> FeeD P (Vb i)):=by
 intro i y; by_cases v:visible P i.val ∅ y.1; swap; · have he(z): FeeD P (Vb z) i y=0:=if_neg v; simp_rw [he]; exact continuous_const
 let f(z:C)(p:Clusters (Aura n)):= sta (Vb z) i 0 p y
 let L(z:C)(m p:ℕ):= funge i (Vb z) m p y; let Z(z:C)(p:ℕ):= L z 0 p
 obtain ⟨j,k⟩:=i.property; obtain ⟨V,w,t⟩:=(show visible P i.val ∅ y.1 from v); let K:=(V,y.2); have hV0:= w; rw [sdiff_empty] at hV0
 have ht(z:C):FeeD P (Vb z) i y= ∑' p:ℕ,Z z p:=if_pos v
 have hs(j):Continuous fun z:C=>Z z j:=by
    unfold Z L funge; simp_rw [Finset.sum_apply]; refine continuous_finsetSum _ fun k _=>?_ ; let p:Clusters (Aura n):=⟨j,k⟩
    have hh(z:C):sta (Vb z) i 0 p y=sta (Vb z) i 0 p K:= (ponder i p hp1 (o z) 0).same y K t (fun _ _=>rfl); change Continuous (fun z=>sta (Vb z) i 0 p y); rw [funext hh]
    unfold sta; split; swap; · exact continuous_const
    next h=> unfold guava; simp_rw [Pi.smul_apply,Finset.prod_apply]; refine Continuous.smul (continuous_const (y:=(coefficient gRule p.2/(p.1+1).factorial:ℝ))) (continuous_finsetProd _ fun a _=>?_ ) -- tune
             exact g (p.2 a) K (fun j x=> hV0 _ (fun z=>x (Disjoint.mono_left (show (p.2 a).val⊆i.val from h.1 ▸ rimY p a) z))) -- tune
 have hp(z m):0 ≤ spanD i (X z) m :=tsum_nonneg (fun p=>(ponder i p hp1 (o z) m).wage (zero_le_one.trans hp1))
 have hx(z:C)(m:ℕ): ‖Z z m‖ ≤ spanD i (X z) m:=by
    have hh: Summable (sepV (X z) i m):= glomM i (s z) u; have h(j:ℕ):0 ≤ (∑' k:Tuple (Aura n) j, sepV (X z) i m ⟨j,k⟩):=tsum_nonneg fun p=>(ponder i _ hp1 (o z) m).wage (zero_le_one.trans hp1)
    let c(z:C)(p):= ∑ l:Tuple (Aura n) p, (sepV (X z) i m ⟨p,l⟩); have he: c z m ≤ spanD i (X z) m:=by rw [spanD,hh.tsum_sigma]; rw [show c z m= ∑' j:Tuple (Aura n) m,sepV (X z) i m ⟨m,j⟩ from (tsum_fintype _).symm]; exact Summable.le_tsum hh.sigma m (fun u h'=>h u)
    refine le_trans ?_ he; change ‖funge i (Vb z) 0 m y‖ ≤_; unfold funge; rw [Finset.sum_apply]; apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=> ?_; let p:Clusters (Aura n):=⟨m,j⟩; have ht:sta (Vb z) i 0 p=sta (Vb z) i m p:=by unfold sta; rw [show p.1=m from rfl]; simp
    change ‖sta (Vb z) i 0 p y‖≤ _; rw [ht,(ponder i p hp1 (o z) m).same y K t (fun _ _=>rfl)]; exact (ponder i p hp1 (o z) m).capF hp1 K w
 have hc(z:C)(m:ℕ): ‖Z z m‖ ≤ q^m*(S*(1-q)⁻¹):=by
    refine (hx z m).trans ?_; let w(y:Aura n):=spanD y (X z) m * Trees.currency B a y.val
    have hx:spanD i (X z) m≤w i:= le_mul_of_one_le_right (hp z m) (Real.one_le_exp (mul_nonneg u (Nat.cast_nonneg _)))
    have hc':w i≤ S*q^m*(1-q)⁻¹:=(single_le_sum (f:=w) (fun j' _=> mul_nonneg (tsum_nonneg (fun p=>(ponder j' p hp1 (o z) m).wage (zero_le_one.trans hp1))) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ i,k⟩)).trans (thinX (s z) u j m)
    exact (hx.trans hc').trans_eq (by ring)
 simp_rw [ht]; exact continuous_tsum hs ((summable_geometric_of_lt_one qh qt).mul_right _) (fun i z=>hc z i)
end YM.CF.Ione
