import YM.CF.DPress.Motto.Yawn
import YM.CF.BPress.Wealth.Groves
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open DPress.Plaque Larch Ione Taxi Bake Salt
namespace WagesC
variable {n:Side}{k L:ℕ}(P:BudgetPoint){a h b:ℝ}
local notation "Sx"=> Point n
structure Blend (n:Side)(k:ℕ) where
 μ: Point n→ Point n→ℝ
 p(i j): 0≤μ i j
 card(i):∑ j,μ i j=1
 near :∀ i j,μ i j≠0→ separation i j ≤ k
variable (B:Blend n k)
namespace Blend
abbrev liveW (X Y:Point n):Prop:= separation X Y ≤ k -- implicit k? drop
abbrev κN(n:Side)(k:ℕ): Finset (Point n × Point n) := univ.filter fun i=>separation i.1 i.2≤ k
abbrev χΩ(v:Sx×Sx) := κov v.1 v.2
abbrev coinP(v:Sx×Sx) := υκ v.1 v.2
-- transl equiv.x y notation on fermion coarse-root.
protected abbrev even (s:Sweep n): Prop:= ∀ i j, B.μ ( (boxA s).symm i) ((boxA s).symm j)=B.μ i j
abbrev τσ(s:Sweep n): Equiv.Perm (Sx × Sx):= Equiv.prodCongr (boxA s).symm (boxA s).symm
lemma similar(v:Sx × Sx)(s:Sweep n):v∈κN n k ↔ τσ s v∈κN n k:=by
 simp only [κN,mem_filter,mem_univ,true_and,τσ,Equiv.prodCongr_apply]; nth_rw 1 [←Equiv.apply_symm_apply (boxA s) v.1,←Equiv.apply_symm_apply (boxA s) v.2]; rw [sitT]; rfl -- tune rhs introduced metas.
lemma ride(v:Sx×Sx)(s:Sweep n): χΩ (τσ s v)=moveHub s (χΩ v):=Subtype.ext (Prod.ext rfl (by change haloW ((boxA s).symm v.1)∪haloW ((boxA s).symm v.2)=_; rw [moving_halo,moving_halo]; exact (Finset.map_union ..).symm)) -- tune
lemma coinΩ(s:Sweep n)(v:Sx×Sx): coinP (τσ s v) = moldA s (coinP v):=Subtype.ext (congrArg (fun x:Scree.Hub n=> x.val.2) (ride v s))
abbrev φΩ(B:Blend n k)(v:Sx×Sx):=B.μ v.1 v.2
lemma weight(v:Sx × Sx) : 0≤φΩ B v:= B.p ..
-- cost aggregation: pay over all pairs in range. no multiplicity depending n
lemma money (i:Sx): ∑ j∈κN n k with j.1=i,φΩ B j=1:=by
 rw [←B.card i,sum_filter,sum_filter,Fintype.sum_prod_type]; let V(i j:Sx):= B.μ i j; simp only [φΩ]; -- rewrite
 rw [Finset.sum_eq_single i]; swap
 · intro j _ p; exact sum_eq_zero fun x _=> by split <;> simp only [p,if_false]
 swap; · exact fun p=> (p (mem_univ _)).elim
 apply sum_congr rfl; intro j _; split; next p=> rw [if_pos rfl]
 next p=> exact Eq.symm (not_not.mp (fun e=>p (B.near _ _ e)))
variable (w: Wings k P a n)(t:1≤h)(z:ℝ)
abbrev fA(v:Sx×Sx): InkD n:= (z*(φΩ B v)) • (fund v.2-fund v.1)
abbrev Sα:= sunY (κN n k) χΩ (fA B z)
abbrev Zα:= ∑ v∈κN n k,(z*φΩ B v) • (stroke (τ₀ v.2) (τ₀ v.1) (coinP v) (oV (fund v.2)) (oV (fund v.1)))
lemma sport0(v:Sx×Sx): fA B z v 1=0:=by change (z*φΩ B v) • ((fund v.2 1)-(fund v.1 1))= (0:Cipher n); rw [freeH,freeH,sub_self,smul_zero]
lemma at_cash (v:Scree.Hub n): Sα B z v 1=0:=by unfold Sα sunY; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun i _=> sport0 ..
-- transport.H proof test
lemma morphS (s:Sweep n)(u:B.even s) (p:UNI SpinIdx)(x: Pane n) (i:Sx×Sx): fA B z (τσ s i) (flashA s x)=paintR s.charge (detX s.s) (prepU (castX s) p (xtra s.charge) n) (fA B z i x):=by
 have he(y:Sx):fund ((boxA s).symm y) (flashA s x)= paintR s.charge (detX s.s) (prepU (castX s) p (xtra s.charge) n) (fund y x):=by
    unfold fund; rw [stampW]; unfold moldV; change feeW _ _ • (1:Cipher n)= paintR _ _ _ ((feeW y x) • (1:Cipher n)); rw [map_smul,map_one]
 unfold fA; rw [show φΩ B (τσ s i)=_ from u i.1 i.2]; simp only [τσ,Equiv.prodCongr_apply,Pi.smul_apply,Pi.sub_apply, Prod.map_fst,Prod.map_snd, he,φΩ,map_smul,map_sub] -- tune
lemma suitS : Ru B.even (Sα B z):=by
 intro s v U g X V; simp only [Sα,sunY,Finset.sum_apply,map_sum]; symm; refine sum_equiv (τσ s) ?_ (fun i _=> (morphS _ _ _ v U V _).symm); intro i; rw [mem_filter,mem_filter (s:=κN n k) (p:=fun x=> χΩ x = moveHub s X),ride]; exact and_congr (similar i s) (Haro.pure_s s).eq_iff.symm
end Blend
end WagesC
end YM.CF.Py.Kay
