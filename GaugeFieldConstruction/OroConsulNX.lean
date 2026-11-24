import GaugeFieldConstruction.LoyalShelfNX
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2800
set_option linter.unusedSectionVars false
set_option maxHeartbeats 140000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze Sifter VoucherOp Theatre
variable {P:Spine}{R:P.Register}{x:P.Spectrum0 3}{D N:Doorway}{M:P.Menagerie}
variable {F G:SampleDose}{s n:ℕ}{o:Orders}(w:P.Dawn R x s n D N o F G M)(Z W:Lead.Clan)
private lemma forwardBillNX {ε:ℝ}(v:Scoop)(f:ℕ→ℂ)(z:ℂ)(h:∀j∈v.take, ‖f j-z‖≤ε) : ‖v.recipe f-z‖≤ε:=by
 have he:∑ j∈v.take, (v.weight j:ℂ) • z=z:=by rw[←Finset.sum_smul,←Complex.ofReal_sum,v.total]; simp
 have ht:=v.cap h; convert ht using 1; unfold Scoop.recipe; simp_rw[smul_sub]; rw[Finset.sum_sub_distrib,he]
-- NOTE b sufficient unbounded/tends.No requirement old path identical in unrelated takes.
variable {b:ℕ→ℕ}(v:Tendsto b atTop atTop)(DZ:P.VoucherOp x Z n b)(DW:P.VoucherOp x W n b)(ε:ℝ)(p:0<ε)
include v w p
lemma bothFlowNX : ∀ᶠ j:ℕ×ℕ in atTop,∀ t,DZ.eligible j.1 t → DW.eligible j.2 t →
   ‖P.singleState 3 t x (DZ.markField false j.1 t F*DW.markField true j.2 t G)- star (P.electro M Z)*P.electro M W‖≤ε ∧
   ‖P.singleState 3 t x (DZ.markField false j.1 t F)-star (P.electro M Z)‖≤ε ∧ ‖P.singleState 3 t x (DW.markField true j.2 t G)-P.electro M W‖≤ε:=by
   obtain ⟨f,hf⟩:=eventually_atTop.mp (properFlowNX w Z W ε p)
   obtain ⟨g,hg⟩:=eventually_atTop.mp (properSingleNX w Z W ε p)
   let e:= max (max f.1 f.2) g
   obtain ⟨m,hm⟩:=eventually_atTop.mp (v.eventually (eventually_ge_atTop e))
   filter_upwards [eventually_ge_atTop (m,m)] with j hk t hu hv
   let A:= DZ.cost j.1; let B:= DW.cost j.2
   let q(i:ℕ):= b (j.1+i); let r(i:ℕ):= b (j.2+i)
   have hp(i):f.1≤ q i := ((le_max_left ..).trans (le_max_left ..)).trans (hm _ (by exact hk.1.trans (Nat.le_add_right ..)))
   have hh(i):f.2≤ r i:= ((le_max_right ..).trans (le_max_left ..)).trans (hm _ (by exact hk.2.trans (Nat.le_add_right ..)))
   have hP(i): g ≤ q i:= (le_max_right ..).trans (hm _ (by exact hk.1.trans (Nat.le_add_right ..)))
   have hQ(i): g ≤ r i:= (le_max_right ..).trans (hm _ (by exact hk.2.trans (Nat.le_add_right ..)))
   let p0(i):= P.thinIncoming Z (q i) n t F
   let q0(i):= P.thinOutgoing W (r i) n t G
   let X:=P.singleState 3 t x
   have here(S:Scoop)(F:ℕ→P.Test)(Z:P.Test→ₗ[ℂ]ℂ): Z (S.recipe F)= S.recipe (Z ∘ F):=by unfold Scoop.recipe; simp only[map_sum,map_smul]; rfl
   constructor
   · have hz(a:P.Test)(S:Scoop)(F:ℕ→P.Test):X (a*S.recipe F)=S.recipe (fun i=> X (a*F i)):=here S F (X.comp (LinearMap.mulLeft ℂ a))
     change ‖X (A.recipe p0 * B.recipe q0)- _‖≤ε
     rw[hz]; apply forwardBillNX B; intro k u; rw[mul_comm, hz]; refine forwardBillNX A _ _ ?_
     intro i v; rw[mul_comm]; exact hf (q i,r k) ⟨hp i,hh k⟩ t (max_le (hu _ v) (hv _ u))
   change ‖X (A.recipe p0)- _‖ ≤ ε ∧ ‖X (B.recipe q0)- _‖≤ε
   rw [here,here]; exact ⟨forwardBillNX A _ _ (fun i v=>(hg _ (hP i) t (hu _ v)).1),forwardBillNX B _ _ (fun i v => (hg _ (hQ i) t (hv _ v)).2)⟩
#print axioms bothFlowNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
