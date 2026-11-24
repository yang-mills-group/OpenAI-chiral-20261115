import YM.CF.BProof.Shore.Warm
/-! Constructors are Borel on fixed fields (discrete tables independent of period/free
operators). First measurability before randomness. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Function Metric MeasureTheory Filter Finset Lattice Wilson Nest Stave Gallery
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{s l q:ℕ}{u ε d a b δ θ:ℝ}
local notation "Sκ"=>Site n
local notation "Z"=> Nerve.Halo
namespace Score
open Wool
variable (u s l)(T:Tray (Floor q) ε)(F:Drum (rollup q T) (Floor q)) (A:Score n q)
local notation "Sπ"=> Config SU.group n
-- signatures
lemma key_meas(x:Sκ):Measurable (fun U:Config SU.group n=> Key T A U x):= (T.stamps (A.fine.hue x) (A.fire x)).comp ((vacuum_c A.orderC A.cur x).measurable) -- tune type opens measurable plate
lemma caught_meas(x:Sκ): MeasurableSet {U:Sπ| caught s l u A U x}:=by unfold caught sound; simp only [Set.setOf_forall]; exact MeasurableSet.iInter (fun i=> MeasurableSet.iInter fun _=> clear_borel u _ i)
lemma open_meas(x:Sκ):Measurable (fun U:Config SU.group n=> opened s l u T F A U x):=by
 refine Measurable.ite (f:=fun U=> lower _) (caught_meas s l u A x) (show Measurable (fun U:Sπ=> lower (native A.cur A.orderC U x)) from (show Continuous (fun U:Sπ=>lower (native A.cur A.orderC U x)) from ((Isometry.of_dist_eq lower_dist).continuous.comp (vacuum_c A.orderC A.cur x))).measurable) ?_ -- tune
 let q(U:Sπ):= Key T A U; let p(U:Sπ)(i:Sκ):Bool:= if sound s l u U i then true else false
 let B (z:(Site n→ Bool)×(Site n→ rollup _ T)):= dummy F (bale ((z.1) · = true) z.2 (A.fine.wheel x))
 have ht : Measurable (fun U:Sπ=>(p U,q U)):= by
    apply Measurable.prodMk (measurable_pi_lambda _ _) (measurable_pi_lambda _ _); all_goals intro i
    · exact Measurable.ite (clear_borel u _ i) (measurable_const (a:=true)) (measurable_const (a:=false))
    exact key_meas T A i
 suffices (fun U:Sπ=>dummy F (tagger s l u T A U x))=B ∘ (fun U:Sπ=>(p U,q U)) by exact this.symm ▸ (measurable_of_countable B).comp ht
 ext1 U; dsimp only [B,Function.comp_apply]; unfold tagger; congr! with i; simp [p]
end Score
end YM.CF.BProof.Mesh.Shore
