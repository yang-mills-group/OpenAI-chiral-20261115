import YM.CF.BPress.Mount.Cast
/-! § eq:B-Ms casts Mark tests skeleton. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mount
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree Voice Noon Phase Extensor
variable {s m B N:Side}
structure Calyx {U:Driver N}(P:Edition U){α: Type*}(v:α→ U.Pose) where
 body:Tenor (More N)→ Plain N→ℂ
 hull:Support (More N)→Plain N→ℂ
 pay (t): Extensor.Extends (P.opfee t) (scaffold t) (body t)
 phaseRec(t): Extensor.Extends (P.fee t) t (hull t)
 eye(x:α)(t): body t (v x).val = P.op t (v x)
 C_eye(x:α)(t):hull t (v x).val=P.reg t (v x,(v x).val.G)
-- choose relative Extends each band.Gauge extension.
variable {U:Driver (mid m B)}{F:GramM (mid m B)}{G:Brace.Duet m B}{Y Z T A:Pledge}{V:Wish U Y Z T}{P:Edition U}{a q g u v:ℝ}
variable (H:Passports U F G V P A a q g u v)
include H
lemma mounting {α: Type*}[MeasurableSpace α][StandardBorelSpace α](R:α→ U.Pose)(t:Measurable R): Nonempty (Calyx P R):=by
 choose W h b using fun i=>thick V (scaffold i) (P.op i) (H.measure i) (H.known i) R t (H.cruise.pos i) (fun x y=>H.view i x y) (fun p x=>H.theme i x p)
 let G(t:Support (More (mid m B)))(x:U.Pose):= P.reg t (x,x.val.G); have ht (i): Measurable (G i):= by refine (H.seem i).comp (measurable_id.prodMk ?_); exact measurable_fst.comp measurable_subtype_coe
 choose U' ht v using fun i=> thick V i (G i) (ht i) (fun x=>H.feel i _) R t (H.grow.pos i) (fun x y u=> H.reads i x y x.val.G y.val.G u u.up) (fun p x=>H.mast i x x.val.G p); refine ⟨W,U',h,ht,?_ ,?_⟩
 · intro x i; simpa only [pose_one,τ_one] using (show W i (moveW (R x) V 1).val=_ from b i x 1)
 intro x i; change _= G i (R x); simpa only [pose_one,τ_one] using (show U' i (moveW (R x) V 1).val=G i (moveW (R x) V 1) from v i x 1)
end YM.CF.BPress.Mount
