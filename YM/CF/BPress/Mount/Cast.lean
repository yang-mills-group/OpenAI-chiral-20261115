import YM.CF.BPress.Mount.Bore
/-! package `MeasuredFees`. Only prices are high offsets. Mark dust amplitude bounds stitched.NPL. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mount
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree Voice Noon Phase Extensor
variable {s m B N:Side}
-- weak hand typed independently of domain; exact evaluations use actual spectra. No measure choices packaged here.
structure Edition (U:Driver N) where
 op : Tenor (More N)→ U.Pose →ℂ
 opfee : Tenor (More N)→ℝ
 reg : Support (More N)→ U.Pose × Pane N →ℂ
 logG : Support (More N)→ U.Pose → Shot N →ℂ
 fee : Support (More N)→ℝ
variable {U:Driver (mid m B)}{F:GramM (mid m B)}{G:Brace.Duet m B}{X Y Z H W H0 Z' X':Pledge}
local notation "β"=> payA X Y Z
local notation "E_"=> Edition U
local notation "η"=> (mid m B)
local notation "ρ"=> (More η)
-- cultureStencil. Weak vis pure on true&both; clock costs $zeta$.
structure Passports (U: Driver (mid m B))(F: GramM (mid m B))(G:Brace.Duet m B)(u:Wish U X Y Z)(P: Edition U)(A:Pledge)(q c ε μ v:ℝ):Prop where
 cruise: Cash scaffold P.opfee A.rate A.price
 measure : ∀ p,Measurable (P.op p)
 known :∀ p x, ‖P.op p x‖≤ P.opfee p
 point :∀ p,P.opfee p≠0→ Grove (Grid.field 4 (More _)) p.2 ∧ p.1∈ p.2
 view (p) (x y:U.Pose) : Along  (scaffold p) x.val y.val→ P.op p x=P.op p y
 theme (p) x g: P.op p (moveW x u g)=P.op p x
 surge (T) (x y:U.Pose) {b a:ℝ}: y.val.G=1→ Slow 1 (hook y.val.X) q→ Shell (scaffold T) y.val.X x.val.G x.val.X b→0<b→b≤c→U.Beta.eval (scaffold T) x y≤a→b≤a→ ‖P.op T x-P.op T y‖ ≤ P.opfee T*a
 issuer(x):∑ i, P.op i x= stark x- Pec.pigment F.J.I x.val.G- Spire.zen (Spire.hum m B G x.val.G x.val.X)
 real0 (x) (p): (Fare.town F.J.I x p).re=∑ t,(P.op (p,t) x).re
 grow : Cash id P.fee μ v
 fee_land : ∀ p,P.fee p≠0→ Grove (Grid.field 4 (More _)) p
 seem :∀ p, Measurable (P.reg p)
 reads: ∀ (p: Support (More (mid m B)))(x y:U.Pose)(K V:Pane (mid m B)), Along p x.val y.val → Agrees p K V → P.reg p (x,K)=P.reg p (y,V)
 mast : ∀ T x p g,P.reg T (moveW x u g,gauge g p)=P.reg T (x,p)
 feel(t) (x): ‖P.reg t x‖≤ P.fee t
 turn (p s x): inBudget s ε→ ‖P.logG p x s‖≤ P.fee p
 frost (p:Support (More (mid m B)))(s t:Shot (mid m B))(x y:U.Pose): Along p x.val y.val→Camera s U.decks x y p t F.p.B (P:=U.Beta)→ P.logG p x s=P.logG p y t
 bare (p s x) : barren F s p→ P.logG p x s=P.reg p (x,s.field.1)
 cloud (p) : ∀ {α:Type}[MeasurableSpace α](T:α→ Shot (mid m B))(X:α→ U.Pose), Shot.Given T → Measurable X → Measurable fun i=> P.logG p (X i) (T i)
 wick_p (x:U.Pose)(S:Shot (mid m B))(p:inBudget S ε)(ω) (h: Pf.Top (mood (U.decks.A x) (U.decks.M x)) ω) : wickO F S.field 1 S.f (U.decks.KG x) S.stampX (U.decks.A x) S.j S.inserts ω (U.decks.seat x)= Complex.exp (∑ i, P.logG i x S)
namespace Passports
variable (u: Wish U X Y Z)(T:Stellar U H W F.J.I)(p:Till U.Beta F)
abbrev castP (ε:ℝ): E_ := ⟨T.publicF u,T.myCost,fun b x=> Dust.pureG u p b x.1 x.2,Dust.wholeG u p,Dust.feeG p ε⟩ -- tune need ε argument
-- expose before x thresholds.PL. lease.
theorem settled {h q v ε σ δ k:ℝ} (a:Store U.Beta U.decks X' F h U.ε U.v ε q σ p)(K:Shale.Grant H0 X (payA X Y Z) (stream 1) (Sight.price U.h) U.v U.ε quota)(Y:Voice.Solo T.voice G k W.rate W.price)(P: Shell.plot v U.p U.d δ k): Passports U F G u (castP u T p ε) (H.plus W) v δ ε σ (Dust.dustC X' ε q F.p.B):=by
 refine ⟨T.cost_0 Y,fun p=>T.knownL u p Y,fun i x=>T.budget0 u i x Y,T.rows_t Y,fun p x y g=> T.stable_c u p x y Y g,fun i x v=>T.gauge_m u i x Y v,fun p x y {_ _} c d h=> T.cost0 u p x y Y P d c h, fun x=>T.burst u x Y H0 K, fun x p=>(T.billzR u x Y p).symm, Dust.earnedG a,fun t h=>?_,fun i=> Dust.pure_m u i a,fun p x _ K _ v q=> Dust.pure_read u p x K a v q, fun i x p y=> Dust.pure_g u i x p a y, fun i ⟨x,k⟩=>?_,fun i z x h=> Dust.whole_p u i x z a h,fun i j k x y h=> Dust.whole_read u i x j a h k,fun i t p h=>Dust.whole_k u i p t a h,fun i _ _ p x g v=>Dust.whole_m u i a p g x v,fun x s t ω h=>?_⟩ -- tune constructor
 · exact currencyOn a t (fun g=>h (show 3*p.currencyGas ε t=0 from by rw [g,mul_zero]))
 · exact (Dust.pure_on u i x k a).trans (le_mul_of_one_le_left (currencyPays a|>.pos _) (by norm_num : (1:ℝ)≤3))
 change _=Complex.exp (∑ i,Dust.wholeG u p i x s); rw [Dust.full_cost u x s a]; exact lift_log a 1 (by simp) x t ω h
end Passports
end YM.CF.BPress.Mount
