import YM.CF.BProof.Gale.Kiosk
set_option autoImplicit false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 26000
open Skye Law
open Arbor
open Wager Frost Half Leg Rush Tulip Peaks TripD Scree Tap Haro ArborW RillW
namespace Gale
variable {N P:Side}{F G:Orbit N → Pane N}{a:ℝ} {R:Patch} {r l k:ℕ}
variable (i:Axis)(X: ClockD R r l k)
local notation "X_" t:max=> shade N i t X.gF -- names pos use
local notation "Xs" b:max=> shade N i b X.pF
local notation "Γs" b:max=> shade N i b X.uF
attribute [local instance] Wager.measureVal Wager.billVal
open Push.SectorMeasure -- Chi
variable (B:Ratio N P) (q:Chi) (z:ℝ) {T:StepData (More N) (More P)}
variable {W V:Part N P} {b:Bool}
variable (RT:T.patch=R) (h:T.ratio=ratio B) (hp:B.count=R.L) (t:0<z)(v:2*z < Next.SectorChange.firstRadius group)
variable {τ n:ℕ}{c e:ℝ}(L:Roof N c e l F) (Q: Vogue.Quartz N τ a l F)
-- preserve support under heal
namespace ClockD -- namespace wrong? do manage explicitly
end ClockD
abbrev hake (F:Orbit N→ Pane N)(U:Part N P) (A:Pane N)(V:Pane P):= heal F (fun x=>U x V) A
include L
lemma loaf (p:Envelope (Function.uncurry W)): Envelope (Function.uncurry (hake F W)):= Frost.fullM _ L.bill (fun x : Pane N×Pane P=> fun y:PairD N=> W y x.2) (fun x=>x.1) (Law.pull (f:=Function.uncurry W) (q:=fun x: (Pane N × Pane P) × PairD N=> (x.2,x.1.2)) p (by fun_prop)) measurable_fst -- include L
omit L
section heal
local notation "C0"=>shade N i b
local notation "Y0"=>shade P i b
include Q
lemma hale (p:Envelope (Function.uncurry W))(u:peep b X i W) (V:Pane P) : LocalOn (C0 X.gF) (fun y=> hake F W y V):= Frost.stop_h Q (C0 X.gF) (C0 X.pF) (hedge i X.duty b) (Law.pull (f:=Function.uncurry W) (q:=fun y=>(y,V)) p measurable_prodMk_right) (u.1 V)
lemma earnTag(p:Envelope (Function.uncurry W))(v:Envelope (Function.uncurry V))(u:peep false X i W)(y:peep true X i V) (x:Pane N)(A:Pane P): hake F (fun x U=> W x U* V x U) x A= hake F W x A* hake F V x A:= by
 let X0:= shade N i false X.pF; let X1:= shade N i true X.pF
 have he:=X.pos; refine Frost.matrix_FD Q X0 X1 (shade N i false X.gF) (shade N i true X.gF) (Half.splits i false he) (hedge i X.duty false) (hedge i X.duty true) (fun L p' r w=>?_) (Frost.lookP _ _ (u.1 A) x) (Frost.lookP _ _ (y.1 A) x) ?_ ?_ _
 · exact Half.gap i false p' w (by have :=X.duty; omega : l < X.pF)
 · exact Law.pull (f:=Function.uncurry W) (q:=fun y: Pane N=>((x,y),A)) p (by fun_prop)
 exact Law.pull (f:=Function.uncurry V) (q:=fun y: Pane N=>((x,y),A)) v (by fun_prop)
omit Q
lemma little (p:peep b X i W) (V:Pane N): LocalOn (Y0 X.pF) (hake F W V):=fun U W h=> integral_congr_ae (Eventually.of_forall fun t=> p.2 _ U W h)
include L
lemma influx (W:Part N P)(p:Envelope (Function.uncurry W))(x: Pane N)(V: Pane P): hake F (Travel i W) x V= theta (Fixed.reflectP P i) (hake F W (Fixed.reflConfig N i x) (Fixed.reflConfig P i V)):=by
 let t:Pane N→FC (Single P):=fun y=> W (Fixed.reflConfig N i x,y) (Fixed.reflConfig P i V); have ht : Envelope t:= Law.pull (f:=Function.uncurry W) (q:=fun y:Pane N=> ((Fixed.reflConfig N i x,y), Fixed.reflConfig P i V)) p (by fun_prop); let U(y:Ids N):=Fixed.reflConfig N i (F (x,y))
 change meanS (depot N) (fun y=> theta _ (t (U y)))=_; have hx:Envelope (fun y=>t (U y)):= Law.pull (q:=U) ht ((Fixed.reflConfig_cont ..).measurable.comp (L.bill.comp measurable_prodMk_left)); rw [t_avg (depot N) _ hx]; exact congrArg _ (hMirror F L i t x ht.meas)
end heal
variable (p:T.patch.Branches T.kernel SU.group) (β:ℝ)
abbrev fuel (T:StepData (More N) (More P))(β:ℝ)(F:Orbit N→ Pane N)(W:Part N P): Body P:=fun x=> flow_b T β (fun y=> hake F W y x.2) x.1
local notation "ψ" => hake F
local notation "Fθ"=> fuel T β F
include p L
lemma carries (W:Part N P)(u:Envelope (Function.uncurry W)): Envelope (Fθ W):= RillW.true_b T p β (fun w:PairD P=>w.1) (fun (w:PairD P) y=>hake F W y w.2) (Law.pull (f:=Function.uncurry (hake F W)) (q:=fun x:PairD P× Pane N=> (x.2,x.1.2)) (loaf L u) (by fun_prop)) measurable_fst
lemma upheld (U:Pane P)(W:Part N P)(e:Envelope (Function.uncurry W)): Envelope (fun y=>hake F W y U):= Law.pull (f:=Function.uncurry (hake F W)) (q:=fun y=> (y,U)) (loaf L e) measurable_prodMk_right -- omit p? include
include RT h hp Q
lemma local_a (u:peep b X i W)(t:Envelope (Function.uncurry W)): blook (shade P i b X.gF) (shade P i b X.pF) (Fθ W) :=by
 let K:= shade N i b X.gF; let Z:=ψ W; let D:= shade P i b X.gF; intro V U u' v; have he: LocalOn D (fun x=> flow_b T β (fun y=> Z y V.2) x):= RillW.localB T p β K (upheld L p V.2 W t) (hale i X Q t u _) D (fun y g=> by rw [RT,h]; exact X.trueW i B hp b y g)
 have hx:(fun y=> Z y V.2)=(fun y=> Z y U.2):= funext fun y=>little i X u y V.2 U.2 v; refine Eq.trans (he V.1 U.1 u') (congrArg (fun Z=>flow_b T β Z U.1) hx)
omit RT h hp
lemma term (W V:Part N P)(u:peep false X i W)(t:Envelope (Function.uncurry W))(g:peep true X i V)(e:Envelope (Function.uncurry V)): Fθ (W*V) = Fθ W * Fθ V:=by
 ext1 x; let w(A:Pane N):= hake F W A x.2; let v(A:Pane N):= hake F V A x.2; change flow_b T β _ _=flow_b T β w _* flow_b T β v _; rw [show (fun y=>hake F (W*V) y x.2)=(fun y=>w y * v y) from funext (fun y=> earnTag i X Q t e u g y x.2)]; exact RillW.twice T p β x.1 _ _ (upheld L p x.2 W t) (upheld L p x.2 V e) (Finset.disjoint_coe.mpr (splits (N:=N) i false X.pos)) (hale i X Q t u x.2) (hale i X Q e g x.2)
omit Q
lemma mantle (W:Part N P)(u:Envelope (Function.uncurry W)): Fθ (Travel i W)=mant i (Fθ W):=by
 ext1 x; unfold fuel hake mant; change flow_b T β _ _=theta _ (flow_b _ _ (fun y=>hake F W y (Fixed.reflConfig _ i x.2)) (Fixed.reflConfig _ i x.1)); let C (y:Pane N):=ψ W y (Fixed.reflConfig _ i x.2)
 rw [← RillW.lay_cue β p C (upheld L p _ W u) i]; let μ:=prior SU.group (More N); let K:Pane N→ℝ:=T.density β x.1; let Q(y):=C (Fixed.reflConfig N i y); have hp: Envelope Q:=Law.pull (f:=C) (upheld L p _ W u) ((Fixed.reflConfig_cont ..).measurable)
 refine Eq.trans ?_ (Wager.take μ (thetaCL _) hp (density_E T p β x.1)); unfold flow_b avg; apply integral_congr_ae; refine Eventually.of_forall fun i'=>?_ ; exact congrArg (K i' • ·) (influx i L W u i' x.2)
end Gale
end YM.CF.BProof.Bide
