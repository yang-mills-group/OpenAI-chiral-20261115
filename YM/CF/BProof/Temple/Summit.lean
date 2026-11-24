import YM.CF.BProof.Temple.Cup
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
variable {W V:Part N P}
variable (RT:T.patch=R) (h:T.ratio=ratio B) (hp:B.count=R.L) (t:0<z)(v:2*z < Next.SectorChange.firstRadius group)
variable {τ n:ℕ}{c e:ℝ}(L:Roof N c e l F) (Q: Vogue.Quartz N τ a l F)
-- preserve support under heal
variable (p:T.patch.Branches T.kernel SU.group) (β:ℝ)
open Window.Unfit
namespace Soul
local notation "θ"=> Fixed.reflectTest i false
variable {Y:Body N}(b:Soul i X Y)
local notation "ΩY"=> heal F Y
local notation "κx"=> heal F
include L Q b
lemma avgSoulR(B:Support (More N))(u:X_ true ⊆ B) : Allowed B (heal F Y) := by
 have p: LocalOn (X_ true) ΩY:= Frost.stop_h Q _ _ (hedge i X.duty true) b.env b.bit; refine ⟨heal_v F L.bill b.env, fun V W v=> p _ _ (agrees_mono v u), ?_⟩; intro x; let T:= Γs true; have hv:T⊆ B:= (Half.mono i (by have ht:=X.duty; have he:=X.born; omega) true).trans u; let f(y:Ids N):= Y (x,F (x,y)); let t:Leg.Snow T false (ΩY x) := Wager.fund_s _ ((winter T false).restrictScalars ℝ) (show Envelope f from Law.pull (q:=fun i:Ids N=> (x,F (x,i))) b.env (measurable_const.prodMk (L.bill.comp measurable_prodMk_left))) fun i=>b.free _
 exact (snown hv t).sector
omit Q
lemma θ_avg(V:Pane N) : heal F (mant i Y) V=θ ΩY V:= by
 let t(j:Pane N):=Y (Fixed.reflConfig N i V,j); -- tune i shadow
 let f(U:Ids N):=(t (Fixed.reflConfig _ i (F (V,U)))); have he: Envelope t:= Law.pull (q:=Prod.mk _) b.env measurable_prodMk_left; have hh:Envelope f:= Law.pull (q:=fun U=>Fixed.reflConfig _ i (F (V,U))) he ((Fixed.reflConfig_cont ..).measurable.comp (L.bill.comp measurable_prodMk_left))
 rw [Leg.mirQ]; change meanS _ (fun z=>Fock.theta (Fixed.reflectP N i) (f z))=_
 rw [t_avg (depot N) (Fixed.reflectP N i) hh]; exact congrArg (Fock.theta (Fixed.reflectP N i)) (hMirror F L i t V he.meas)
include Q
lemma κ_avg(V:Pane N) : heal F (sqR i Y) V=(θ ΩY * ΩY) V:=by
 rw [Pi.mul_apply, ←θ_avg i X L]; swap; · exact b -- tune
 let A:= Xs false; let B:= Xs true; have he:=X.pos; apply Frost.matrix_FD Q A B (X_ false) (X_ true) (Half.splits i false he) (hedge i X.duty false) (hedge i X.duty true) (fun L p r u=> Half.gap i false p u (by have :=X.duty; omega : l < X.pF)) (Frost.lookP _ _ b.mantR V) (Frost.lookP _ _ b.bit V) (Law.pull (f:=mant i Y) (q:=Prod.mk V) b.mantL measurable_prodMk_left) (Law.pull (f:=Y) (q:=Prod.mk V) b.env measurable_prodMk_left) V
variable {f: Orbit N→ Phys N}
omit Q b
lemma coast (A:Body N)(u:Envelope f)(y:Envelope A){p:Pane N→Prop}(c:∀ᵐ x∂prior SU.group (More N),p x) (h:∀ x:Pane N,p x→∀ (B:FC (Single N))(U V: Ids N),pass B (f (x,U))=pass B (f (x,V))): cup f F A= Fixed.functional f (heal F A):=by
 let T (x:Orbit N):=pass (A (poke F x)) (f x); let S(x: Orbit N):=pass (heal F A x.1) (f x); have hv:Envelope T:= priceA u (Law.pull (q:=poke F) y (measurable_fst.prodMk L.bill)); have he: Envelope S:= priceA u (Law.pull (q:=Prod.fst) (heal_v F L.bill y) measurable_fst); let μ:=prior SU.group (More N); change (∫ i,T i∂ μ.prod (depot N))=(∫ i,S i∂ μ.prod (depot N)); rw [integral_prod T (Law.pay hv),integral_prod S (Law.pay he)]; apply integral_congr_ae; filter_upwards [c] with x hX
 let v:=Classical.arbitrary (Ids N); let C:=capL (f (x,v)); let H(i:Ids N):= A (x,F (x,i)); have hH:Envelope H:=Law.pull (q:=fun i:Ids N=>(x,F (x,i))) y (measurable_const.prodMk (L.bill.comp measurable_prodMk_left)); have hx(i:Ids N): S (x,i)= C (meanS (depot N) H):=h x hX _ i v; have hp(i:Ids N): T (x,i)= C (H i):=h x hX _ i v
 simp_rw [hp,hx]; rw [integral_const]; simp only [probReal_univ,one_smul]; exact C.integral_comp_comm (Law.pay hH)
include Q b
lemma harvest (u:Envelope f){p:Pane N→Prop}(c:∀ᵐ x∂prior SU.group (More N),p x)(h:∀ x:Pane N,p x→∀ (B:FC (Single N))(U V: Ids N),pass B (f (x,U))=pass B (f (x,V))) : cup f F (sqR i Y)= Fixed.functional f (θ ΩY * ΩY):=by rw [coast L (sqR i Y) u b.sq_price c h, funext (κ_avg i X L Q b)]
end Soul
end Gale
end YM.CF.BProof.Bide
