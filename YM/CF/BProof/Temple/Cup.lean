import YM.CF.BProof.Gale.Aim
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
variable (p:T.patch.Branches T.kernel SU.group) (β:ℝ)
open Window.Unfit
namespace Soul
abbrev pass (A:FC (Single N))(z:Phys N): ℂ:=beamZ _ (acts A z)
abbrev cupL (A:FC (Single N)) : Phys N →L[ℝ]ℂ:= (beamL _).comp ((acts A).restrictScalars ℝ)
abbrev capL (z:Phys N): FC (Single N)→L[ℝ]ℂ:= (beamL _).comp (
 let f: FC (Single N)→L[ℂ]Phys N:=
   { toFun:=fun A=> acts A z
     map_add':=fun a b=> act_add ..
     map_smul':=fun c A=> act_smul ..
     cont:=acts_cont.clm_apply continuous_const }; f.restrictScalars ℝ)
lemma priceA {Y:Type}[MeasurableSpace Y]{F:Y→ Phys N}{Z:Y→ FC (Single N)}(p:Envelope F)(g:Envelope Z):Envelope (fun x=> pass (Z x) (F x)):= by
 apply Girt.pole_w (X:=Phys N) (fun x=> acts (Z x) (F x)) (beamL N) (beamL _|>.continuous); exact Girt.kitE Z F (fun a b=>acts a b) (Continuous.clm_apply (acts_cont.comp continuous_fst) continuous_snd) g p

def cup {n:Side}(E:Orbit n→Phys n)(F:Orbit n→Pane n)(X:Body n):=∫ x,pass (X (poke F x)) (E x) ∂city _
-- integrate low orbit reward against S.density cond
section gen
private lemma birth_l {A Bf E:Type}[MeasurableSpace A][MeasurableSpace Bf][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure A)(ν:Measure Bf)[IsFiniteMeasure μ][IsFiniteMeasure ν](L:E →L[ℝ]ℂ)(f:A × Bf→ E)(r:A→ℝ)(hf:Envelope f)(hr:Envelope r):
 (∫ x,L (r x.1 • f x)∂ μ.prod ν)= L (avg μ r fun a=>meanS ν fun x=> f (a,x)):=by
 have he:Envelope (r ∘ Prod.fst (β:=Bf)):=Law.pull hr measurable_fst; let g(x:A × Bf):=r x.1 • f x; have hp:Integrable g (μ.prod ν):=Law.pay (Wager.fee hf he); rw [L.integral_comp_comm hp]; apply congrArg; rw [integral_prod g hp]; apply integral_congr_ae; apply Eventually.of_forall; intro x; exact integral_smul (μ:=ν) (r x) (fun i=> f (x,i))
include L p
abbrev live {N:Side}(F:Orbit N→ Pane N)(f:PairD N→ FC (Single P))(r:Pane N→ℝ) (U:Orbit N):=r U.1 • f (poke F U)
lemma portal (U:Part N P)(e:Envelope (Function.uncurry U))(z:PairD P)(x:Phys P) :
 (∫ i:Orbit N,T.density β z.1 i.1 • pass (U (poke F i) z.2) x∂city N)=pass (fuel T β F U z) x:=by
 let r0:=T.density β z.1 -- tune implicit θ
 let g(t: PairD N):=U t z.2; have ht:Envelope g:= Law.pull (f:=Function.uncurry U) (q:=fun t=> (t,z.2)) e measurable_prodMk_right; have hu: Envelope r0:=RillW.density_E T p β z.1; let f:=g∘Frost.poke F; have hf:Envelope f:= Law.pull (q:=Frost.poke F) ht (measurable_fst.prodMk L.bill)
 let β'(i: Orbit N):=r0 i.1; have Hb:Envelope β':=Law.pull (q:=Prod.fst) hu measurable_fst
 let L:= capL x; calc
    _ = ∫ i, L (r0 i.1 • f i)∂city N:= integral_congr_ae (Eventually.of_forall fun i=> (map_smul L _ _).symm)
    _ = _:= birth_l (prior group (More N)) (depot N) L f r0 hf hu
end gen
end Soul
end Gale
end YM.CF.BProof.Bide
