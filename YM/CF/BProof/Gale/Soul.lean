import YM.CF.BProof.Harbor.Flue
import YM.CF.BProof.Harbor.Vow
import YM.CF.BProof.Mote.Ling
import YM.CF.BProof.Fine.Gist
set_option autoImplicit false
set_option maxHeartbeats 900000
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
variable {N P:Side}{F G:Orbit N → Pane N}{a h:ℝ} {R:Patch} {r l k:ℕ}
variable (i:Axis)(X: ClockD R r l k)
abbrev g0 (N:Side)(X:ClockD R r l k)(b:Bool):= shade N i b X.gF
abbrev g1 (N:Side)(X:ClockD R r l k)(b:Bool):= shade N i b X.pF
abbrev g2 (N:Side)(X:ClockD R r l k)(b:Bool):= shade N i b X.uF
local notation "X_" t:max=> shade N i t X.gF -- names pos use
local notation "Xs" b:max=> shade N i b X.pF
local notation "Γs" b:max=> shade N i b X.uF
attribute [local instance] Wager.measureVal Wager.billVal
abbrev Body (n:Side) := PairD n→ FC (Single n)
def flipK (x: PairD N) :PairD N:= (Fixed.reflConfig N i x.1,Fixed.reflConfig N i x.2)
lemma flip_m : Measurable (flipK (N:=N) i):= (((Fixed.reflConfig_cont ..).measurable.comp measurable_fst).prodMk ((Fixed.reflConfig_cont ..).measurable.comp measurable_snd))
lemma flip_r(x:PairD N) : flipK i (flipK i x)=x:=Prod.ext (Fixed.square_reflConfig ..) (Fixed.square_reflConfig ..)
def mant (T:Body N):Body N:=fun x=> Fock.theta (Fixed.reflectP N i) (T (flipK i x))
def sqR (T:Body N):Body N:= mant i T*T
structure Soul (i:Axis)(X:ClockD R r l k)(T:Body N):Prop where
 env: Envelope T
 bit: blook (shade N i true X.gF) (shade N i true X.pF) T
 free:∀ x,Snow (shade N i true X.uF) false (T x)
lemma snown {T:FC (Single N)}{U V:Support (More N)}{b:Bool}(p:U⊆ V)(h:Snow U b T): Snow V b T:= Fixed.fine_growRegion h (by intro j q; exact (mem_modes ..).mpr (p ((mem_modes ..).1 q)))
lemma zone {T:Support (More N)}{V U:Pane N}(h:Agrees (↑(regionD (Fixed.reflectSweep N i) T)) U V) : Agrees T (Fixed.reflConfig N i U) (Fixed.reflConfig N i V):=by
 rw [←Fixed.flash_reflect,←Fixed.flash_reflect]; apply flashD; have he : boxA (Fixed.reflectSweep N i)=(boxA (Fixed.reflectSweep N i)).symm:=(by rw [←sitU,Fixed.inv_reflectSweep]); rw [he]; exact h
lemma zone_x (b:Bool)(k:ℕ){V U:Pane N}(h:Agrees (↑(shade N i (!b) k)) U V) :Agrees (shade N i b k) (Fixed.reflConfig N i U) (Fixed.reflConfig N i V):= zone i (by rw [shade_carry]; exact h)
lemma taxS{I:Type}[Fintype I][LinearOrder I][MeasurableSpace I] (S:Submodule ℂ (FC I))(a:ℝ)(p:FC I)(h:p∈S):a • p∈S:=(S.restrictScalars ℝ).smul_mem a h
namespace Soul
variable {i X}{T:Body N}(p:Soul i X T)
lemma entry (F:Obs N)(h:Allowed (shade N i true X.uF) F)(z:∀ U, Snow (shade N i true X.uF) false (F U)): Soul i X (F ∘ Prod.fst):=by refine ⟨Law.pull h.bounded measurable_fst, fun U V v w=>?_,fun _=> z _⟩; have hx:= X.duty; have hz:= X.born; exact h.reads U.1 V.1 (agrees_mono v (mono i (by omega) true)) -- tune
include p
local notation "Yt"=> (Fixed.reflConfig N i)
lemma mantL : Envelope (mant i T):= Girt.pole_w (X:=FC (Single N)) (T∘flipK i) _ (Fock.theta_cont _) (Law.pull p.env (flip_m i))
lemma mantR : blook (shade N i false X.gF) (shade N i false X.pF) (mant i T):=fun U V h g=> congrArg (theta (Fixed.reflectP N i)) (p.bit _ _ (zone_x i true X.gF h) (zone_x i true X.pF g))
lemma sq_price : Envelope (sqR i T):= Wager.engine p.mantL p.env
/-- moving positive-only scalar compensation into Soul -/
lemma hookup {f:Pane N→ℝ}(h:Envelope f)(g:LocalOn (↑(shade N i true X.gF)) f): Soul i X (fun x=>f x.1 • T x):=by
 refine ⟨Wager.fee p.env (Law.pull (q:=Prod.fst) h measurable_fst),fun U V h w=> congrArg₂ ((·•·):ℝ→FC (Single N)→FC (Single N)) (g U.1 V.1 h) (p.bit U V h w), fun x=>?_⟩; exact ((winter (shade _ i _ _) false).restrictScalars ℝ).smul_mem (f _) (p.free x)
end Soul
end Gale
end YM.CF.BProof.Bide
