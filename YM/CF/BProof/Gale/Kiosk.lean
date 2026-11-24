import YM.CF.BProof.Gale.Soul
set_option autoImplicit false
set_option maxHeartbeats 140000
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
abbrev Part (N P: Side) := PairD N→ Pane P→FC (Single P)
abbrev Travel (i:Axis)(R:Part N P):Part N P:=fun y x=> Fock.theta (Fixed.reflectP P i) (R (flipK i y) (Fixed.reflConfig P i x))
structure Pear (X: ClockD R r l k)(i:Axis)(B:Ratio N P) (b:Bool)(F:Part N P):Prop where
 envy: Envelope (Function.uncurry F)
 ore:∀ U, blook (shade N i b X.gF) (shade N i b X.pF) (fun x=> F x U)
 stern:∀ x,LocalOn (Leg.reach B (shade N i b X.uF) k) (F x)
variable {W:Part N P} {b:Bool}
lemma turnP (p:Pear X i B b W): Pear X i B (!b) (Travel i W):=by
 let f(x:PairD N×Pane P):= (flipK i x.1, Fixed.reflConfig P i x.2); let F:= Law.pull (q:=f) p.envy ((flip_m i |>.comp measurable_fst).prodMk ((Fixed.reflConfig_cont ..).measurable.comp measurable_snd))
 refine ⟨Girt.pole_w ((Function.uncurry W) ∘ f) _ (Fock.theta_cont _) F, fun U x y v g=>congrArg (theta _) (p.ore _ (flipK i x) _ (zone_x i b _ v) (zone_x i b _ g)),fun a U V t=>?_⟩; exact congrArg (theta _) (p.stern _ _ _ (zone i (by rw [mirrorLeg, shade_carry]; exact t)))
abbrev generalizeP(B:Ratio N P) (q:Chi)(z:ℝ)(x:Part N P)(F:Forest (ratio B))(V:PairD N)(U:Pane P):=x V (seine B F q z U V.2)
-- bend about actual common plane both expressed at Origin
variable (h:T.ratio=ratio B) (hp:B.count=R.L) (t:0<z)(v:2*z < Next.SectorChange.firstRadius group)
local notation "λZ"=> generalizeP B q z -- tune unused I binder
abbrev peep (b:Bool) (X: ClockD R r l k)(i:Axis) (L:Part N P):Prop:=(∀ u,blook (shade N i b X.gF) (shade N i b X.pF) (fun x=>L x u)) ∧ ∀ x, LocalOn (shade P i b X.pF) (L x)
include t v
lemma generalE (F:Forest (ratio B)){L:Part N P}(p:Envelope (Function.uncurry L)): Envelope (Function.uncurry (λZ L F)):=by
 let f:PairD N × Pane P→Pane P × Pane N:=fun x=>(x.2,x.1.2); have he:Measurable f:=measurable_snd.prodMk (measurable_snd.comp measurable_fst); have hb:Measurable (Function.uncurry (seine B F q z)):=(Skye.brake B q z F t v).measurable; have hv:Measurable ((Function.uncurry (seine B F q z))∘f):=hb.comp he; have hm:Measurable (fun x:PairD N × Pane P=> (x.1,seine B F q z x.2 x.1.2)):=measurable_fst.prodMk hv; exact Law.pull (f:=Function.uncurry L) (q:=fun x:PairD N × Pane P=> (x.1,seine B F q z x.2 x.1.2) ) p hm
omit t v
namespace Pear
variable {i X B z q} (p:Pear X i B b W)
include hp h p
lemma feel (q z) (f:Forest (ratio B)): peep b X i (generalizeP B q z W f):=by
 constructor; swap; · exact fun x U V hZ=> p.stern x _ _ (seer B h X hp i _ _ _ _ _ _ b (fun _ _=>rfl) (fun _ _ _=>rfl) hZ)
 intro U x y g v; let z1:=seine B f q z U x.2; let z2:=seine B f q z U y.2; exact (p.ore z1 x y g v).trans (p.stern y _ z2 (seer B h X hp i _ _ _ _ _ _ b (fun _ _=>rfl) v (fun _ _ _=>rfl)))
lemma songE (U:PairD N)(V:Pane P) : Arbor.visits _ (fun t : Forest (ratio B)=>generalizeP B q z W t U V) (shade N i b X.pF):=fun x y v=> p.stern U _ _ (seer B h X hp i x y _ _ _ _ b v (fun _ _ _=>rfl) (fun _ _ _=>rfl))
end Pear
local notation "μY"=> (grove (ratio B))
-- averaged
abbrev wince (B:Ratio N P)(q:Chi)(z:ℝ)(F:Part N P): Part N P:=fun x y=> Wager.meanS (grove (ratio B)) (fun A:Forest (ratio B)=> generalizeP B q z F A x y)
variable [hN:Nonempty (Forest (ratio B))]
include hN t v
lemma winceC {L:Part N P} (p:Envelope (Function.uncurry L)): Envelope (Function.uncurry (wince B q z L)):=by
 let Y:=PairD N× Pane P; let X'(x:Y × Forest (ratio B)):= (Function.uncurry (generalizeP B q z L x.2)) x.1; have h:= Wager.atMost X' (fun F=> generalE B q z t v F p); exact Law.fund μY (f:=X') h
omit hN t v
include h hp
lemma winceP (p:Pear X i B b W):peep b X i (wince B q z W):= ⟨fun U x y h1 h2=> integral_congr_ae (Eventually.of_forall fun t=>(p.feel h hp q z t).1 U x y h1 h2),fun x U V t=>integral_congr_ae (Eventually.of_forall fun L=>(p.feel h hp q z L).2 x U V t)⟩
omit hp
include hN
omit hN h
lemma t_avg {J:Type}[LinearOrder J][Fintype J]{E:Type}[MeasurableSpace E](μ:Measure E)[IsFiniteMeasure μ](U:UNI J){F:E→ FC J}(p:Envelope F) : meanS μ (fun t=>Fock.theta U (F t))=Fock.theta U (meanS μ F):=by
 unfold meanS; rw [←Wager.one μ (φ:=fun t=>_),←Wager.one (φ:=F) μ]; exact Wager.take μ (thetaCL _) p (Envelope.const 1) -- omit extras
include hN h
lemma tallyX(W:Part N P) : wince B q z (Travel i W)=Travel i (wince B q z W) :=by
 ext x U:2; let f(a:Forest (ratio B)):=generalizeP B q z W a (flipK i x) (Fixed.reflConfig P i U); let σ:= fun a:Forest (ratio B)=> moveTree B T h a (Fixed.reflectSweep N i); let E:=align B h (Fixed.reflectSweep N i)
 rw [show Travel i (wince B q z W) x U= theta (Fixed.reflectP P i) (meanS μY f) from rfl,←t_avg μY _ (Wager.mean_f f),meanS, ← Law.apply_pres E (measurable_of_countable (fun t=> theta (Fixed.reflectP P i) (f t)))]; apply integral_congr_ae; apply Eventually.of_forall; intro u; change theta _ (W _ (Fixed.reflConfig _ i (seine B u q z U _)))= theta _ (W _ (seine _ _ _ _ _ _)); unfold flipK; dsimp only; rw [mirrorG B h i q]
end Gale
end YM.CF.BProof.Bide
