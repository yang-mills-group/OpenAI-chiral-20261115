import YM.CF.BProof.Payment.PayRoll
import YM.CF.BProof.Payment.Choice
/-! Calculation on one Palm Z-tag. Unpaid Spin before consuming. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.BProof.Payment
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Hero Stint Oasis Scree Palot Wick Crystal Garden Veil Trek Mark Mapping Angular Anthem
open Jet Vault Paige Drapes Moment RG Wilson Charge Tape
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {m B L:Side}{j:ℕ}{p: Odd L.val}{V: Pricing j L p (Vault.Thread j)}{δ:ℝ}(D:GramM (mid m B)){W:Grasp V B δ}(F:Loom (mid m B)) {Y:Yard (More (mid m B))}
variable {I:Type}[Fintype I](Q:Score Y I)(M:ℕ)
local notation "N_"=> mid m B
variable (L': Moment.Bill (More (mid m B)) SU.group)
structure Holds : Prop where
 exactF (x: Pane N_): D.path.inChannels D.funds D.p D.beta x= (∑ i:Y.Index,Q.gaugeCharge i x)+Charge.left Y x L'+heavyG D Y M x
lemma holdLemma {μ R ν:ℝ}(h:D.path.Bounds D.funds μ R ν)(k: Charge.ValidR D.funds D.p M)(g:Q.gaugeCharge=fun i x=> Charge.outlay Y i D.funds D.p D.path M D.beta x (Charge.weak D.funds D.p D.path M D.beta h k)): Holds D Q M (Charge.weak D.funds D.p D.path M D.beta h k):=by constructor; intro x; rw [g]; exact Charge.expenditures Y D.funds D.p D.path M D.beta x h k
variable (w: Holds D Q M L')
abbrev porches (z:Orbit N_) := (Charge.left Y z.1 L':ℂ)
def plume (z:Orbit N_)(f:Y.FaceS):ℂ:= (∑ i:Y.Index, Q.mask i z.1 (f i))
abbrev highMark(z:Orbit N_)(b:Y.FaceS):= (Madd (Q.SBook z.1 b)).prod (Score.chamber Y univ)
def Outlook(z:Orbit N_)(f:Y.FaceS):ℂ:= inner ℂ (mateK N_) (acts (highMark Q z f) (acts (tank (spar j D.J.M (F z)) (D.board z)) (relV W D.J (F z)))) -- W implicit? include
include w
lemma overhead(z:Orbit N_)(f:Y.FaceS): ask D W F Q z f M=Complex.exp (-Charge.left Y z.1 L'-plume Q z f-Pec.pigment D.J.I (F z)) * Outlook (W:=W) D F Q z f := by
 unfold ask; rw [ket₀_eq,map_smul,inner_smul_right]; unfold Outlook; rw [← mul_assoc,←Complex.exp_add]; refine congrArg (· * _) (congrArg Complex.exp ?_); rw [w.exactF z.1]; unfold Score.exponent plume; rw [sum_sub_distrib]; push_cast; abel -- tune casting unary neg ambiguity
omit w
variable {c η a b l r:ℝ}{K:Core j a b l r (mid m B)}{P:Spin.Ready j a b l r}{H:Honor P K δ}
variable {p':Pay}{A α₀ C Lr Cp t o ε α' C':ℝ}{D Q L' M}
structure Fund₀ (D:GramM (mid m B))(K:Core j a b l r (mid m B))(X:Spire.Pearl W) :Prop where
 member : D.J.P=K.aim.val
 own : D.J.M=K.M
 stamp : Stamped j L p V
 pos : 1 ≤ j
 road : W.roundZ≤ (mid m B).val
variable (J:Hinge W H c rateH η p' D.J.I A α₀ C Lr Cp) {y:Pay}{q:Cargo D t o}{Z: Oasis.Marks H y c rateH η}(T:Pantry Z q ε)(R: Oasis.Tube D y t ε o α' C') {z:Orbit (mid m B)}{x:Loft K δ c rateH η}{S:Support (mid m B)}{Y':Spire.Pearl W}{b':Y.FaceS}{u:ℂ}{X:Stun (mid m B)}
-- convenience
section
variable (Z D z x S b' u X Q)
def changeFee (f:Fields N_) :=∑ i, fBusy x Z D (desire Q z.1 b') z f u S i -- tune f variable sign
abbrev purc (f:Fields N_):ℂ:= Garden.outFuel D z f.1*Garden.outPay u S f.2
abbrev wageH : World (mid m B):= eyeWorld z.1 (sion x) X
end
variable (G:Fund₀ D K Y')(e:u≠0)(l':‖u‖≤ε)(w':Pick Q b' z.1 x Y'.q S X)(fx:F z=carried x.val.1)
include G e l' w' J T R fx
lemma outAware : Complex.exp (-Pec.pigment D.J.I (F z)) * Outlook (W:=W) D F Q z b' = ∫ f:Fields N_, purc D z S u f * Complex.exp (steam J T z.1 X x + changeFee D Q Z z x S b' u f) ∂gardenF N_:=by
 let A' := LastC x; let U:=carried x.val.1; let R':=lampWorld W x; let C':= Q.SBook z.1 b'; let A0:= Score.chamber Y univ
 let I:= Garden.siteJ A' (desire Q z.1 b')
 have hp:R'=relV W D.J (F z):=by rw [fx]; exact (Tape.realPulse W G.road x D.J G.member G.own) -- tune
 have ha: coreA x=spar j D.J.M (F z):=by rw [fx,G.own]
 unfold Outlook; rw [← hp,← ha]
 change Complex.exp (-Pec.pigment D.J.I (F z)) * inner ℂ (mateK _) (acts ((Madd C').prod A0) (acts (tank (coreA x) (D.board z)) R')) = _; rw [← Garden.pollinated D z (leanA x) u e S A0 x.val.1.val.2 w'.apart A' C' w'.safe w'.stamp R',←integral_const_mul]
 apply integral_congr_ae; apply Eventually.of_forall; intro f; dsimp only
 let v:= Complex.exp (-Pec.pigment D.J.I (F z)); have hB:(cbra A' x.val.1.val.2).ket=pressK x:=cbra_spec A' w'.safe x.val.1.val.2; change v*(purc D z S u f *values D z (coreA x) u S I R' _ f)=_; rw [hB,mul_left_comm v]; congr 1
 unfold v; rw [fx]; exact Veil.expect J T R G.stamp G.pos G.road X w'.slow w'.scene w'.beam l' S z I (desire Q z.1 b') (fun i _=>rfl) (cbra_coin (Q.healthy z.1 b') _) f -- tune signature
omit fx w' e G R
omit l'
-- support substitution Pay
include w'
-- abstract picked
lemma active (i:Y.Index) : Q.M.fee Y i Q.r (eyeWorld z.1 (sion x) X)=Q.mask i z.1 (b' i):=sum_congr rfl fun j hj=> (Q.M.page j).include_b (w'.spoke i j hj) -- tune field
omit w'
-- identity
variable {Q': Score Y (Manus.Poles (mid m B))}
variable (h':Holds D Q' M L')(k:Q'.M= Manus.plumb J T)
include G h' k fx R e l'
--
lemma actualF (w': Pick Q' b' z.1 x Y'.q S X) : ask D W F Q' z b' M= ∫ f: Fields N_,purc D z S u f * Complex.exp (-Charge.left Y z.1 L' + Q'.M.rest Y Q'.r (eyeWorld z.1 (sion x) X)+ changeFee D Q' Z z x S b' u f) ∂gardenF N_:=by
 have he:steam J T z.1 X x=(plume Q' z b') + Q'.M.rest Y Q'.r (eyeWorld z.1 (sion x) X):=by
    rw [← Manus.tally J T,← k,Manus.deliver]; exact congrArg (· + Q'.M.rest Y Q'.r (eyeWorld z.1 (sion x) X)) (sum_congr rfl fun i (_:i ∈ univ)=> active (J:=J) (T:=T) w' i)
 rw [overhead D F Q' M L' h', sub_eq_add_neg _ (Pec.pigment _ _), Complex.exp_add, mul_assoc,outAware (F:=F) J T R G e l' w' fx,←integral_const_mul]; apply integral_congr_ae; apply Eventually.of_forall; intro v; dsimp only; rw [mul_left_comm (Complex.exp _),←Complex.exp_add,he]; congr 2; abel -- tune
end YM.CF.BProof.Payment
