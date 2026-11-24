import YM.SU5.FiniteGaugeData.Endless.Horde
import YM.SU5.FiniteGaugeData.Celeritas.Lacem
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace InnerProductSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
set_option quotPrecheck false
variable {H :Hilbert} {a b:Axis}(S:OS.Semigroup H a) {K:Axis→ Hilbert}(W:∀ a:Axis,OS.Semigroup (K a) a)(Ω: (a:Axis)→(K a).space)
open Endless.Piper Mist
-- shared record data: Euclidean marks centered in cube at origin
structure Shrine (K:Axis→ Hilbert) where
 t : Axis→ℝ≥0 -- *half* physical width in each axis, centered.
 f : ∀ a:Axis,(K a).Op -- centering op.Physics.
namespace Land
variable (x y:E4)
abbrev leg(x:E4):H.Op:= S.U (SEP a x)
abbrev opt(x:E4)(F:H.Op):H.Op:= leg S x* F*leg S (-x)
local notation "T" x:max=> leg S x
lemma leg_add : leg S (x+y)=T x*T y:= (congrArg S.U (map_add _ ..)).trans (S.space ..)
lemma leg_inv : leg S 0=1:=by unfold leg; rw [map_zero,S.uZero]; rfl
lemma leg_pair : leg S (-x)*leg S x=1:=by rw [←leg_add,neg_add_cancel,leg_inv]
lemma leg_veil (t:ℝ) : leg S (t • basis a)=1:=by
 have h:SEP a (t • basis a)=0:= Subtype.ext (show t • basis a-_=_ by simp); unfold leg; rw [h,S.uZero]; rfl
lemma leg_sp (x:Cross a): leg S x.val=S.U x:=congrArg _ (yup x)
lemma leg_star : star (leg S x)=leg S (-x):=by
 have he : T x=(S.unit.translation (SEP a x).val):=Eq.symm (vacancy ..); let Θ: Willow H E4:= ⟨S.unit.translation,S.unit.origin,fun x y=>(S.unit.sends x y).symm,S.unit.unitary⟩
 rw [he]; unfold leg; rw [map_neg,←vacancy]; exact Θ.remit (SEP a x).val
lemma leg_e (t:ℝ≥0) : Commute (S.E t) (leg S x):= S.independent ..
lemma leg_G (v:H)(t:∀ x:E4,S.unit.translation x v=v) : leg S x v=v:=by unfold leg; rw [←vacancy]; exact t _
lemma leg_norm : ‖leg S x‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=> ((S.unitary (SEP a x) v).trans (one_mul ..).symm).le
lemma opt_add (F:H.Op): opt S x (opt S y F) = opt S (x+y) F := by simp only [opt,leg_add, neg_add_rev]; simp only [mul_assoc] -- `simp only leg_add` etc iter
lemma opt_zero (F:H.Op): opt S 0 F=F:=by rw [opt, neg_zero,leg_inv,one_mul,mul_one]
lemma opt_star (F:H.Op): star (opt S x F)=opt S x (star F):=by unfold opt; rw [star_mul,star_mul,leg_star,leg_star,neg_neg,mul_assoc]
lemma opt_C {X:Type*}[TopologicalSpace X](Tc:X→E4)(p:Continuous Tc)(F:H.Op)(u:X→H.space)(w: Continuous u): Continuous fun x=> opt S (Tc x) F (u x):=by
 let B(x):= F (leg S (-(Tc x)) (u x)); exact S.cont_cross B (fun x=>SEP a (Tc x)) (F.continuous.comp (S.cont_cross u (fun x=>SEP a (-(Tc x))) w ((SEP a).continuous.comp p.neg))) ((SEP a).continuous.comp p) -- capitalization cont_cross? 
-- Gap spec record
variable {σ:Type*}(F:σ→ Shrine K)(A:σ→E4)
variable {a b:Axis}{S:List σ}

def endX(a:Axis)(i:σ):ℝ:=A i a+ ((F i).t a:ℝ)
def startX(a:Axis)(i:σ):ℝ:= A i a-((F i).t a:ℝ)
def Seers(F:σ→ Shrine K)(A:σ→ E4)(a:Axis)(i j:σ):Prop:=endX F A a i < startX F A a j
abbrev Plot (i:σ)(x:E4) (a:Axis):= opt (W a) x ((F i).f a)
-- often use Tape with fixed order list. position
abbrev actO (a:Axis)(i:σ):= Plot W F i (A i) a
def Hi (a:Axis)(i j:σ) := (startX F A a j-endX F A a i).toNNReal
def Leap (a:Axis)(i j:σ): (K a).Op:= (W a).E (Hi F A a i j)
variable {σ:Type}(F:σ→ Shrine K)(A:σ→ E4)
def chorus (V:List σ)(a:Axis):= inner ℂ (Ω a) (Mist.TapeT (actO W F A a) (Leap W F A a) V (Ω a))
-- identity of any positional G products with centered versions
section
variable (S:OS.Semigroup H a)(D:σ→ H.Op)(J:σ→σ→ℝ≥0)(X: H)(v:∀ x, S.unit.translation x X=X)
local notation "D'" => fun i=>opt S (A i) (D i)
local notation "Y" => fun i j=> S.E (J i j)
local notation "Z" => fun i j=> S.E (J i j)*leg S (A j-A i)
include v
lemma ledger (V:List σ): inner ℂ X (TapeT D Z V X)= inner ℂ X (TapeT (fun i=>opt S (A i) (D i)) (fun i j=>S.E (J i j)) V X):=by
 let D0:=D'; let F:=Z; let G:=Y; cases V with
 | nil=> rfl
 | cons i V=>
    have he(i:σ):=leg_G S (-(A i)) X v; have hb(i):=leg_G S (A i) X v
    have hx(V:List σ)(i):TapeT D0 G (i::V) X= leg S (A i) (TapeT D F (i::V) X):=by
       induction V generalizing i with
        | nil=> change _=leg S (A i) (D i X); exact congrArg (fun x:H=>leg S (A i) (D i x)) (he i)
        | cons j V ih=> 
           change opt S (A i) (D i) (S.E (J i j) (TapeT D0 G (j::V) X))= _; rw [ih];
           let P:=leg S (-(A i)); let Q:=leg S (A j); have hg: P*G i j*Q=F i j:=by unfold P Q F; rw [(leg_e S (-(A i)) (J i j)).eq.symm,mul_assoc]; rw [←leg_add,sub_eq_add_neg,add_comm];
           exact congrArg (fun x':H.space=> leg S (A i) (D i x')) (DFunLike.congr_fun hg (TapeT D F (j::V) X))
    let u:=TapeT D F (i::V) X; change inner ℂ X u= inner ℂ X (TapeT D0 G (i::V) X); rw [hx]; change _= inner ℂ X (leg S (A i) u); nth_rw 2 [←hb i]; exact ((⟨(leg S (A i)).toLinearMap, S.unitary _⟩: H→ₗᵢ[ℂ] H).inner_map_map X u).symm
end
#print axioms ledger
end Land
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
