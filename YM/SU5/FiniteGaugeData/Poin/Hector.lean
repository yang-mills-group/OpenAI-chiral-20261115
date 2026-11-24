import YM.SU5.FiniteGaugeData.Poin.Arc
import YM.SU5.FiniteGaugeData.Poin.Pole
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Real
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "a"=> timeAxis
namespace Flute
variable (e:Mink.Ray)(x y:E4)(t u v:ℝ)
def magnet : Cross timeAxis:= ⟨position e.val 0,show time (position e.val 0)=0 from time_position ..⟩
def fsp : Cross timeAxis:= SEP timeAxis x - Ray.along e x • magnet e
local notation "T"=> time x
local notation "E"=> magnet e
local notation "μ"=>Ray.along e
local notation "A"=> e.val
local notation "Θ"=> fsp e
lemma bearing : ‖magnet e‖=1:=by
 change ‖position e.val 0‖=1; apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1; simp [Mink.squares (position e.val 0),e.property]
lemma InnerSp : spatial (fsp e x).val = spatial x - (μ x) • e.val:=by
 change spatial (x-x timeAxis • basis timeAxis- (μ x) • position e.val 0)=_; simp [sub_eq_add_neg]
lemma innerSpace (u:Cross a) : inner ℝ u (magnet e)= e.along u.val:=by change inner ℝ u.val (position e.val 0)= _; rw [pairing]; simp [Ray.along]
lemma nez : inner ℝ (Θ x) (E)=0:=by rw [innerSpace]; unfold Ray.along; rw [InnerSp]; simp [inner_sub_left,inner_smul_left,Ray.along, e.property]
lemma btime (y:Cross a): time (board (magnet e) t u y)=t:= bclock ..
lemma sideSp(y:Cross a): spatial (board (magnet e) t u y)= spatial y.val+u • e.val:=by change spatial (y.val+u • position e.val 0+t • basis a)=_; simp
lemma bpart (Y:Cross timeAxis)(eY:inner ℝ Y (magnet e)=0): μ (board (E) t u Y) = u:=by unfold Ray.along; rw [sideSp e, inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,show inner ℝ (spatial Y.val) e.val= _ from (innerSpace e Y).symm.trans eY]; simp [e.property]
lemma attend : board (E) (time x) (μ x) (fsp e x)=x:=by apply ext_by; rw [sideSp,InnerSp]; simp; exact btime .. -- parentheses parser.П
-- Eu & Lor boost preserve orth rema.
variable (Y:Cross timeAxis)(eY:inner ℝ Y (magnet e)=0)
abbrev useu (r t u:ℝ):= cos r*t-sin r*u
abbrev user_ (r t u:ℝ):= sin r*t+cos r*u
include eY
local notation "x₀"=> board (magnet e) t u Y
lemma alto : walk (moveB e v).val (board (magnet e) t u Y)= board (magnet e) (useu v t u) (user_ v t u) Y:=by
 apply ext_by
 · change spatial (circleB e v x₀)=_; rw [stake,btime,bpart e t u Y eY,sideSp,sideSp]; unfold user_; module
 change time (circleB e v x₀)=_; rw [ttake,btime,bpart e t u Y eY,btime]
omit eY
abbrev hyperu (r t u:ℝ):= cosh r*t+sinh r*u
abbrev hypers (r t u:ℝ):= sinh r*t+cosh r*u
include eY
lemma trip : Lorentz.act (e.boost v) x₀= board (magnet e) (hyperu v t u) (hypers v t u) Y:=by
 apply ext_by
 · rw [Ray.boost_at, Ray.newSpace,btime,bpart e t u Y eY,sideSp,sideSp]; unfold hypers; module
 rw [Ray.boost_at, Ray.newClock,btime,bpart e t u Y eY,btime]
omit eY
-- stabilizer also keeps such coords; maybe use spatial Lor covariance without e. Need choose shelf for imaging e' via spatial.S.Earp.Instead transform Y by `rotate`, choose $v`=0 positions ambiguous. Derive via gestures height with χ zero both. 
lemma PinSep (p:Mink.Lorentz)(h:Pin p) : SEP timeAxis (Lorentz.act p x)= ⟨Lorentz.act p (SEP timeAxis x).val,show time (p.act _)=_ from ( (pin_iff p).1 h _ ).trans (SEP timeAxis x).property⟩:=by
 apply Subtype.ext; change _= (p.act (x-x a • basis a)); rw [map_sub,map_smul, show Lorentz.act p (basis a)=basis a from h]; change p.act x- time (p.act x) • basis a=p.act x- time x • basis a; rw [(pin_iff p).1 h]
#print axioms alto
#print axioms trip
end Flute
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
