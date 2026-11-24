import YM.SU5.Reconstruction.Marque.Clipping
import YM.SU5.Reconstruction.Marque.Magnetic
import YM.SU5.Reconstruction.Marque.Hall
/-! Spell out Poincare kinematics and action together; preserve translation normalization.
Conditional, Haag-observable result, still not statement about all charges/rank etc. -/
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Metric NormedSpace ContinuousLinearMap BridgeClub CrossedFrame Passage
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical
variable {H:Hilbert}(N:Set E4→Net H)(S:OS.Semigroup H clock)(Ω:H)
local notation "W"=> Wander H.space
local notation "SB" => Picket.trans S
local notation "ϒ"=> mover S
local notation "Φ"=> Lot N S Ω
variable (X:Chair N Ω 0)(Y:Chair N Ω 1)(Z:Chair N Ω 2)
-- Spin + position group law; $(g,q)$ goes first moving and shifts target.
local notation "π"=> Two × E4
noncomputable def Origin : Two×E4:=(1,0) -- rigid
noncomputable def forecast (x y:π):π := (x.1*y.1, Motion x.1 y.2+x.2)
noncomputable def whiten (x:π):= {Λ:= onWorld x.1, b:=x.2:Mink.Poincare}
lemma lane(v:π)(x:E4): (whiten v).sends x=Motion v.1 x+v.2:=by change Mink.Lorentz.act (onWorld v.1) x+_= _; rw[onWorld_at]; rfl
lemma respects(g h:π): whiten (forecast g h)= whiten g*whiten h:= by apply Mink.Poincare.by_placement; intro t; rw[lane,Mink.Poincare.sends_mul,lane,lane]; unfold forecast; simp only [multiplies, visible_add,add_assoc]
lemma on_origin : whiten Origin=1:= Mink.Poincare.by_placement _ _ fun x=>by simp [lane,Origin]
lemma allFrames :Surjective whiten:=by intro v; obtain ⟨g,h⟩:= onWorld_onto v.Λ; exact ⟨(g,v.b), Mink.Poincare.ext _ _ h rfl⟩
noncomputable def Reception(g:Two→ W)(v:π):= (mover S v.2)* g v.1
-- packaging as action of envelope. 
structure Full where
 Bow : Two→* Wander H.space
 Lor(u:Two):Lot N S Ω false u (Bow u)
 nearGross: Continues (Bow: Two→ Wander H.space)
 live(v:Two × E4):Fleet (Reception S Bow v) false∧ Reception S Bow v Ω=Ω
 order(v w:Two× E4): Reception S Bow v * Reception S Bow w= Reception S Bow (forecast v w)
 starts : Reception S Bow Origin=1
 quenched : Bow bezel=1
 monitor : Continues (Reception S Bow)
 sends(v:Two× E4)(U':Set E4):IsOpen U'→ Conveys (Reception S Bow v) (N U') (N ((whiten v).sends '' U'))
-- honest matching
structure Matches (b:Full N S Ω) : Prop where
 ax(x:ℝ): b.Bow (Zip x)=X.boost (2*x)
 ay(x:ℝ): b.Bow (Yell x)=Y.boost (2*x)
 az(x:ℝ): b.Bow (Tuning x)=Z.boost (2*x)
-- coordinate transport between lobbies.night
namespace Annual
variable {S Ω X Y Z}
local notation "X'"=> MCourse
variable {N}
variable (p:Annual N S Ω X Y Z) (e:∀ x:E4,Picket.trans S x Ω=Ω) -- notation ALERT
omit e
local notation "μ"=> p.banner
local notation "R"=> Reception S p.banner
include p
lemma relates (v:π) : Fleet (R v) false:= (p.allWalk v.1).fleet.times (transport S v.2)
lemma relation (v:Two)(r:E4): p.banner v * mover S r=mover S (Motion v r)* p.banner v:=by
 ext1 x; simp only [wander_mul,mover_at]; exact ((p.allWalk v).wagon r x).symm
lemma buys(v w:π): R v* R w= R (forecast v w):=by
 have h(x y:E4):ϒ x*ϒ y= ϒ (y+x):=by
    ext1 z; rw [wander_mul,mover_at,mover_at,mover_at,add_comm]; exact DFunLike.congr_fun (Picket.trans_sum S x y).symm z
 unfold Reception forecast; change _=ϒ _ * μ _; rw [map_mul, mul_assoc,← mul_assoc (μ v.1),p.relation _,← mul_assoc (ϒ v.2),← mul_assoc (ϒ v.2),h, mul_assoc] -- tune
lemma profit : Continues R:= by
 apply nowC.mpr; intro v
 apply stackLimit (u:=mover S v.2) (v:=p.banner v.1) (U:=fun v:π=>mover S v.2) (V:=fun v:π=>p.banner v.1)
 · intro x; simp only [mover_at]; exact ((S.unit.moves x).comp continuous_snd).continuousAt.tendsto
 exact spirals (continuousAt_fst ..) p.schedule -- tune
variable (q:∀ (v:Set E4)(x:E4),Conveys (mover S x) (N v) (N (strace x v)))
include e q
lemma sells : ∃ g:Full N S Ω,Matches N S Ω X Y Z g:= by
 refine ⟨⟨μ,p.allWalk,p.schedule,fun v=>⟨p.relates v,show ϒ v.2 (μ v.1 Ω)=Ω from by rw [(p.allWalk _).pecan,mover_at,e]⟩,p.buys,?_,p.payBezel,p.profit,?_⟩,⟨p.pennantX,p.pennantY,p.pennantZ⟩⟩
 · unfold Reception Origin; rw [map_one,mul_one]; ext1 x; rw[mover_at]; exact DFunLike.congr_fun S.unit.origin _ -- syntax
 intro v V o; obtain ⟨B,A⟩:=v; unfold Reception; change Conveys (ϒ A*μ B) _ _; let Ux:=roller false B; rw [show (whiten (B,A)).sends '' V = strace A (roller false B '' V) from ?_]; exact ((p.allWalk B).ready V o).joins (q _ _) (p.allWalk B).fleet; unfold strace; rw [image_image]; congr! 1; exact lane .. -- eta
end Annual
end YM.Marque.Flow
