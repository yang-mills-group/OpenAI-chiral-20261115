import YM.CF.BProof.Transit.Action
import YM.CF.Sour.Candy
import YM.CF.Levier.Culler
import YM.CF.BProof.Mote.Hall
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive Tap Haro
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye
set_option synthInstance.maxSize 28000
namespace Leg
variable {m n : Type}[LinearOrder m][Fintype m][LinearOrder n][Fintype n]
def port (b:Bool)(x:Ket n): FC n:= if b then create x else remove x
lemma pipe_pail (b:Bool)(S:Finset n)(U:m↪n)(e:Deck U S)(x:Ket m)(p:Wave n): pailL U S (acts (port b (coat U x)) p)= acts (port b x) (pailL U S p):=by
 apply ext_inner_left ℂ; intro y; rw [pails _ _ e,←act_inner,←act_inner,pails _ _ e]; cases b
 · unfold port remove; simp only [Bool.false_eq_true,↓reduceIte,star_star]; rw [hoist_c _ _ e]
 unfold port; simp only [ite_true]; exact congrArg (inner ℂ · p) (hoist_r U S e x y).symm
lemma trails_back (E:m≃n)(x:Ket n): coat E.toEmbedding (trailK E.toEmbedding x)=x:=by rw [stance,show lows E.toEmbedding=univ by unfold lows; ext; simp]; apply PiLp.ext; intro i; rw [cut_apply, if_pos (mem_univ _)] -- tune
lemma about (E:m≃n) (b:Bool)(x:Ket n)(p:Wave m): acts (port b x) (cartsL E p)= cartsL E (acts (port b (trailK E.toEmbedding x)) p):=by
 unfold cartsL; cases b; simpa only [port,Bool.false_eq_true,↓reduceIte,trails_back] using (hoist_r E.toEmbedding ∅ (shelfG E) (trailK E.toEmbedding x) p).symm; simpa only [port,ite_true,trails_back] using (hoist_c E.toEmbedding ∅ (shelfG E) (trailK E.toEmbedding x) p).symm
variable {N P:Side} (Q:SpaceM)
abbrev eligibleZ (P:Op n)(b:Bool)(x:Ket n):Prop:= acts P x= if b then x else 0
abbrev okSpin (b:Bool)(x:Ket (Single N)):= eligibleZ (tickA N) b x
def belt (N:Side)(Q:SpaceM)(b:Bool):= if b then exp (plankP N Q.val) else exp (-(plankP N Q.val))
local notation "A_"=> plankP N Q.val
lemma belt_acts (p:Ket (Single N))(b:Bool)(x:Phys N): acts (port b p) (scaleZ Q.val x)=scaleZ Q.val (acts (port b (acts (belt N Q b) p)) x):=by
 let V:= exp (-A_); have he:star V=V:=by unfold V; rw [star_exp,star_neg,plank_h Q.property.adj]
 unfold scaleZ; simp only [map_smul]; congr 1; cases b
 · rw [← act_mul,←act_mul]; change acts _ x=_; unfold port belt; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),quant_ann,show star _ = _ from he]
 have hk:V*exp A_=1:=mul_eq_one_comm.mp (Fock.wind_inv ..)
 unfold port belt; rw [if_pos rfl,if_pos rfl,if_pos rfl,←act_mul,←act_mul,quant_create,←act_mul,hk,act_one]
lemma belt_comm {C: Op (Single N)}(p:Commute C (plankP N Q.val))(b:Bool): Commute C (belt N Q b):=by
 letI : NormedAlgebra ℚ (Op (Single N)):= NormedAlgebra.restrictScalars ℚ ℂ _; cases b; exact p.neg_right.exp_right; exact p.exp_right
lemma shine {A C:Op n}{x:Ket n}(p:acts A x=x)(h: Commute A C): acts A (acts C x)= acts C x:=by rw [←act_mul,h.eq,act_mul,p];
lemma beam (b:Bool){A C:Op n}{x:Ket n}(p:eligibleZ A b x)(h:Commute A C): eligibleZ A b (acts C x):=by cases b; change acts _ _=0; rw [←act_mul,h.eq,act_mul,show acts A x=0 from p,map_zero]; exact shine p h
lemma belt_s {x:Ket (Single N)}{b:Bool}(h:okSpin b x): okSpin b (acts (belt N Q b) x):= beam b h (belt_comm Q (plank_tick _) b)
lemma belt_turn (i: Axis)(b:Bool): twist (Fixed.reflectP N i) (belt N Q b)= belt N Q (!b):=by
 let U:= Fixed.reflectP N i; let s:=Fixed.reflectSweep N i
 have hx:= Sour.plight s Q.val Q.property; unfold Sour.bolt Sour.γS Sault.hitL at hx; have hp: detX s.s=true:= Spire.det_t i
 rw [hp] at hx; -- tune
 rw [show s.charge=false from rfl,←Sour.poll (castX s) false A_ (Fixed.pinSpin i) (spinU false s.s) (by rw [show detX (castX s).s=_ from hp]; exact mirrorX i) (spinZ false (castX s).s)] at hx
 have h1: twist U A_ = -A_:=by rw [Fixed.castX_reflect] at hx; change -star (twist U A_)=A_ at hx; rw [← map_star,plank_h Q.property.adj] at hx; exact neg_injective (hx.trans (neg_neg _).symm)
 cases b<;>simp only [belt,breeze_exp, Bool.false_eq_true, Bool.not_false,Bool.not_true, ite_true, ↓reduceIte]; rw [map_neg,h1,neg_neg]; exact congrArg exp h1
lemma belt_frame (i: Axis)(b:Bool)(x:Ket (Single N)): acts (Fixed.reflectP N i).val (acts (belt N Q b) x)=acts (belt N Q (!b)) (acts (Fixed.reflectP N i).val x):=by rw [← belt_turn]; exact Fock.swivel ..
lemma belt_reach (R: Support (More N))(b:Bool): Commute (cutM (modes R)) (belt N Q b):=by
 apply belt_comm; unfold Commute SemiconjBy; ext i j; rw [cutM,Matrix.diagonal_mul,Matrix.mul_diagonal]; by_cases h:i.1.1=j.1.1; simp [h]
 have he: plankP N Q.val i j=0:=by unfold Tap.plankP Tap.headW; rw [loveAt]; exact if_neg h
 rw [he,zero_mul,mul_zero]
end Leg
end YM.CF.BProof.Bide
