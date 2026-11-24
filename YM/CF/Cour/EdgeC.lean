import YM.CF.Levier.Hymn
import YM.CF.Hom.Sally
import YM.CF.Cour.Monet
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory
open Pec Reef Levier
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N m X B L:Side}{n k j:ℕ}{e d t x u C A:ℝ}
variable{G:Ratio (CSide m B) (CSide X B)}{p: Aim N}
abbrev turnsH (b:Bool)(a:Shape)(U:UNI SpinIdx)(X:Op (Single N)):= sings b (prepU a U (xtra b) N) X
def yank (b:Bool)(a:Shape)(U:UNI SpinIdx)(X:Op (Single N)):= Thera.jazz (detX a.s) (turnsH b a U X)
lemma turn_h(a c:Shape)(b t:Bool)(U V:UNI SpinIdx)(x: Op (Single N)): yank t c V (yank b a U x)=yank (b.xor t) (joinX a c) (V*whiten t U) x:=by
 let W:=V*whiten t U; have hh(Q:Op (Single N)):turnsH t c V (turnsH b a U Q)=turnsH (b.xor t) (joinX a c) W Q:=by unfold turnsH; rw [wake_r, show (prepU _ V _ N)*whiten _ _=prepU (joinX a c) W (xtra (b.xor t)) N from turns N b a U V c t]
 let X:=turnsH b a U x; have he(Q:Op (Single N))(u:Bool):turnsH t c V (Thera.jazz u Q)=Thera.jazz u (turnsH t c V Q):=by cases u; rfl; unfold turnsH Thera.jazz; rw [singT,singT]; simp only [ite_true,win_n,win_s,map_neg,map_star]
 unfold yank; rw [he,hh, show (joinX a c).s=a.s*c.s from rfl,det_p]
 cases d:detX a.s<;>cases k:detX c.s<;>simp [Thera.jazz,W]
lemma turn_r(a:Shape)(b:Bool)(U V:UNI SpinIdx)(x:Op (Single N))(p:JetS a.s b (detX a.s) U)(h:JetS a.s b (detX a.s) V): yank b a U x=yank b a V x:=by
 obtain ⟨z,h,hz⟩:=kitsX b a.s U V p h
 apply congrArg (Thera.jazz (detX a.s)); unfold turnsH; rw [singT,singT,twist_formula,twist_formula,show (prepU a U (xtra b) N).val= z • (prepU a V (xtra b) N).val from Ygs _ _ _ h, Matrix.smul_mul,star_smul,Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_comm (star z),hz,one_smul]
lemma apart(a:Shape): joinX (lagX a.t) (incX a.s)=a:=by unfold joinX lagX incX; simp
lemma spin_c (a:Shape)(V:Post N):stir (xtra true) a V=echo (Yg a V):=rfl
lemma peak_f (X:Aim N)(h:Ample X.den)(t:Cry X)(a:Shape)(b:Bool)(U:UNI SpinIdx)(q:JetS a.s b (detX a.s) U)(V:Bkg (More N)): X.den (stir (xtra b) a V)=yank b a U (X.den V):=by
 have hp:X.den (Yg a V)= ZoneH a (X.den V):=by calc
    _ = X.den (Yg (incX a.s) (Yg (lagX a.t) V)):=by rw [←kor, apart]
    _ = _:=by rw [h.plane,h.across,zno,apart]
 cases b
 · exact hp.trans (z_spin a _ _ q)
 rw [spin_c,cry_p t,hp,rally_p]
 let x:=X.den V; let B:= spinU false a.s; let Y:=ZoneH (n:=N) a x; have hy:Y=yank false a B x:=z_spin a _ _ (spinZ ..)
 let t':=turn_h a diva false true B axS (X.den V); have hv: joinX a diva=a:=by simp [diva,incX,joinX]
 have hz:JetS diva.s true (detX diva.s) axS:= det_i.symm ▸ cloneSX
 have hl:JetS (joinX a diva).s true (detX (joinX a diva).s) (axS*whiten true B):= shineU false a true _ _ _ (spinZ ..) hz
 rw [hv,Bool.false_xor] at t'; rw [hv] at hl; rw [←turn_r a true _ _ _ hl q,← t']; change sings true _ Y=yank true diva axS (yank false a B x); rw [←hy]
 unfold yank; rw [show detX diva.s=false from det_i]; rfl
lemma portPartH (X: Pride N)(h:WordK X)(hk:ClearP X)(a:Shape)(b:Bool)(V:Bkg (More N)): pigment X (stir (xtra b) a V)= cSignX (b.xor (detX a.s)) (pigment X V):=by
 have hp:pigment X (Yg a V)= cSignX (detX a.s) (pigment X V):=by calc
    _ = pigment X (Yg (incX a.s) (Yg (lagX a.t) V)):=by rw [←kor, apart]
    _ = _:=by rw [show pigment X (Yg (incX a.s) _) = _ from prog (zinger X) (Yg (lagX a.t) V) a.s,complX]; exact congrArg (cSignX _) (tolls h _ _)
 cases b
 · rw [Bool.false_xor]; exact hp
 rw [spin_c,pig_g]; rw [hp,← sign_seq]; have hx:star (pigment X (Yg a V))=pigment X (Yg a V):=by
    have hv:= spot X hk (Yg a V); rw [pig_g] at hv; exact hv
 -- tune
 rw [hp] at hx; exact hx.symm
lemma pledge (a b c:ℂ)(t:Bool): cSignX t (a+b-c)=cSignX t a+cSignX t b-cSignX t c:=by cases t; rfl; simp [cSignX]
end YM.CF.Cour
