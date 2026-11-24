import YM.CF.Vp929.Paint.Active
import YM.CF.Vp929.Law.Fire
import YM.CF.Vp929.Law.Guise
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Mesh Lattice Rooms Atlas Delta Guide MeasureTheory Palace Mos Mesa Cube Lat
open scoped Topology Classical NNReal Matrix.Norms.Frobenius
namespace Cane

private lemma sentinel(i:ℕ):∃ d:Side,i ≤ d.val:=⟨⟨i+1,by omega⟩,Nat.le_succ _⟩
def granite:Side:=(sentinel (64*(pinch+1))).choose
lemma grain:64*(pinch+1) ≤ granite.val:=(sentinel _).choose_spec
variable (C:Side)
abbrev Huge:=granite.val*C.val
abbrev Belt:= (Delta.roofLength granite).val*C.val
def Bolt:ℕ:=1000*Huge C
abbrev Record C:=Cover→Mark (Bolt C)
def tint(P:Record C)(x:Cover):ℕ:= (P x).1.val
def sails(P:Record C)(x:Cover):Signed×Bool:= ((P x).2.dir,(P x).2.charge)
def Trust (P:Record C): Prop:=Coloring (tint C P) (Bolt C)
def home (P:Record C):Pal:=Delta.village (tint C P) (sails C P) C granite
lemma abide(P:Record C)(t: Trust C P): Ready C (Delta.roofLength granite).val (home C P):= Delta.room_ready grain t (sails C P)
abbrev RoofRise:=1+5*40*Belt C
def Fringe:ℕ:= RoofRise C +4*Huge C+(Atlas.height (Bolt C)+Atlas.height (Bolt C))*Bolt C
variable {K:ℕ→ℝ}{A D:Realms}(P P':Record C)(t: Trust C P)(k:Trust C P')
protected def Q (C:Side)(K:ℕ→ℝ)(P:Record C)(A:Realms): Realms:=(home C P).board C K A 5
include t k
lemma matchTurn (s:March) (h:∀ a,P' (s.slide a)=((P a).1,Atlas.star s*(P a).2)) (K:ℕ→ℝ)(A:Realms) : Cane.Q C K P (s.turns A)=s.turns (Cane.Q C K P' A):= by
 unfold Cane.Q; refine Pal.turns_board (abide C P t) (abide C P' k) K s (turnPal s (χ:=tint C P) t ?_ ?_) 5
 · exact funext fun i=>by simp only [tint,Function.comp_apply,h]
 intro i; unfold sails; rw [h]; rfl
lemma inScope (o:Cover)(h:Gear P P' o (Fringe C))(A D:Realms)(k':Agrees {v| Range (Fringe C) o v} A D) : Agrees {v| Range 1 o v} (Cane.Q C K P A) (Cane.Q C K P' D):=by
 let p:= RoofRise C; let E:=p+4*Huge C; let b:=Belt C
 have Z:1+5*40*Belt C ≤ Fringe C:= by unfold Fringe RoofRise; omega
 apply Pal.BoardBound (abide C P t) (abide C P' k); swap; · exact fun _ u v=> k' _ ((u: Range _ _ _).mono Z) ((v:Range _ _ _).mono Z)
 refine Delta.meetTown o (Atlas.height (Bolt C)) (RoofRise C) (χ:=tint C P) (χ':=tint C P') (fun x=>(P x).1.isLt) (fun x=>(P' x).1.isLt) t k grain ?_ ?_
 · intro j v; unfold tint; rw [h j v]
 intro j v; unfold sails; rw [h j (v.mono (Nat.le_add_right ..))]
omit P' k
lemma measurable(K:ℕ→ℝ):Measurable (Cane.Q C K P) := Pal.runs (abide C P t) ..
lemma paying{u d:ℝ}(p:Sweater C (Delta.roofLength granite) K u d)(A:Realms)(i:Cover)(j:PlaqAxes):Mesa.lambda (faceValue (Cane.Q C K P A) (i,j))≤d:= p.wind (abide C P t) ..
lemma glowing{u d:ℝ}(p:Sweater C (Delta.roofLength granite) K u d)(A:Realms)(i:Edge Cover)(v:∀z:Cover,Range (Fringe C) i.1 z→∀j:PlaqAxes,Mesa.lambda (faceValue A (z,j))≤u): Cane.Q C K P A i=A i:= p.lamp (home C P) (abide C P t) _ _ (fun z p=> v z (p.mono (show Belt C ≤ Fringe C from by unfold Fringe RoofRise; omega)))
omit t P

lemma faith(n:Side)(p:2*(spanR* Bolt C)<n.val)(x:Sent n p): Trust C (patchM n p x ∘ wrap n):=fun i j q v=> Mesh.scented n p x i j q (Fin.ext v)
end Cane
end YM.CF.VolumeCape
