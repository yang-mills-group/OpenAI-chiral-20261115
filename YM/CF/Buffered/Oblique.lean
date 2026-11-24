import YM.CF.Buffered.Crowns
import YM.CF.Buffered.Piling
/-! Recurrence patches on the lifted gauge torus. Assign common values on ALL
 bonds whose *tail* is within dual rook plank of a cut. Not just the bonds
 crossing. Script bins include each cell all axes simultaneously. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Crust
open Function Filter Finset Lattice Wilson RG PathData Work.F03
open Cube Region Roost Rush
open scoped InnerProductSpace Matrix.Norms.Frobenius BigOperators Topology
variable {G:Gauge}{N P D:Side}{a b:ℝ}{s:ℕ}
variable (K:Planck N P D)
namespace Grid
abbrev Tower (n: Side):= Rail (Uniform n)
private lemma post_nat (x:Site P)(i:Axis): 0≤natural x i ∧ natural x i<P.val := by
   have he:=ZMod.val_lt (x i); unfold natural; omega
private def place(P:Side): Site P≃ Post P where
 toFun x := ⟨natural x,fun i=> by rw [wall_mem i (mem_univ _)]; obtain ⟨b,v⟩:=post_nat x i; omega⟩
 invFun x:= wrap P x.val
 left_inv:= nat_true
 right_inv x:= Subtype.ext (by funext i; change (↑(wrap P ↑x i).val:ℤ)=_; rw [wrap_here,int_val _ (x.nonneg i) (x.below i (mem_univ _)), Int.toNat_of_nonneg (x.nonneg i)])
def send(K:Planck N P D) : Tower D × Site P ≃ Site N := ((Equiv.refl _).prodCongr (place P)).trans K.slots
lemma toe (r: Tower D) (x:Site P): send K (r,x)=K.zone r (natural x):= rfl
def gridFrom (z: Site N): Site P:= ((send K).symm z).2 -- keyword
-- map this site to the cell index (uses half-open convention)
def ledge (z:Site N): Tower D:= ((send K).symm z).1
lemma tile (x:Site N) : K.zone (ledge K x) (natural (gridFrom K x))=x:=by rw [←toe]; exact (send K).apply_symm_apply x
def lesser₀ : Site N→+ Site P := { toFun:= fun x i=> (ZMod.castHom (m:=P.val) (n:=N.val) (show P.val∣ N.val from ⟨D.val,K.ratio⟩) (Per P)) (x i), map_zero':=funext fun _=> map_zero _,map_add':=fun _ _=>funext fun _=> map_add _ _ _ }
lemma lesser_w (v:Cover): lesser₀ K (wrap N v)=wrap P v:=funext fun i=> map_intCast (ZMod.castHom (m:=P.val) (n:=N.val) (show P.val∣ N.val from ⟨D.val,K.ratio⟩) (Per P)) (v i)
lemma lesser_pay (z:Site N): lesser₀ K z=gridFrom K z:=by
 nth_rw 1 [← tile K z]; rw [Planck.zone, lesser_w,map_add, Rush.nat_true, show wrap P (K.sail (ledge K z))=0 from funext fun i=>?_ ,zero_add]
 change (((↑P.val * ↑(ledge K z i).val:ℤ):Per P))=0; push_cast; rw [ZMod.natCast_self,zero_mul]
lemma lesser_add (x y:Site N) : gridFrom K (x+y)= gridFrom K x+gridFrom K y:=by simp_rw [←lesser_pay,map_add]
lemma lesser_c (d:Step) : gridFrom K (d.vec:Site N)=d.vec:=by rw [←lesser_pay, ←wrap_vec N, lesser_w, wrap_vec]
lemma lesser_here(r:Tower D)(p:Site P): ledge K ((send K) (r,p))=r ∧ gridFrom K ((send K) (r,p))=p:=by unfold ledge gridFrom; simp

-- strips. Deep site in POST may walk back up to v gauge sites and remain in same tile.
def Deep (P:Side) (u:Site P) (v:ℕ) := ∀ i,(v:ℤ)≤ natural u i ∧ natural u i+(v:ℤ)<P.val
def stripP(P:Side)(v:ℕ) : Finset (Edge (Site P)):=by classical exact univ.filter fun x=>¬Deep P x.1 v
lemma strip_iff(v:ℕ)(i:Edge (Site P)): i∉stripP P v ↔ Deep P i.1 v:=by classical simp [stripP]
lemma ledge_v (r:Tower D) (p:Site P)(g:Deep P p s) (z:Site N)(h:separation z ((send K) (r,p)) ≤ s) : ledge K z=r := by
 let q:= (send K) (r,p); let x:=Lattice.lift (z-q); let w:Cover:=natural p+x
 have ht(i:Axis):0≤ w i∧w i<P.val:=by
    have hx:(x i).natAbs ≤ s:=(component_le ..).trans h; obtain ⟨p₁,p₂⟩:=g i; change 0 ≤ natural p i+x i∧ natural p i+x i<P.val; omega
 let b:= wrap P w; have hr:natural b=w:=by funext i; unfold natural b; rw [wrap_here,int_val _ (ht i).1 (ht i).2, Int.toNat_of_nonneg (ht i).1]
 have he:z=send K (r,b):=by
    rw [toe,hr]; unfold w Planck.zone; rw [←add_assoc,map_add,show wrap N (K.sail r+natural p)=q from rfl, show wrap N x=z-q from wrap_lift .., add_sub_cancel] -- wrong
 have hw:= lesser_here K r b; exact he ▸ hw.1

def issue(h: Tower D → Config G P) : Config G N := fun x=> h (ledge K x.1) (gridFrom K x.1,x.2)
variable {K}
structure Connected (s:ℕ)(a:ℝ)(Y:Tower D→ Config G P) : Prop where
  bond : ∀ r t, ∀ i∈stripP P s, Dg G (Y r i) (Y t i) ≤ a
variable (K) (Y:Tower D→ Config G P){r:Tower D}{x:Site P}
include K
lemma allocated (z:Site N)(i:Axis)(u:0≤a)(t:Connected s a Y)(h:separation z (send K (r,x))≤ s): Dg G (issue K Y (z,i)) (Y r (gridFrom K z,i))≤a:=by
 cases t with| mk t=>
 by_cases g:(gridFrom K z,i)∈ stripP P s
 · exact t _ _ _ g
 unfold issue; dsimp only
 have ht:(ledge K z)=r:=by
    symm; apply Eq.trans ((lesser_here K r x).1.symm); apply ledge_v K (ledge K z) (gridFrom K z) ((strip_iff _ _).1 g) (send K (r,x)); rw [toe K (ledge K z),tile,separation_comm]; exact h
 rw [ht,Dg_self]
 -- strip may empty (s=0). add a≥0 argument
 exact u
private lemma tock (_u:ℕ)(o:Site N)(v:Site P)(d:Lattice.Step) (e:gridFrom K o=v): gridFrom K (o+d.vec)=v+d.vec:=by rw [lesser_add,e,lesser_c]
lemma travel_g (p:Tower D)(x:Site P)(w: Walk)(g:Connected s a Y)(u:0≤a)(h:w.length ≤ s) :
 Dg G (travel (issue K Y) (send K (p,x)) w) (travel (Y p) x w) ≤ w.length*a :=by
 suffices he:∀ (l:Walk)(z:Site N),separation z (send K (p,x))+l.length≤ s → Dg G (travel (issue K Y) z l) (travel (Y p) (gridFrom K z) l)≤ l.length*a from by have H:=he w (send K (p,x)) (by simpa); rw [(lesser_here K p x).2] at H; exact H
 intro l; induction l with
 | nil=> intro z _; simp [travel,Dg_self]
 | cons d l ih=>
   intro z h'; let y:= z+d.vec; let t:= send K (p,x); let Z:=issue K Y; let V:=Y p
   have he: separation y t+l.length ≤ s:=by
       have hv:= separation_triangle y z t; have hx: separation y z≤1:=by rw [separation_comm]; exact Work.E04.stop_separation_le z [d] -- tune
       rw [List.length_cons] at h'; unfold t at *; omega
   have hx : Dg G (d.read Z z) (d.read V (gridFrom K z))≤a:=by
       have ht: separation z t ≤ s:=le_trans (Nat.le_add_right ..) h'; obtain ⟨i,v|v⟩:= d
       · exact allocated K Y z i u g ht
       change Dg G ((negDir i).read Z z) ((negDir i).read V _ )≤a; rw [Step.neg_read, Step.neg_read,Dg_inv]; rw [sub_eq_add_neg (gridFrom K z),←(show gridFrom K (z-step i)=_ from (show gridFrom K (z-step i)=gridFrom K z+-step i from (by rw [sub_eq_add_neg]; exact tock K 0 z _ (negDir i) rfl)))]; exact allocated K Y (z-step i) i u g (by rw [sub_eq_add_neg]; exact (Nat.le_add_right ..).trans he)
   rw [travel, travel,List.length_cons] -- remove
   refine (Dg_mul ..).trans ?_; rw [← tock K 0 _ _ d rfl]; push_cast; exact (add_le_add hx (ih y he)).trans_eq (by ring)
end Grid
end YM.CF.Buffered.Crust
