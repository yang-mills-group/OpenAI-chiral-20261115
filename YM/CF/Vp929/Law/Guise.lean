import YM.CF.Vp929.Law.Spark
import YM.CF.Vp929.Law.Fire
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms March Filter Palace Mos
open scoped Topology Classical
namespace Delta
variable {C d:Side} {χ χ':Cover→ℕ}{x y:Cover} {B n:ℕ}(s:March)
local notation "H"=> (d.val*C.val)
local notation "T"=> (1000*H)
def Ticket(o:Cover)(n:ℕ)(ρ σ:Cover→ℕ):= Gear ρ σ o n
private lemma nearbyTicket(C d:Side)(i:ℕ){x y:Cover}(n:ℕ)(g:Gear χ χ' x ((i+1+n)*1000*(d.val*C.val)))(v:Range (1000*(d.val*C.val)) x y):Gear χ χ' y ((i+n)*1000*(d.val*C.val)):=by
 apply gear_near g v; rw [show i+1+n=i+n+1 by omega]; simp only [Nat.add_mul,Nat.one_mul]; omega
private lemma survey {o:Cover}(x:Cover)(i:ℕ)(g:Gear χ χ' x ((i+n)*T+T)) (p:∀ x,χ x<n): watch χ d C x o ↔ watch χ' d C x o:=by
 have m:n*H ≤ (i+n)*T:=Nat.mul_le_mul (by omega) (by omega)
 by_cases h:Range T x o; swap; · exact iff_of_false (fun e=> h e.2.1) (fun e=> h e.2.1)
 have eq: cull χ H o↔ cull χ' H o:= flashCull _ _ H o n (p _) (gear_near g h (by omega))
 unfold watch; rw [eq,g _ (Range.refl _ _|>.mono (le_refl _)),g o (h.mono (by omega))]
lemma ballotEq (n i:ℕ)(u:∀ x,χ x<n)(v:χ x < i) (g:Gear χ χ' x ((i+n)*T)): ballot χ d C x=ballot χ' d C x:=by
 induction i generalizing x with
 | zero=> omega
 | succ i ih=>
   rw [ballot.eq_1,ballot.eq_1 χ']; congr 1; ext k
   have H':(i+1+n)*T=(i+n)*T+T:=by rw [show i+1+n=i+n+1 by omega]; simp [Nat.add_mul]
   have e(o:Cover) := survey (o:=o) x i (H' ▸ g) u
   constructor
   · intro E y v'; obtain H'' : watch χ d C x y:= (e y).2 v'; rw [←ih (x:=y) (by exact Nat.lt_of_lt_of_le H''.2.2 (Nat.le_of_lt_succ v)) (gear_near g H''.2.1 (by omega))]; exact E y H''
   intro E y v'; have v'':χ y < i:= Nat.lt_of_lt_of_le v'.2.2 (Nat.le_of_lt_succ v); rw [ih v'' (gear_near g v'.2.1 (by omega))]; exact E y ((e y).1 v')

private lemma flare (n p:ℕ)(u:∀ x,χ x < n) (g:Gear χ χ' x (p+2*H+(n+n)*T)) (t:Coloring χ T) (sz:64*(pinch+1)≤d.val) {o:Rooms}(e:Range p x o.foot)(v:o∈ windQ χ d C): o∈ windQ χ' d C:=by
 rcases v with ⟨y,a,rfl⟩; let z:= clusterQ χ d C y; let i:= z.foot; have s: Range (p+2*H) x y:= (e.trans (Range.symm ((Delta.plot_here (lotto d C (ballot χ d C y)) i y).1 (foot_in z)))).mono (Nat.add_le_add_left (culled χ d C sz t y).2.2 p); let h:= gear_near g s (le_refl _); refine ⟨y,(flashCull χ χ' _ y n (u y) (fun i v=>h i (v.mono ?_))).1 a,?_⟩
 · exact Nat.mul_le_mul (Nat.le_add_left n n) (show H ≤ T by omega)
 unfold clusterQ; rw [ballotEq n n u (u y) h]
-- build Pal
abbrev roofLength (d:Side) :Side:= 4*d
def mapW (χ:Cover→ℕ) (f:Cover→Signed × Bool) (x:Rooms):March:= let a:= Master χ x; ⟨(f a).1,(f a).2,a⟩
def village(χ:Cover→ℕ)(f:Cover→Signed × Bool)(C d:Side):Pal:= ⟨windQ χ d C,tintCode χ,mapW χ f⟩
lemma room_ready(z:64*(pinch+1)≤d.val)(t:Coloring χ T)(f:Cover→Signed × Bool) : Ready C (roofLength d).val (village χ f C d):= by
 have he:(roofLength d).val*C.val=4*H:=by change 4*d.val*_=4*_; rw [Nat.mul_assoc];
 refine ⟨he.symm ▸ gathered z t,fun X e=>rent (gathered z t) _ e.1 (collation χ d C z t)⟩
variable {f F:Cover→ Signed×Bool}
lemma meetTown (o:Cover)(n p:ℕ)(u:∀ x,χ x<n)(v:∀ x,χ' x<n)(R:Coloring χ T)(Z:Coloring χ' T)(g:64*(pinch+1)≤d.val)(e:Gear χ χ' o (p+4*H+(n+n)*T))(t:Gear f F o (p+4*H)) : Pal.Atem p ((roofLength d).val*C.val) o (village χ f C d) (village χ' F C d):=by
 have h:(roofLength d).val*C.val=4*H:=by change 4*d.val*_=4*_; rw [Nat.mul_assoc]
 have hp(x:Rooms)(u:x.bounded ((roofLength d).val*C.val))(v:Range p o x.foot)(i:Cover)(l:i∈x.marks):χ i=χ' i ∧ f i=F i:=by
    rw [h] at u; have p:=v.trans (within u (foot_in _) l); exact ⟨e i (p.mono (Nat.le_add_right ..)), t i p⟩
 refine ⟨⟨fun i t=> ⟨flare n p u (fun x w=>e x (w.mono (by omega))) R g t, flare n p v (fun x w=>(e x (w.mono (by omega))).symm) Z g t⟩⟩,fun x u v=> TintCompare (fun i w=> (hp x u v i w).1),fun x u v=>?_⟩; let k:=hp x u v; let V:=Master χ' x; have a:Master χ x=V:=by
    refine pick (B:=4*H) (fun x y v=>R x y (v.mono (by omega))) (h ▸ u) (at_home _ _) ?_; rw [(k V (at_home χ' x)).1,(k (Master χ x) (at_home χ x)).1]; exact lowT _ _ (at_home χ x)
 simp only [village,mapW]; change _; unfold V at *; rw [a,(k _ (at_home χ' x)).2]

lemma turnPal (u:Coloring χ T)(p:χ=χ'∘s.slide)(e:∀ x, F (s.slide x)=(s.step*(f x).1,(s.charge.xor (f x).2))) : Pal.Twist (village χ f C d) (village χ' F C d) s ((roofLength d).val*C.val) :=by
 refine ⟨wind_spin C d s p,fun i=>paintCharge s p i,fun x h=>?_⟩; let i:=Master χ x; have v: Master χ' (s.follow x)=s.slide i:= (turnMaster s p (B:= (roofLength d).val*C.val) (fun x y v=>u x y (v.mono (by change 4*d.val*C.val ≤ T; rw [mul_assoc]; omega))) x h).symm
 change mapW _ _ _=_; unfold mapW; simp only [v]; rw [e]; apply March.ext <;> rfl
end Delta
end YM.CF.VolumeCape
