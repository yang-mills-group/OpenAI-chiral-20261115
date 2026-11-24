import Merino.Mitre.Crystal
import Merino.Medal.Scepter
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 620000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Mitre
open Fock Finset Lattice Lat Spire Scroll Cube Branch Skye Tenant RG BProof
open scoped BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Buffered
variable {N:Side}
open Brooch

open Roots Lamour.Bridge.Celeste.Clock Fabric Thera

open Cuff Lace Medal Garter
variable (F:Obs N)
-- supply credential
structure Sits(F:Obs N)(s:Sweep N)(b:ℕ)(c:ℝ):Prop where
 seat: AtSupport false (purse b (boxA s 0)) (ball F s)
 cost: ∀ V,‖ball F s V‖≤ c

lemma Sits.reflect {s:Sweep N}{b c}
    (h:Bide.plainP F)(e:Sits F s b c)(i w):
    Sits F (flipL i w*s) b c:=by
 constructor
 · unfold ball; rw [posed _ _ _ h]
   refine (e.seat.refl i w).mono ?_
   rintro x p
   obtain ⟨y,g,rfl⟩:=mem_image.mp p
   obtain ⟨x,k,t⟩:=halo_spec.mp g
   rw [mem_singleton.mp k] at t
   refine halo_spec.mpr ⟨_,mem_singleton_self _,?_⟩
   rwa [push_box,←fl_box,sitT]
 unfold ball;rw [posed _ _ _ h]
 exact reflBound c (P:=ball F s) e.cost i w
open Swell
abbrev up(t:ℕ):Sweep N:=taxiPlus (wrap N (noon (t/2)))
abbrev down(t:ℕ):Sweep N:=flipL pole 0 * up t


open CF.Pannier.Chancel StepIn Garter
variable {b t:ℕ}{c:ℝ}
lemma upfly (g:t%2=0): boxA (up t:Sweep N) 0=(matinee (More N) t).there:=by
 change (castX (up t)).anon N 0=_
 rw [stir_l,affine,Signed.act_zero,zero_add,matinee]
 change (assembly N).embed (wrap N (Lace.noon (t/2))) = _
 rw [Ratio.embed_wrap]
 change wrap _ (2 • Lace.noon (t/2)) = wrap _ (Lace.noon t)
 have u:2*((t/2:ℕ):ℤ)=t:=by omega
 congr 1
 rw [two_smul];unfold Lace.noon;rw [←add_smul,←two_mul,u]

lemma downfly(g:t%2=0):boxA (down t:Sweep N) 0=(soiree (More N) t).there:=by
 unfold down
 rw [push_box,upfly g,fl_box]
 change affine (Signed.mirror pole) _ (wrap (More N) (Lace.noon t)) = -_
 unfold Lace.noon affine
 ext i
 by_cases h:i=pole <;> simp [Signed.mirror,Signed.act,plane,step,wrap_here,h]


lemma origin(h:Bide.plainP F) (C: AtSupport false (purse b 0) (toMark F))(D:∀ V,‖F V‖≤c):Sits F 1 b c:=by
 have u:boxA (1:Sweep N) 0=0:=by
   change (castX _).anon N _=_
   rw [stir_l,affine,Signed.act_zero]
   rw [show (1:Sweep N).b=0 by rfl, zero_add]
   rw [←Ratio.root_embed, map_zero]
 have v:ball F 1=toMark F:=by unfold ball;rw [inv_one,Bide.move_e h]
 exact ⟨by rw [u,v];exact C, by rw [v];exact fun _=>D _⟩

lemma flown(h:Bide.plainP F) (C: AtSupport false (purse b 0) (toMark F))(D:∀ V,‖F V‖≤c)
    (t:ℕ):Sits F (up t) b c ∧ Sits F (down t) b c:=by
   have u:=((origin F h C D).reflect F h pole 0).reflect F h pole (t/2:ℕ)
   rw [mul_one,fl_prod] at u
   exact ⟨u,u.reflect F h pole 0⟩
variable (t b)
def mural(t b:ℕ): Fabric N:=⟨photo (ball F (up t)),duet b (showtime (More N) t),0,0⟩


variable {t b}
lemma fardel{v w:Seat N}(V:v∈baseball b (matinee _ t).there)
     (W:w∈baseball b (soiree _ t).there)
     (l:ℕ)(L:b+l<t)(R:4*t≤N.val):l<separation w v:=by
 by_contra! h
 have e:v∈baseball (b+l) (soiree _ t).there:=by
   obtain ⟨x,p,u⟩:=halo_spec.mp W
   exact halo_spec.mpr ⟨_,p,(separation_triangle _ _ _).trans (Nat.add_le_add u h)⟩
 obtain ⟨a,j,n,o⟩:=night _ V pole
 change v∈baseball (b+l) (-wrap (More N) _) at e
 rw [←map_neg] at e
 obtain ⟨u,g,d,z⟩:=night _ e pole
 simp [Lace.noon] at j n g d
 have c:= (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (z.trans o.symm)
 have p:=Int.le_of_dvd (show 0 < a-u by omega) c
 change ((N.val*2:ℕ):ℤ) ≤ _ at p
 omega


lemma crown{r:ℕ}{z:Site N}(head:separation 0 (node z)≤b)
 (g:t%2=0)(L:b+paddle r<t)(R:4*t≤N.val)
 (h:Bide.plainP F)(U:Sits F (up t) b c)(A:Sits F (down t) b c):
 Ample F z (c^2) r (mural F t b):=by
 have m: (mural F t b).x=ball F (down t)*ball F (up t):=
    congrArg (· * ball F (up t)) (posed pole 0 (up t) h).symm
 have low:purse b (boxA (up t:Sweep N) 0) = baseball b (matinee (More N) t).there:=by rw [upfly g]
 have hi:purse b (boxA (down t:Sweep N) 0)= baseball b (soiree (More N) t).there:=by rw [downfly g]
 have here(s:Sweep N):birthplace z s∈purse b (boxA s 0):=halo_spec.mpr ⟨_,mem_singleton_self _,(sitT s 0 _).trans_le head⟩
 have a:=here (up t); rw [low] at a
 have d:=here (down t);rw [hi] at d
 refine ⟨?_,?_,down t,up t,mem_union_right _ d,mem_union_left _ a,fardel a d _ L R,m⟩
 · rw [m]
   have y:=A.seat;rw [hi] at y;have v:=U.seat;rw [low] at v
   exact (y.mono subset_union_right).mulM (v.mono subset_union_left)


 intro V;rw [m,Pi.mul_apply,sq]
 exact (norm_mul_le ..).trans (mul_le_mul (A.cost _) (U.cost _) (norm_nonneg _) ((norm_nonneg _).trans (A.cost V)))

lemma patio{l w}(e:b+l≤t)(h:4*t≤w)(i:Axis): cows i (Lattice.halo l (mural F t b).S) w:=by
 obtain ⟨q,p⟩:= noon_cows (m:=b+l) (t:=t) (n:=N) w (by omega) i
 refine ⟨q,fun v g=> p _ (halo_spec.mpr ⟨v,?_,(separation_self _).le⟩)⟩
 obtain ⟨x,j,k⟩:=halo_spec.mp g
 have u(z:Seat N)(a:x∈baseball b z):v∈baseball (b+l) z:=by
   obtain ⟨y,q,r⟩:=halo_spec.mp a
   exact halo_spec.mpr ⟨_,q,(separation_triangle _ _ _).trans (Nat.add_le_add r k)⟩
 rcases mem_union.mp j with t'|t'
 · exact mem_union_left _ (u _ t')
 exact mem_union_right _ (u _ t')
end YM.CF.Merino.Mitre

