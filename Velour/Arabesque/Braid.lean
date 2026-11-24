import Velour.Arabesque.Foilwork
import Velour.Arabesque.Tendrils
import Mathlib.Data.List.Perm.Basic
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

variable {S}{H':Hilbert}{b:Axis}{T:Semigroup H' b}
variable {κ:Type}(L:S.Livery κ)(J:T.Livery κ)
   (h:a≠b)(A:S.Tiles h)(B:T.Tiles (Ne.symm h))
variable {n:ℕ}
local notation "ℓ"=> Fin n→ℝ
local notation "ℒ"=> Fin n→ℂ
local notation "σ"=> Equiv.Perm (Fin n)
variable (u:Fin n→κ)(X:Fin n→E4)
namespace Livery
local notation "D"=>S.muslin
local notation "Ω"=>L.Ω
local notation "Y"=>L.Y
local notation "U"=>S.liftL
local notation "τ"=>κ × Test4
local notation "ℙ"=>List (κ × Test4)


abbrev thread(x:τ):=Y x.1 x.2

def line_(l: ℙ):Module.End ℂ (D):=(l.map L.thread).prod
def gem(l:ℙ):S.muslin:=L.line_ l Ω
def song(l:ℙ):= inner ℂ L.Ω.val (L.gem l).val
local notation "K"=>L.line_

lemma line_cons (x:τ)(l:ℙ): K (x::l)=L.thread x*K l:=by
 unfold line_
 rw [List.map_cons,List.prod_cons]

lemma line_append (l n:ℙ): K (l++n)= K l*K n:=by
 unfold line_
 rw [List.map_append,List.prod_append]

lemma song_cast (t:Fin n→τ): L.song ((Each n).map t)=L.brim (fun i=>(t i).1) (fun i=>(t i).2):=by
 unfold song gem line_
 rw [List.map_map]
 rfl

def onFoot(p:E4)(x:τ):τ:=(x.1,ahead p x.2)
def parade(p:E4)(l:ℙ):ℙ:=l.map (onFoot p)


lemma parade_w(p:E4)(l:ℙ):
 K (parade p l)*U p=U p * K l:=by
 induction l with
 | nil=>
   change 1*_= _*1; rw [mul_one,one_mul]
 | cons x l ih =>
   rw [parade,List.map_cons,L.line_cons,L.line_cons, ← parade, mul_assoc, ← mul_assoc (U p), ih]
   rw [←mul_assoc, ←(show L.thread (onFoot p x)* U p=U p*L.thread x from
    (L.sewn _).translates _ _)]

lemma parade_vac(p:E4)(l:ℙ): L.gem (parade p l)= U p (L.gem l):=by
  have y:=congrArg (fun K':Module.End ℂ D=> K' Ω) (L.parade_w p l)
  simp only [Module.End.mul_apply,
    show U p Ω=Ω from Subtype.ext (L.vacU p)] at y
  exact y

-- Foot, Parade and local closure
def CompactW (l:ℙ):Prop:=∀x∈l,LocalTest x.2

lemma CompactW.parades {l:ℙ}(q:CompactW l)(p:E4):CompactW (parade p l):=by
 intro x r
 obtain ⟨y,t,rfl⟩:=List.mem_map.mp r
 exact LocalTest.ahead (q _ t) p


lemma parade_op(p:E4)(l:ℙ):K (parade p l)=U p*K l*U (-p):=by
 rw [← L.parade_w, mul_assoc, ← liftL_add,add_neg_cancel,liftL_zero, mul_one]

lemma line_in(l:ℙ){P:Set Test4}(q:∀x∈l,x.2∈P):K l ∈ S.grove Y P:=by
 induction l with
 | nil=>exact one_mem _
 | cons x l ih=>
   rw [line_cons]
   exact (S.grove Y P).mul_mem (grove_seed x.1 (q x List.mem_cons_self))
     (ih (fun _ i=>q _ (List.mem_cons_of_mem x i)))


lemma sparring(p:E4)(x y:S.muslin): inner ℂ (U p x).val (U p y).val=inner ℂ x.val y.val:=
    (LinearIsometry.inner_map_map
       (show H →ₗᵢ[ℂ] H from ⟨(S.unit.translation p).toLinearMap,S.unit.unitary p⟩) x.val y.val)

lemma song_move(p:E4)(l r:ℙ):
 L.song (parade p l ++ r)=L.song (l++parade (-p) r):=by
 rw [song, gem,line_append,parade_op]
 change inner ℂ L.Ω.val (U p (K l (U (-p) (L.gem r)))).val=_
 conv_rhs => rw [song,gem]
 rw [line_append,Module.End.mul_apply,← sparring p Ω (K l (K _ _)),show U p Ω=Ω from Subtype.ext (L.vacU p),
     ←parade_vac]
 rfl


/- Prefix priced. right-translation shifts. -/
include A in
lemma peel_right (t:S.Fray L.Q L.Y)(l r l' r':ℙ)
 (d:ℝ)(g:∀p:E4,|p a|≤1→d≤|p b|→
    L.song (l++parade p r)=L.song (l'++parade p r')):
 L.song (l++r)=L.song (l'++r'):=by
 let C:=chase (S:=S)
 have x(Ls Gs:ℙ):∃u:H, L.song (Ls++Gs)=C u (L.gem Gs).val 0 ∧
     ∀p:E4,L.song (Ls++parade p Gs)=C u (L.gem Gs).val p:=by
    obtain ⟨W,_,e⟩:=t.faces (P:=Set.univ) (fun _ _=> trivial)
       (L.line_in Ls (fun _ _=>trivial))
    have y(p:E4)(k:ℙ)(m:L.gem k=U p (L.gem Gs)):
      L.song (Ls++k)=C (W Ω).val (L.gem Gs).val p:=by
         rw [song,gem,line_append,Module.End.mul_apply]
         change inner ℂ _ (K _ (L.gem _)).val=_
         rw [m, ←e.symm]
         rfl
    exact ⟨_,y 0 Gs (by rw [liftL_zero]; rfl),fun p=>y _ _ (L.parade_vac _ _)⟩
 obtain ⟨u,i,q⟩:=x l r
 obtain ⟨v,j,s⟩:=x l' r'
 rw [i,j]
 exact plumeLift h A _ _ _ _ d (fun z hz e=>(q z).symm.trans ((g z hz e).trans (s z)))

include A in
lemma peel_left (t:S.Fray L.Q L.Y)(l r l' r':ℙ)
 (d:ℝ)(g:∀p:E4,|p a|≤1→d≤|p b|→
    L.song (parade p l++r)=L.song (parade p l'++r')):
 L.song (l++r)=L.song (l'++r'):=by
 apply L.peel_right h A t l r l' r' d
 intro p u v
 have y:=g (-p) (by simpa using u) (by simpa using v)
 simpa only [song_move,neg_neg] using y
#print axioms peel_left


lemma frame {α:Type*}(l:List α): ∀{n:ℕ},l.length=n→∃u:Fin n→α, (Each n).map u=l:=
 by rintro _ rfl; exact ⟨_, List.map_get_finRange l⟩

lemma cornice {α:Type*}(l:List α)(t:Fin n→α)(p:l.Perm ((Each n).map t)):
 ∃g:Equiv.Perm (Fin n), l=(Each n).map (t ∘ g):=by
  have h:Relation.Comp (fun y z => y=List.map t z) List.Perm l (Each n):=
     List.eq_map_comp_perm t ▸ p
  obtain ⟨m,i,r⟩:=h
  obtain ⟨u,q⟩:= frame m (n:=n)
     (r.length_eq.trans (List.length_finRange ..))
  subst m
  have e:Injective u:=List.nodup_ofFn.mp (by
     rw [List.ofFn_eq_map]
     exact r.symm.nodup (List.nodup_finRange n))
  let g:=Equiv.ofBijective u (Finite.injective_iff_bijective.mp e)
  exact ⟨g,i.trans (List.map_map ..)⟩
