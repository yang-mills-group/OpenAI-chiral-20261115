import Velour.Arabesque.Borders
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} (S:Semigroup H timeAxis)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

variable {S}
variable {κ:Type}(L:S.Livery κ)
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

open Mink Mink.Lorentz YM.Motifs

local notation "𝒜"=>Module.End ℂ (D)

lemma airs (N:Set Test4){W:Module.End ℂ S.muslin}(t:W∈S.grove Y N):
 ∀P:𝒜→Prop,
  (∀x y,P x → P y → P (x+y)) →
  (∀(x :𝒜)(c:ℂ),P x → P (c • x)) →
  (∀l:ℙ,(∀x∈l,x.2∈N)→P (L.line_ l)) →
  P W:=by
 refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ t
 · rintro _ ⟨i,f,q,rfl⟩ P _ _ e
   have v:=e [(i,f)] (fun _ w=>(List.mem_singleton.mp w).symm ▸ q)
   simpa [line_,thread] using v
 · intro c P _ k e
   rw [Algebra.algebraMap_eq_smul_one]
   exact k _ _ (e [] (by simp))
 · exact fun _ _ _ _ i j _ a b y =>a _ _ (i _ a b y) (j _ a b y)
 intro A B _ _ i j P a b y
 refine i (fun x=>P (x*B)) ?_ ?_ ?_
 · intro x z t u; rw [add_mul]; exact a _ _ t u
 · intro x c t; rw [smul_mul_assoc]; exact b _ _ t
 intro m e
 refine j (fun x=>P (L.line_ m*x)) ?_ ?_ ?_
 · intro x z t u; rw [mul_add]; exact a _ _ t u
 · intro x c t; rw [mul_smul_comm]; exact b _ _ t
 intro n r
 rw [←L.line_append]

 exact y _ (fun v u=>(List.mem_append.mp u).elim (e v) (r v))

local notation "𝓞"=>({f:Test4 | LocalTest f})
local notation "C"=>S.grove Y 𝓞
local notation "K"=>S.nursery Y Ω

lemma seedlings {P:S.muslin→Prop}
  (a:∀x y, P x→P y→P (x+y))
  (b:∀x,P x→∀c:ℂ,P (c • x))
  (q:∀r:ℙ,CompactW r→P (L.gem r))
  (x:S.muslin)(e:x∈S.sprout L.Y L.Ω):P x:=by
    obtain ⟨A,i,rfl⟩:=e
    exact L.airs 𝓞 i (fun X=>P (X Ω))
      (fun _ _ => a _ _) (fun _ c p=>b _ p _) q

lemma barLocal: MapsTo ⇑bar 𝓞 𝓞:=by
 intro f p
 have t:tsupport (bar f)⊆tsupport f:=pocket_over (O:=tsupport f) (show f ∈ placement (tsupport f) from Set.Subset.refl _)
 exact (show IsCompact (tsupport f) from p).of_isClosed_subset (isClosed_tsupport _) t

def Sublimate (X:Module.End ℂ S.muslin): Prop:=
 ∀r s:ℙ,CompactW r→CompactW s→ inner ℂ L.Ω.val (L.line_ r (X (L.gem s))).val=0

lemma first_wick {X:𝒜}(h:S.Fray L.Q L.Y)(p:L.Sublimate X)
 (x y:D)(i:x∈S.sprout Y Ω)(j:y∈S.sprout Y Ω):
 inner ℂ y.val (X x).val=0:= by

 obtain ⟨A,t,rfl⟩:=j
 obtain ⟨W,e,s⟩:= h.faces barLocal t
 rw [s]
 refine L.airs 𝓞 e
    (fun B=>inner ℂ L.Ω.val (B (X x)).val=0) ?_ ?_ ?_
 · intro v w z j
   rw [show (v+w) (X x)=v (X x)+w (X x) from rfl,Submodule.coe_add,inner_add_right,z,j,add_zero]
 · intro v a z
   rw [show (a • v) (X x)=a • v (X x) from rfl,Submodule.coe_smul_of_tower,inner_smul_right,z,mul_zero]
 intro r j
 refine L.seedlings 
   (P:=fun x=>inner ℂ L.Ω.val (L.line_ r (X x)).val=0)
   ?_ ?_ (fun _ t=> p _ _ j t) _ i
 · intro u v g k; rw [map_add,map_add,Submodule.coe_add,inner_add_right,g,k,add_zero]
 intro u g a; rw [map_smul,map_smul,Submodule.coe_smul_of_tower,inner_smul_right,g,mul_zero]

variable {L} in
lemma Sublimate.burn {X:𝒜}
 (p:L.Sublimate X)(h:S.Fray L.Q L.Y)(t:S.Firm X)(w:∀x:D,x.val∈K→(X x).val∈K)
 (v:D)(m:v.val∈K): X v=0:=by
    have c:=h.wiggle L.vacU
    obtain ⟨x,y,r⟩:= c.core m
    obtain ⟨z,k,s⟩:= c.core (w v m)
    apply Subtype.ext
    apply @inner_self_eq_zero ℂ H.space _ _ _ _|>.mp
    exact tendsto_nhds_unique (s.plain.inner (firm_ruffs t r).plain)
         (tendsto_const_nhds.congr fun i=>(L.first_wick h p _ _ (y i) (k i)).symm)


def Partner (X A:Module.End ℂ S.muslin):Prop:=∀v:S.muslin,v.val∈K → X (A v) = A (X v)

lemma staysClear(h:S.Fray L.Q L.Y)(E:Set Test4){X:𝒜}(p:X∈S.grove Y E):
  ∀v:D,v.val∈K→(X v).val∈K:=grove_keep (fun i=>(h.pruned_keep L.vacU i).1) p

theorem nearField(h:L.Blithe)(i j:κ)(f g:Test4)(p:Spaced f g):L.Partner (Y i f) (Y j g):=by
  let X:=Y i f*Y j g-Y j g*Y i f
  have t:X∈S.grove Y Set.univ:= sub_mem
      (mul_mem (grove_seed i trivial) (grove_seed j trivial))
      (mul_mem (grove_seed j trivial) (grove_seed i trivial))
  have c:L.Sublimate X:=by
     intro r s d e
     change inner ℂ _ (L.line_ r (Y i f (Y j g (L.gem s))- Y j g (Y i f (L.gem s)))).val=_
     rw [map_sub,Submodule.coe_sub,inner_sub_right]
     apply sub_eq_zero.mpr
     have y:=L.clearVoice h r s i j d e f g p
     simp only [vowel,song,gem,List.append_assoc,List.cons_append,List.nil_append,L.line_append,
          line_cons] at y
     exact y
  intro v e
  exact sub_eq_zero.mp (c.burn h.fray (h.fray.bound t) (L.staysClear h.fray _ t) _ e)
#print axioms nearField



lemma fromGrove(h:S.Fray L.Q L.Y)(E:Set Test4)(A:𝒜)
 (p:∀ i,∀f∈E,L.Partner (Y i f) A)
 {X:𝒜}(t:X∈S.grove Y E):L.Partner X A:=by
 refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ t
 · rintro _ ⟨i,f,j,rfl⟩; exact p _ _ j
 · intro c x _
   simp only [Module.algebraMap_end_apply,map_smul]
 · rintro x y _ _ a b u e
   change x (A u)+y (A u)=A (x u+y u)
   rw [map_add,a u e,b u e]
 intro x y _ t a b u e
 change x (y (A u))=A (x (y u))
 rw [b u e,a _ (L.staysClear h E t _ e)]

variable {L} in
lemma Partner.swap {X A:𝒜}(p:L.Partner X A):L.Partner A X:= fun _ i=>(p _ i).symm

theorem seamAllowance (h:L.Blithe)
 (E F:Set Test4)(d:∀f∈E,∀g∈F,Spaced f g)
 {X A:𝒜}(p:X∈S.grove Y E)(q:A∈S.grove Y F):
 L.Partner X A:=by
  exact L.fromGrove h.fray E _ (fun i f y=>
   (L.fromGrove h.fray F _ (fun j g t=> (L.nearField h i j f g (d _ y _ t)).swap) q).swap) p


theorem spacious (h:L.Blithe)(E F:Set E4)
 (d:∀x∈E,∀y∈F,y-x∈spacelike)
  {X A:𝒜}(p:X∈pocket L.Y E)(q:A∈pocket L.Y F): L.Partner X A :=
  L.seamAllowance h (placement E) (placement F)
    (fun _ y _ z _ i=>d _ (y i.1) _ (z i.2)) p q
#print axioms spacious

