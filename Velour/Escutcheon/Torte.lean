import Velour.Escutcheon.Flora
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


local notation "R"=> saucer S
local notation "E"=> S.E
local notation "P"=> Par S

/- Ops encoded in Livery supply higher Par energies. -/
lemma parc_glue (i j:ℕ)(l r:ℝ≥0)(p:0<l)(q:0<r):
 P i l*P j r=P (i+j) (l+r):=by
 have h:Commute (R^j) (P i l):=(gear S _ (dur.mpr p) i).pow_left j
 have v: Cache S (i+j) * (P i l * P j r)=Cache S (i+j) * P (i+j) (l+r):=by
    rw [P_Heq _ _ _ (add_pos p q),cacheA,mul_assoc,←mul_assoc _ (P i l),h.eq,
        mul_assoc,←mul_assoc, P_Heq _ _ _ p,P_Heq _ _ _ q]
    exact (S.time l r).symm
 ext1 x; exact cache_I S (i+j) (DFunLike.congr_fun v x)

/-- Replace X by charged Q with par arcs to both ends, paying m energy powers each. -/
lemma parc_sleeves {Q:ℝ≥0→H.Op}{i:ℕ}{G:H.Op}(hp:S.Prepaid Q i G)
 {l r:ℝ≥0}(p:0<l)(q:0<r):
 S.insulate Q l r=P i l*G*P i r:=by
 let d:= min l r
 have u:0<d:= lt_min p q


 have h: R^i * Q d * R^i = E d * G * E d:=by rw [← S.gauze_eq_saucer]; exact hp _ u
 set F:= S.insulate Q l r
 set B:= P i l*G*P i r
 have x:Cache S i * F * Cache S i= E l * G * E r:=by
    have hp(t r): E t * E r=E (t+r):=(S.time ..).symm
    have w(t):Commute (Cache S i) (E t):=(cupE S t).pow_left _
    change Cache S i * (E (l-d) * Q d * E (r-d)) * Cache S i=_
    calc
     _ = E (l-d)*(R^i * Q d * R^i)*E (r-d):=by
         simp only [mul_assoc]
         rw [←mul_assoc _ (E (l-d)) _, (w _).eq, ← (w (r-d)).eq]; simp only [mul_assoc] -- undo
     _ = _ :=by
        rw [h, ←mul_assoc,←mul_assoc,hp,
             tsub_add_cancel_of_le (show d≤l from min_le_left ..),
             mul_assoc _ (E d),hp,add_tsub_cancel_of_le (show d≤r from min_le_right ..)]
 have y:Cache S i * B * Cache S i= E l * G * E r:=by
    have u:P i r * Cache S i= E r:= (change_m S i _ (dur.mpr q)).trans (S.roots_heat q)
    rw [show B=P i l*G*P i r from rfl, ←mul_assoc,←mul_assoc,P_Heq _ _ _ p,mul_assoc _ _ (Cache ..),u]


 have z:F*Cache S i = B*Cache S i:=by
    ext1 s; apply cache_I S i
    change (Cache S i * (F*Cache S i)) _ = (Cache S i *(B*Cache S i)) _
    rw [←mul_assoc,x,←mul_assoc,y]
 apply S.equal_heat (d:=1)
 have h₁:E 1= Cache S i * P i 1:=(P_Heq S 1 i zero_lt_one).symm
 conv_lhs=>rhs;rw [h₁]
 conv_rhs=>rhs;rw [h₁]
 rw [mul_assoc _ F,←mul_assoc F,z]; simp only [mul_assoc]



variable {S}{κ:Type} (L:S.Livery κ){I:Type} (u:I→κ)(p:I→E4)
namespace Livery
local notation "Ω"=> L.Ω
local notation "Y"=> L.Y
local notation "F"=> L.G
local notation "v"=> L.m

local notation "x"=> fun i=>p i a
local notation "X"=> fun i=>coreSp S (p i) (F (u i))
local notation "V"=> fun i=>L.m (u i)

def domes (i j:I): H.Op := P ((V) i+(V) j) ((x) j - (x) i).toNNReal
def glade (J:List I) : ℂ:= inner ℂ (Ω).val (Film (X) (L.domes u p) J (Ω).val)
/-- E-compatibility across permutations. -/
lemma glade_shape {B:Type}(f:B→I)(J:List B): L.glade (u ∘ f) (p ∘ f) J=L.glade u p (J.map f):=by
 rw [glade,glade,Film_map];rfl

variable (l r:I→ℝ)
local notation "α"=> fun i=>((x) i-l i).toNNReal
local notation "β"=> fun i=>(r i-(x) i).toNNReal
def styled (i:I) := P ((V) i) ((α) i) * ((X) i) * P ((V) i) ((β) i)
local notation "B"=> L.styled u p l r


lemma quiet_caps (m:ℕ)(d:ℝ≥0)(h:0<d) : P m d (Ω).val=(Ω).val:=by
 apply cache_I S m
 rw [←mul_apply_eq_comp,P_Heq _ _ _ h,L.vacE,keepO _ _ (still S _ L.vacE)]

lemma dome_next (i j:I)(h: r i=l j)
 (y:(x) i<r i)(z:l j<(x) j):
 P ((V) i) ((β) i) * P ((V) j) ((α) j)=L.domes u p i j:=by
 have a:=sub_pos.mpr y
 have b:=sub_pos.mpr z
 rw [S.parc_glue _ _ _ _ (Real.toNNReal_pos.mpr a) (Real.toNNReal_pos.mpr b),domes,
      ← Real.toNNReal_add a.le b.le]
 dsimp only
 rw [h]; congr 2; ring
lemma style_table (i:I)(J:List I)
 (g:∀k∈i::J,l k<p k a ∧ p k a< r k)
 (h:∀k j s t,i::J=s++k::j::t → r k=l j):
   ((i::J).map B).prod (Ω).val=
     P ((V) i) ((α) i) (Film (X) (L.domes u p) (i::J) (Ω).val):=by
 induction J generalizing i with
 | nil=>
   have y:0<(β) i:=Real.toNNReal_pos.mpr (sub_pos.mpr (g i List.mem_cons_self).2)
   rw [solitary,List.map_singleton,List.prod_singleton,styled,mul_apply_eq_comp,L.quiet_caps _ _ y]
   rfl


 | cons j J ih=>
   have t:= ih j (fun k e=>g k (List.mem_cons_of_mem _ e)) fun k u₀ s t b=>h k u₀ (i::s) t (by rw [b];rfl)
   rw [List.map_cons,List.prod_cons,mul_apply_eq_comp,t,←mul_apply_eq_comp,
       styled,mul_assoc _ (P _ ((β) i)),
       L.dome_next u p l r i j (h i j [] J rfl)
          (g i List.mem_cons_self).2 (g j (List.mem_cons_of_mem _ List.mem_cons_self)).1]
   rfl

lemma glade_styled (J:List I)
 (g:∀k∈J,l k<p k a ∧ p k a< r k)
 (h:∀k j s t,J=s++k::j::t → r k=l j):
 inner ℂ (Ω).val ((J.map B).prod (Ω).val)= L.glade u p J:=by
 cases J with
 | nil=>rfl
 | cons i J=>
   have w:0<(α) i:= Real.toNNReal_pos.mpr (sub_pos.mpr (g i List.mem_cons_self).1)
   rw [L.style_table u p l r _ _ g h,←ContinuousLinearMap.adjoint_inner_left,
       show (P ((V) i) ((α) i)).adjoint=P ((V) i) ((α) i) from parRev _ _ _ w, L.quiet_caps _ _ w]
   rfl


lemma styled_q (i:I)(d:l i<p i a)(e:p i a<r i):
 B i=M S (SEP a (p i)).val * S.insulate (L.Q (u i)) ((α) i) ((β) i) * M S (-(SEP a (p i)).val):=by
 let m:=(V) i; let x₀:=(SEP a (p i)).val
 have y:0<(α) i:=Real.toNNReal_pos.mpr (sub_pos.mpr d)
 have z:0<(β) i:=Real.toNNReal_pos.mpr (sub_pos.mpr e)
 have r₁:Commute (P m ((α) i)) (M S x₀):=mslot S _ _ (dur.mpr y) _
 have r₂:Commute (P m ((β) i)) (M S (-x₀)):=mslot S _ _ (dur.mpr z) _
 rw [styled,S.parc_sleeves (L.prepaid _) y z]
 change P m ((α) i)*(M S x₀ * F (u i) * M S (-x₀))*P m ((β) i)=_
 conv_lhs=>lhs;rw [←mul_assoc,←mul_assoc,r₁.eq]
 simp only [mul_assoc]
 rw [r₂.eq]; try rfl
end Livery


variable {n:ℕ}
lemma Livery.whole_top (u:Fin n→κ)(p:Fin n→E4):
 L.glade u p (Each n)=TopG S L.Ω.val (L.G ∘ u) (L.m ∘ u) (points p):=rfl

variable {H':Hilbert} {b:Axis}{T:Semigroup H' b}
/-- Eu consistency, priced only on common strict cells. -/
def Pact (J:T.Livery κ):Prop:=
 ∀ {r:ℕ}(U:Fin r→κ)(p:Fin r→E4)(g h:Equiv.Perm (Fin r)),
   StrictMono (fun i=>p (g i) a)→StrictMono (fun i=>p (h i) b)→
   L.glade (U∘g) (p∘g) (Each r)=J.glade (U∘h) (p∘h) (Each r)

#print axioms Livery.glade_styled
