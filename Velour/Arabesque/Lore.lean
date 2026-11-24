import Velour.Arabesque.Motif
import Velour.Arabesque.District
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

structure Blithe :Prop where
 fray:S.Fray L.Q L.Y
 purchase(b:SpaceAxis): Nonempty (S.Tiles (royal b)) ∧
    ∃H':Hilbert,∃T:Semigroup H' b.castSucc,∃J:T.Livery κ,
    Pact L J∧Nonempty (T.Tiles (royal b).symm)
variable (h:L.Blithe)
abbrev leap(g:Lorentz)(f:Test4):=Joint.push (Poincare.motion g) f

def launch(g:Lorentz)(x:τ):τ:=(x.1,leap g x.2)
abbrev throng(g:Lorentz)(l:ℙ):ℙ:= l.map (launch g)

lemma leap_at (g:Lorentz)(f:Test4)(x:E4):leap g f x=f (act g⁻¹ x):=by
 rw [leap,Joint.push_at]
 suffices (Poincare.motion g)⁻¹=Poincare.motion (g⁻¹) by rw [this,Poincare.as_active]
 apply inv_eq_of_mul_eq_one_right
 rw [← Poincare.overL,mul_inv_cancel,Poincare.inactive]
lemma leap_comp(g k:Lorentz)(f:Test4): leap g (leap k f)=leap (g*k) f:=by
 ext1 x
 rw [leap_at,leap_at,leap_at,mul_inv_rev,act_mul]

lemma launch_comp (g k:Lorentz)(x:τ):launch g (launch k x) = launch (g*k) x:=by
 simp only [launch,leap_comp]
lemma launch_one (x:τ): launch 1 x=x:=by
 have e:leap 1 x.2=x.2:=by ext1 y; rw [leap_at,inv_one,act_one]
 exact Prod.ext rfl e

lemma LocalTest.leaps {f:Test4}(p:LocalTest f)(g:Lorentz):LocalTest (leap g f):=by
   have y: ⇑(leap g f)= f ∘ (g⁻¹).sends.toHomeomorph:= funext fun _=>leap_at ..
   unfold LocalTest; rw [y]
   exact p.comp_homeomorph _

lemma CompactW.launched {l:ℙ}(p:CompactW l)(g:Lorentz):CompactW (throng g l):=by
   intro x q; obtain ⟨y,u,rfl⟩:=List.mem_map.mp q
   exact LocalTest.leaps (p y u) _

lemma songleap(t:Fin n→τ)(g:Lorentz):
 L.song (throng g ((Each n).map t))=
 L.brim (fun i=>(t i).1) (af g (fun i=>(t i).2)):= by
 rw [throng,List.map_map,song_cast]; rfl

lemma thrilling(g k:Lorentz)(l:ℙ):
 throng (g*k) l=throng g (throng k l):=by
 simp_rw [throng,List.map_map,Function.comp_def,launch_comp]

theorem linens (h:L.Blithe)(l:ℙ):
 Pattern (fun g=> L.song (throng g l)):=by
 intro g b
 obtain ⟨⟨A⟩,H',T,J,p,⟨B⟩⟩:=h.purchase b
 obtain ⟨t,y⟩:=frame (throng g l) rfl
 let u:=fun i=>(t i).1; let f:=fun i=>(t i).2
 refine ⟨L.ringCost J u,?_⟩
 dsimp only
 simp_rw [thrilling]
 -- dep rw workaround n
 conv => rhs; ext a; rw [←y,L.songleap]
 exact L.grows b J A B u f p



lemma throng_1 (l:ℙ):throng 1 l=l:=by
 unfold throng
 rw [show launch (κ:=κ) 1=id from funext launch_one,List.map_id]

include h in
lemma fourfold (r s:ℙ)(u:CompactW r)(v:CompactW s)
 (x y:τ)(p:LocalTest x.2)(q:LocalTest y.2)
 (k:Lorentz)(j:k∈lobes)(b:SpaceAxis)(d:ℝ)(e:0<d)
 (z:∀ᶠ g in 𝓝 k,bandspace timeAxis b.castSucc d (leap g x.2) (leap g y.2)):
 L.song (r++[x,y]++s)=L.song (r++[y,x]++s):=by
  rw [←throng_1 (r++_++_), ←throng_1 (r++[y,x]++s)]
  refine enthroned (L.linens h _) (L.linens h _) _ j (z.mono fun g t=>?_)
  obtain ⟨⟨A⟩,G,C,J,a,⟨B⟩⟩:=h.purchase b
  simp only [throng,List.map_append,List.map_cons,List.map_nil]
  exact L.prelim J _ A B a h.fray (launch g x) (launch g y)
    (LocalTest.leaps p g) (LocalTest.leaps q g) d e t _ _
    (u.launched g) (v.launched g)

-- For fixed spectators, set-level property.
def Tiny (r s:ℙ)(E F:Set E4):Prop:=
 ∀x y:τ,LocalTest x.2→LocalTest y.2→tsupport x.2 ⊆ E→tsupport y.2 ⊆ F→
  L.song (r++[x,y]++s)=L.song (r++[y,x]++s)


include h in
theorem locale (r s:ℙ)(u:CompactW r)(v:CompactW s)(x y:E4)(t:(y-x)∈spacelike):
 ∃E∈𝓝 x,∃F∈𝓝 y, L.Tiny r s E F:=by
 obtain ⟨k,j,b,e⟩:=aside _ t
 let f:Lorentz × (E4×E4)→ℝ:=fun w=>frontD timeAxis b.castSucc (act w.1 w.2.1) (act w.1 w.2.2)
 have m: 0 < f (k,x,y):=by
    unfold f frontD; rw [map_sub] at e
    exact sub_pos.mpr e
 have c:Continuous f:=by unfold f frontD; fun_prop
 obtain ⟨d,a,l⟩:=exists_between m
 have i:∀ᶠ w in (𝓝 k) ×ˢ ((𝓝 x)×ˢ(𝓝 y)), d<f w:=
     (c.tendsto _).eventually (lt_mem_nhds l) |>.filter_mono
        (by rw [←nhds_prod_eq, ←nhds_prod_eq])
 obtain ⟨M,m,P,p,z⟩:=mem_prod_iff.mp i
 obtain ⟨E,R,F,T,g⟩:=mem_prod_iff.mp p
 refine ⟨E,R,F,T,fun x y c' e' X₀ Y₀=>L.fourfold h r s u v x y c' e' k j b d a ?_⟩

 filter_upwards [m] with k q i j p' q'
 rw [leap_at] at p' q'
 have t:d<f (k,act k⁻¹ i,act k⁻¹ j):=
   z (show _∈M×ˢP from
     ⟨q,g ⟨X₀ (subset_tsupport _ p'),Y₀ (subset_tsupport _ q')⟩⟩)
 dsimp only [f] at t
 rw [undoes,undoes] at t
 exact t.le
#print axioms locale
