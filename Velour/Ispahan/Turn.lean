import Velour.Arabesque.Circle
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

local notation "K"=>L.line_
variable (h:S.Fray L.Q L.Y)
lemma leap_bar(g:Lorentz)(f:Test4):bar (leap g f)=leap g (bar f):= by
 ext1 x
 simp
lemma parade_throng(q:E4)(g:Lorentz)(l:ℙ):
 parade (act g q) (throng g l)=throng g (parade q l):=by
  rw [parade,throng,throng,parade,List.map_map,List.map_map]
  congr 1
  ext1 x; refine Prod.ext rfl ?_
  change ahead _ (leap _ _)=leap _ (ahead _ _)
  ext1 y
  
  change leap _ _ (y-_)=leap _ _ y
  rw [leap_at,leap_at,map_sub,starts]
  rfl

lemma looking (h:S.Fray L.Q L.Y)(l:ℙ):
 ∃r:ℙ,(CompactW l→CompactW r)∧∀g,S.Faces (K (throng g l)) (K (throng g r)):=by
 induction l with
 | nil=>exact ⟨_, id,fun _ _ _=>rfl⟩
 | cons x l ih=>
    obtain ⟨j,e⟩:=h.2 x.1
    obtain ⟨r,u,v⟩:=ih
    refine ⟨r++[(j,bar x.2)],?_,fun g=>?_⟩
    · rintro t y a
      rcases List.mem_append.mp a with w|w
      · exact u (fun d i=>t d (List.mem_cons_of_mem _ i)) _ w
      rw [List.mem_singleton] at w; subst y
      exact barLocal (t x List.mem_cons_self)


    simp only [throng,List.map_append,List.map_cons,List.map_nil,line_append,line_cons]
    rw [show K []=1 from rfl,mul_one]
    have t: S.Faces (L.thread (launch g x)) (L.thread (launch g (j,bar x.2))):=by
       change S.Faces (Y x.1 (leap g x.2)) (Y j (leap g (bar x.2)))
       rw [←leap_bar]
       exact (h.1 _).mirror (h.1 _) e _
    exact t.mul (v g)


open YM.Damask

lemma trellis (h:L.Blithe)(l r:ℙ)(b:SpaceAxis)(g:Lorentz):
 ∃d,∀p:E4,∀a:ℝ,L.song (throng (scroll b a*g) (r++parade p l))=
     ∑ i,hoops d (Damask.raised d) (risen a) i *
          L.song (throng (scroll b (levy d i)*g) (r++parade p l)):=by
 let embed (v:τ→E4→Test4)(x:τ): κ × (E4→Test4):=(x.1,fun q=>leap g (v x q))
 let w:= (r.map (embed fun x _=>x.2)) ++ (l.map (embed fun x p=>ahead p x.2))
 let len:=w.length
 let point(p:E4)(x:κ × (E4→Test4)):τ:=(x.1,x.2 p)
 have z(p:E4): w.map (point p)=throng g (r++parade p l):=by
    simp only [w,List.map_append,throng,parade,List.map_map]
    rfl
 obtain ⟨t,e⟩:=frame w (show w.length=len from rfl)
 let nums:=fun i=>(t i).1
 let probes(p:E4):=fun i=>(t i).2 p


 obtain ⟨⟨A⟩,H',T,J,j,⟨B⟩⟩:=h.purchase b
 let d:=L.ringCost J nums
 refine ⟨d,fun p a=>?_⟩
 have hq(y): L.song (throng (scroll b y*g) (r++parade p l))=
    L.brim nums (af (scroll b y) (probes p)):=by
   rw [thrilling,← z]
   have v:=L.songleap ((point p) ∘ t) (scroll b y)
   simpa only [← List.map_map,e] using! v
 simp_rw [hq]
 exact L.rose_window b J A B nums (probes p) j (levy d) (Nat.cast_injective.comp Fin.val_injective) a

#print axioms trellis
#print axioms looking

