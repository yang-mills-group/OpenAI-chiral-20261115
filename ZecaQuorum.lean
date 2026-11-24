import YM.SU5.Cordial.Fountain
/-! # Explicit tangent gamma for our axial composite field. Compute powers before any spectral continuation. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}{j:ℕ}
open Twah

namespace Quorum
open Cordial
open Lead (Clan)
open YM.Stationary (Gaia)
variable {I:Type*} (u:I→Gaia)(D:I→DirSpin)
set_option quotPrecheck false
local notation "M" => (fun p:Cellz I=>u p.1)
local notation "ρ" => (germRho (fun p:Cellz I=>u p.1) D)
def lo(i:I)(c: Slot): Stamp I:= (i,c,true)
def hi(i:I)(c: Slot): Stamp I:= (i,c,false)
lemma side (x:I): billX M D x x=0:=by unfold billX; simp [Onyx.pencil]
-- include c binder? remove.
private lemma wick₂ {T : Type*}(d : T→T→ℂ)(p q r s : T) : runes d [p,q,r,s]= d p q*d r s-d p r*d q s+d p s*d q r:=by
  simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring

-- lists may repeat points
private lemma wick₃ {T : Type*}(d : T→T→ℂ)(p q r s t u : T) : runes d [p,q,r,s,t,u]=
    d p q*runes d [r,s,t,u]- d p r*runes d [q,s,t,u]+ d p s*runes d [q,r,t,u]- d p t*runes d [q,r,s,u]+d p u*runes d [q,r,s,t]:=by
  simp_rw [wick₂]
  simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring


lemma duo_pay (Z:I→Clan)(x y:I):
 Twah.witness Z [x,y] M D= if Z x=Z y then (dimf (Z x):ℂ) * ( - (billX M D x y*billX M D y x)) else 0:= by
 have h(c d:Slot):
   runes ρ (sayHi (sayHi [] x c) y d)= if c=d then -(billX M D x y*billX M D y x) else 0:=by
   change runes _ [lo x c,hi x c,lo y d,hi y d]=_
   rw [wick₂]
   simp only [lo,hi,funds,side,dcash,funds_neg,if_true,zero_mul,zero_sub]
   by_cases h:c=d<;>simp [h,Eq.comm]
 unfold witness; simp only [chore,h]
 split_ifs with p
 · simp [←p,colors_card]
 apply sum_eq_zero; intro c z; apply sum_eq_zero; intro d q
 refine if_neg ?_
 rintro rfl; exact p ((mem_filter.mp z).2.symm.trans (mem_filter.mp q).2)

theorem trio_pay (x y k : I)(Z:Clan):
 let a:=index Z (D x).1 (D x).2
 let b:=index Z (D y).1 (D y).2
 let e:=index Z (D k).1 (D k).2
 Twah.witness (fun _=>Z) [x,y,k] M D=(dimf Z:ℂ)*sixM (u x) (u y) (u k) a b e := by
 intro a b e
 let A:=billX M D
 let g:=A x y*A y k*A k x+A x k*A y x*A k y
 change _ = (dimf Z:ℂ) * g
 have h(c d f:Slot):
   runes ρ (sayHi (sayHi (sayHi [] x c) y d) k f)= if c=d ∧ d=f then g else 0:=by
   change runes _ [lo x c, hi x c,lo y d,hi y d,lo k f,hi k f] = _
   rw [wick₃]
   simp only [lo,hi, funds, funds_neg, dcash, side, if_true,sub_zero,zero_mul,zero_sub, wick₂]
   by_cases h:c=d <;> by_cases t:d=f
   · subst c; subst d; simp [g,A]; ring
   · subst c; simp [t,Ne.symm t]
   · subst f; simp [h,Ne.symm h]
   simp [h,t,Ne.symm h,Ne.symm t]
 unfold witness; simp only [chore,h]
 rw [←nsmul_eq_mul,← colors_card, ←sum_const]
 refine sum_congr rfl fun i k=>?_; rw [sum_eq_single_of_mem i k]; · simp [k];
 intro j _ h'; simp [Ne.symm h']

section
abbrev Quote (w:ℕ):Type:= (Fin w→Clan)→(Cellz (Fin w)→ Gaia)→ (Fin w→ DirSpin)→ℂ
def Identity (w:ℕ)(q:Quote w):Prop:=∀f d v,q f d v = Twah.witness f (Twah.letters w) d v
def axisTwo (t u:ℝ): Cellz (Fin 2)→Gaia:= fun z=>Window.corner (if z.1=0 then t else u)
def axisThree (t u w:ℝ): Cellz (Fin 3)→Gaia:= fun z=>Window.corner (![t,u,w] z.1)
def checkTwo (q:Quote 2)(t u:ℝ)(y z: Clan):= q (![y,z]) (axisTwo t u) 0
def checkThree (q:Quote 3)(t u w:ℝ)(z:Clan):=
 ∑ i : Fin 2, ∑ j :Fin 2, ∑ k :Fin 2,∑ l:Fin 2,∑ p:Fin 2,∑ a:Fin 2,
 (Window.alpha 0 i j*Window.alpha 1 k l*Window.alpha 2 p a)*q (fun _=>z) (axisThree t u w) ![(i,j),(k,l),(p,a)]

lemma reading_two (q:Quote 2)(h:Identity 2 q)(t₀ t₁:ℝ)(y z:Clan):
 checkTwo q t₀ t₁ y z=if y=z then (dimf y:ℂ)*(Window.kernel (t₁-t₀))^2 else 0:=by
 unfold checkTwo;rw [h]
 let a:Fin 2→Gaia:= fun i=> Window.corner (if i=0 then t₀ else t₁)
 change Twah.witness _ [0,1] (fun i=>a i.1) _ = _
 rw [duo_pay]; unfold billX
 change (if y=z then (dimf y:ℂ)* -(
    Onyx.pencil (Window.corner t₀-Window.corner t₁) (dnSpin 0) (upSpin 0) *
    Onyx.pencil (Window.corner t₁-Window.corner t₀) (dnSpin 0) (upSpin 0)) else 0)=_
 rw [Window.corner_sub,Window.corner_sub,pencil_time,pencil_time,if_pos rfl,if_pos rfl,
     show t₀-t₁=-(t₁-t₀) by ring,kernel_neg]; split <;> ring

lemma reading_three (q:Quote 3)(h:Identity 3 q)(t₀ t₁ t₂:ℝ)(y:Clan):
 checkThree q t₀ t₁ t₂ y= -(Window.signedCost y t₀ t₁ t₂:ℂ):=by
 let a:Fin 3→Gaia:=fun i=>Window.corner (![t₀,t₁,t₂] i)
 have he(i j k l p b:Fin 2):
    q (fun _=>y) (axisThree t₀ t₁ t₂) ![(i,j),(k,l),(p,b)]=
      (dimf y:ℂ)*Window.sixM (Window.corner t₀) (Window.corner t₁) (Window.corner t₂)
        (Window.index y i j) (Window.index y k l) (Window.index y p b):=by
    rw [h]
    exact trio_pay a (![(i,j),(k,l),(p,b)]) 0 1 2 y
 unfold checkThree; simp_rw [he]
 exact Window.left_price ..

structure GaugeTable (U:Quote 2)(V:Quote 3): Prop where
  two : ∀t u y z,checkTwo U t u y z=if y=z then (dimf y:ℂ)*(Window.kernel (u-t))^2 else 0
  alliance : ∀t u:ℝ,t<u→∀ y z,checkTwo U t u y z≠0 ↔ y=z
  three : ∀t u w y,checkThree V t u w y = -(Window.signedCost y t u w:ℂ)
  signed : ∀t u w:ℝ,t<u→u<w→∀ y,
      (checkThree V t u w y).re<0 ∧
         0 < (Window.dexPrice (Window.corner t) (Window.corner u)
                (Window.corner w) (dimf y:ℂ) 0 1 2).re

lemma table (U:Quote 2)(V:Quote 3)(h:Identity 2 U)(e: Identity 3 V) :
 GaugeTable U V:=by
 refine ⟨reading_two _ h,?_,reading_three _ e,?_⟩
 · intro t u p y z
   rw [reading_two _ h]
   split_ifs with a
   · exact ⟨fun _=>a,fun _=>mul_ne_zero (by exact_mod_cast (dimf_pos y).ne')
          (pow_ne_zero _ (fun h=>by have x:=kernel_pos (sub_pos.mpr p);rw [h] at x; exact lt_irrefl (0:ℝ) x)) ⟩
   simp [a]
 intro t u w a b y
 rw [reading_three _ e,Window.dexPrice_sign]
 simpa using cost_pos y a b
#print axioms table
end
