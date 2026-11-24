import YM.CF.Gully.Ink
import YM.CF.Spire.Thick
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gully
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Maize Gloss Floe Ave Phase.Sample Jet Pastry Drapes Gas
variable {r e U K A H:ℝ}{n:ℕ}
variable {a v b c d:ℝ}
section
variable {j:ℕ}{o:Odd L.val} {T:Pricing j L o (Thread j)}{P:Grasp T B e}(X:Spire.Pearl P)(V:Stamped j L o T)(h:1≤j)(p: P.roundZ≤(CSide m B).val)(u:0<e)
include X V p u h
lemma wax_z(U:Briar m B e)(s:Era m):candle m B (P.cost m firstM) (shotV s U).val=payZ s (candle m B (P.cost m firstM) U.val):=by
 let f:=P.cost m firstM; let g:=U.val; obtain ⟨z,hz⟩:=cue_from (m:=m) U.val; let w:=shotV s U; let V':=w.val; have hv:Guard V' e:=w.property; let x:=starfish m B g z; let s':=netB m B s
 let y:=fireA s' x; let Z:=sumX m s z; have hy: y=starfish m B V' Z:=(Τs B s P.topB u.le U.val U.property (slot m z) {0} (stick 0) (stick_in _ (mem_singleton_self _)) hz).symm
 have hx:Slow g (Dial.hook x) X.q:=fun i p=>(starK X.ample u.le U.property hz i p).trans_le X.wide -- namespace tune
 have hh:ZeroF m B V' Z:= (voxel B s _ (U.val,z) ⟨U.property,hz⟩).2; have hi: Slow V' (Dial.hook y) X.q:=by rw [hy]; exact fun i k=> (starK X.ample u.le hv hh i k).trans_le X.wide
 have ht (v:Briar m B e)(k:Cue m)(hp:ZeroF m B v.val k): song m B f v.val (starfish m B v.val k)=Phase.accord m B (northZ m B) v.val k:=by
    apply integral_congr_ae; apply Eventually.of_forall; intro i; unfold herald lyre; by_cases t:law m B v.val i=0; · simp [t]
    unfold f; rw [Brace.price_s P.topB P.baseY (P.couture p firstM) v.val v.property i k (law_rich m B _ _ t) hp]
 have hA:song m B f V' y = payZ s (song m B f g x):=by rw [hy, ht w Z hh,show song _ _ _ g x=_ from ht U z hz]; exact owns_H B s X V h p u U.val U.property z hz
 unfold f at hA
 rw [show candle m B _ (shotV s U).val=_ from candleL X V p h V' hv firstM y hi,candleL X V p h U.val U.property firstM x hx, hA,show hum m B (P.cost m firstM) V' y=payZ s (hum m B f U.val x) from song_x m B f U.val x s', ←Gloss.θ_sub]; exact (show payZ s _=Spire.zen _ from (by simpa only [Complex.ofReal_zero,zero_add] using ley 0 (hum m B f U.val x-song m B f g x) (wageZ s))).symm
omit p
private lemma chalk_s {p:1≤H}{F:Briar m B e→ℂ}(g:Screen (soar m B e) (aether n U e m B) n F a v): HatX e H p U n (fun x=>hollow (F x)) a v:=by
 obtain ⟨T,w,h,u,V⟩:=g; refine ⟨fun i x=>hollow (T i x), w,fun i=>?_,u,fun x=>by dsimp only; rw [V,hollow_sum]⟩
 have u:=h i; refine ⟨⟨u.pos,u.travel,fun x=> Flour.grainE.smul _,fun k=>congrArg _ (u.reads _ _ k),fun x=>(hollow_cost ..).trans_le (u.sumline x),scalarC.comp u.cont,fun j x=>?_⟩,?_⟩
 · change routeM m B j _=_; dsimp only; rw [route_s,show T i ((PinK m B e H p).pick j x)=T i x from u.gauge x j]
 intro E _ _ _ f S t l x q; have hp:=u.plot E S t f l x q -- tune
 have hz:=zero_le_one.trans p
 let L:=Maize.bark (Hearth m B) H; change Allows _ (fun x=>L (T i (f x))) x (w i); rw [←one_mul (w i)]; refine Allows.linear (G:=Dough (Hearth m B)) L hp ?_; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; exact mintB hz (Hearth m B)
lemma wax_m(n:ℕ)(q:1≤U):∃ a C:ℝ,0<a ∧0≤C∧∀ (m:Side),P.roundZ ≤ (CSide m B).val→∀ (H:ℝ)(p:1≤H),HatX e H p U n (fun x:Briar m B e=>hollow (candle m B (P.cost m firstM) x.val)) a C:=by
 obtain ⟨a,c,t,Y,Z⟩:=cycle X V u h n U q; refine ⟨_,_,t,Y,fun m g H p=>?_⟩; exact chalk_s X V h u (Z m g firstM) -- incl inherited vars
end
variable {F G:Briar m B e→ Ewe m B}{p:1 ≤ H}
lemma purse(h:HatX e H p U n F a v)(t:a≥b)(g:v ≤c):HatX e H p U n F b c:=by
 obtain ⟨T,w,h,l,x⟩:=h; refine ⟨T,w,h,fun i=>le_trans ?_ ((l i).trans g),x⟩; exact sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (rent_up t i) (h i).home.price)
lemma unite_L(h:HatX e H p U n F a v)(g:HatX e H p U n G a c): HatX e H p U n (fun i=> F i+G i) a (v+c):=by
 obtain ⟨T,w,h,X,Z⟩:= h; obtain ⟨T',w',h',y,t⟩:=g; refine ⟨fun i x=> T i x+ T' i x, w+w',fun i=>⟨(h i).home.plusT (h' i).home,?_⟩,fun i=>?_,fun i=>by dsimp only; rw [Z,t,sum_add_distrib]⟩
 · intro E _ _ _ f S p q x hx; simp_rw [map_add]; exact ((h i).actsJ E f S p q x hx).add ((h' i).actsJ E f S p q x hx)
 unfold hitE; simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add (X i) (y i)
lemma scale_L(h:HatX e H p U n F a v)(c:ℝ):HatX e H p U n (fun i=> c • F i) a (‖c‖*v):=by
 obtain ⟨T,w,h,g,t⟩:=h; refine ⟨fun i x=>c • T i x,fun i=> ‖c‖* w i,fun i=> ⟨(h i).home.payT _,?_⟩,fun i=>?_,fun i=>by dsimp only; rw [t,smul_sum]⟩
 · intro E _ _ _ f S p q x hx; simp_rw [map_smul]; exact ((h i).actsJ E f S p q x hx).smul _
 unfold hitE; simp_rw [mul_left_comm (rent ..), ←mul_sum]; exact mul_le_mul_of_nonneg_left (g i) (norm_nonneg _)
end YM.CF.Gully
