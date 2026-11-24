import Organdy.Scarab
import YM.CF.Ione.Mesh
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Tulip Lat Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive  Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU
variable (s:Sweep n)
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single n
local notation "Fz"=> FC (Dwell n)


abbrev whirlB (s:Sweep n):Bag n→+*Bag n where
 toFun V:=fun i=> exportQ s (V ((moldA s).symm i))
 map_one':=funext fun _=>map_one _
 map_zero':=funext fun _=>map_zero _
 map_mul' _ _:=funext fun _=>map_mul _ _ _
 map_add' _ _:=funext fun _=>map_add _ _ _

abbrev cirrhose (s:Sweep n):ℂ→ℂ:=cSignX (s.charge.xor (detX s.s))
lemma whirlV (z:ℂ) (X:Bag n):
    whirlB s (z • X)=cirrhose s z • whirlB s X:=
   funext fun _=>funext fun _=>Ione.G_lot ..
lemma priceZ (z:ℂ): ‖cirrhose s z‖=‖z‖:=by
 unfold cirrhose cSignX; split <;>simp

open Leaf
variable {A K:Support (More n)}
lemma whirlMask (V:Firing n):
    exportQ s (capR p A V)=capR p (actY s A) (exportQ s V):=by
 funext i
 let t:=p.threshold
 let W:=actY s A
 have d: yellA s⁻¹ i ∈ pingMask p A ↔ i∈pingMask p W:=by
   change pingS t _ (flashA s⁻¹ i.1) ↔ pingS t W i.1
   conv =>
      lhs
      arg 2
      rw [←tape_C s A]
   exact Salt.glowA ..
 change roll s ((pingMask p A).indicator _ _)= (pingMask p W).indicator _ i

 by_cases w:i∈pingMask p W
 · rw [Set.indicator_of_mem w,Set.indicator_of_mem (d.mpr w)];rfl
 rw [Set.indicator_of_notMem w,Set.indicator_of_notMem (mt d.mp w),map_zero]

variable {t:ℝ}
local notation "Z₄"=> uplift p.order
structure Glare (p:BudgetPoint)(q:ℕ)(A:Support (More n))(h:ℝ)(X:Bag n)(t a b:ℝ):Prop extends
   Barrage p q A h X t a b where
   also:∀ s:Sweep n,Barrage p q (actY s A) h (whirlB s X) t (uplift p.order * a) (uplift p.order * b)

namespace Glare
variable {V W:Bag n}
lemma plusR (u:Glare p q A h V t a b)(v:Glare p q A h W t c d):
    Glare p q A h (V+W) t (a+c) (b+d):=by
 refine ⟨u.toBarrage.plusR v.toBarrage,fun s=>?_⟩
 rw [map_add,mul_add,mul_add];exact (u.also s).plusR (v.also s)
lemma zeroR : Glare p q A h (0:Bag n) t 0 0:=⟨.zeroR,fun s=>by rw [map_zero,mul_zero];exact Barrage.zeroR⟩
lemma swell (u:Glare p q A h V t a b)(w:ℂ):
    Glare p q A h (w • V) t (‖w‖*a) (‖w‖*b):=by
 refine ⟨u.toBarrage.swell _,fun s=>?_⟩;rw [whirlV,mul_left_comm,mul_left_comm Z₄ ‖w‖,←priceZ s w];exact (u.also s).swell _

lemma bigR (u:Glare p q A h V t a b)(g:a≤c)(f:b≤ d):
    Glare p q A h V t c d:=
   ⟨u.toBarrage.bigR g f,fun s=>(u.also s).bigR
      (mul_le_mul_of_nonneg_left g (uplift_nn _)) (mul_le_mul_of_nonneg_left f (uplift_nn _))⟩
lemma fresh (u:Glare p q A h V t a b)(S)(g:S⊆A):
    Glare p q A h (fun i=>capR p S (V i)) t a b:=
   ⟨u.toBarrage.fresh S g,fun s=>by
      have f:whirlB s (fun i=>capR p S (V i))=fun i=> capR p (actY s S) (whirlB s V i):=funext fun _=>whirlMask s _
      rw [f];exact (u.also s).fresh _ (map_subset_map.mpr g)⟩

private lemma frag (H:Barrage p q K h V t a b)(S)(e:S⊆K):
    Barrage p q K h (fun i=>V i-capR p S (V i)) t (a+a) 0:=by
 obtain ⟨Q,J,w,Tu,hq,_⟩:= H.price
 let X:=V
 let P:=S
 let A: Bag n:=fun i=> X i-capR p P (X i)
     -- adapt Louvre
 have hx(i:Aura n)(p':¬K⊆ i.val): A i=0:=by
    unfold A X; rw [(Tu i p').1,capR,show (pingMask p P).indicator (0:Firing n)= (0:Firing n) from Set.indicator_zero .. , sub_self]

 refine ⟨Q+Q,0,fun i=>?_ ,fun i p'=>⟨hx i p',by rw [Pi.add_apply,(Tu i p').2.1,zero_add],rfl⟩,by rw [voyage_plus]; exact add_le_add hq hq,by simp [voyageB]⟩
 by_cases g:K ⊆ i.val; swap; · change Flight p q i h (A i) (Q i+Q i) 0; rw [hx i g,(Tu i g).2.1,zero_add]; exact Flight.zeroR
 apply Flight.laidR; · rw [sub_eq_add_neg]; exact (w i).tube.addR (((w i).tube.mask P (e.trans g)).negR)
 intro Y u Z v; have ht:Z∈pingMask p P:=(pingFix (e.trans (g.trans u)) v).mpr (by simp)
 change acts ((V i-capR p P (V i)) Z) _=_
 rw [Pi.sub_apply,capR,Set.indicator_of_mem ht,sub_self,act_zero]
lemma surplus (u:Glare p q A h V t a b)(S)(e:S⊆A):
    Glare p q A h (fun i=>V i-capR p S (V i)) t (a+a) 0:=
   ⟨frag u.toBarrage S e,fun s=>by
     have f:whirlB s (fun i=>V i-capR p S (V i))=
         fun i=>whirlB s V i-capR p (actY s S) (whirlB s V i):=by
       funext i
       change exportQ s (_-_)=_; rw [map_sub,whirlMask];rfl
     rw [f,mul_add,mul_zero];exact frag (u.also s) _ (map_subset_map.mpr e)⟩

lemma whole {ι: Type*}(S:Finset ι)(Y:ι→ Bag n)(v w:ι→ℝ)(u:∀ i∈S,Glare p q A h (Y i) t (v i) (w i)):
   Glare p q A h (∑ i∈ S,Y i) t (∑ i∈ S,v i) (∑ i∈ S,w i):=
  ⟨Barrage.whole _ _ _ _ fun i e=>(u i e).toBarrage, fun s=>by
    rw [map_sum,mul_sum,mul_sum]
    exact Barrage.whole _ _ _ _ fun i e=>(u i e).also s⟩

lemma single(X:Aura n)(F:Firing n)(u:Flight p q X h F a b)(f:∀ s:Sweep n,
    Flight p q (moldA s X) h (exportQ s F) (Z₄*a) (Z₄*b))
    (r:A⊆X.val):
    Glare p q A h (fun i=> if i=X then F else 0) t (a*Sour.tact t p.B X) (b*Sour.tact t p.B X):=by
 refine ⟨Barrage.single X F u r,fun s=>?_⟩
 have e:Sour.tact t p.B (moldA s X)=Sour.tact t p.B X:=by
    unfold Sour.tact widthK;rw [show (moldA s X).val=actY s X.val from rfl,glow_q]
 have g:whirlB s (fun i=> if i=X then F else 0)=(fun i=> if i=moldA s X then exportQ s F else 0):=by
    funext i;change exportQ s (if (moldA s).symm i=X then F else 0)=_
    simp only [Equiv.symm_apply_eq];split_ifs
    rfl;exact map_zero _

 rw [g,←e,←mul_assoc,←mul_assoc]
 exact Barrage.single _ _ (f s) (map_subset_map.mpr r)
end Glare

lemma turn0 (x:FC (Dwell n))(p:acts x (vacuum (Dwell n))=0):
    acts (roll s x) (vacuum (Dwell n))=0:=by
 let U:= hail_Q s
 let b:=s.charge.xor (detX s.s)
 have he:=congrArg (dove b) p
 rw [dove_acts,dove_base] at he
 have hx: dove b (0:Wave (Dwell n))=0:=by ext; cases b <;> simp [dove,cSignX]
 have h := Fock.swivel U (windX b x) (vacuum (Dwell n))
 change acts (twist U (windX b x)) (vacuum (Dwell n))=0
 rw [he,hx] at h
 have hv: acts U.val (vacuum (Dwell n))=vacuum (Dwell n):=quant_vac ..
 rw [hv,map_zero] at h; exact h.symm
end YM.CF.Organdy
