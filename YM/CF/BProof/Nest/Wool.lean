import YM.CF.BProof.Stave.Simplex
import YM.CF.BProof.Nerve.Circuit
/-! Interface and purchasing, used at two scales. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Nest
open Lattice Function Finset
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators Classical
variable {n:Side}{K:Type*}{C q s:ℕ}{r:ℝ}
structure Wool (n:Side)(q:ℕ) where
  hue : Site n→ Fin q
  wheel : Site n→Site n→ℝ
namespace Wool
open Nerve Carpet Note Regard Sleet -- note.nS
variable (a:Wool n q)
def group(x:Site n) : Support n:= Stave.supp (a.wheel x)
def both (x y:Site n):= a.group x ∪ a.group y
structure Rub (a:Wool n q)(s:ℕ)(r:ℝ) : Prop where
  deals(x): Stave.Sim (a.group x) (a.wheel x)
  mom(x) (i)(p:i∈ a.group x):separation x i≤ Halo*s
  distinct(x y:Site n)(d:separation x y≤1): Set.InjOn a.hue (a.both x y)
  mar(x y:Site n)(d:separation x y≤1): (a.both x y).card≤5
  decal(x y:Site n)(d:separation x y≤1)(i:Site n): |a.wheel x i-a.wheel y i| ≤ r
abbrev rowz (n:Side)(q:ℕ) := Fin q × (Site n→ℝ)
def mark(x:Site n):rowz n q:= (a.hue x,a.wheel x)
def Equates (e:Equiv.Perm (Site n)) (a b:Wool n q):Prop:= (∀ i,a.hue i=b.hue (e i)) ∧ ∀ i j,a.wheel i j=b.wheel (e i) (e j)
variable {a}
@[simp] lemma group_in (x i:Site n): i∈ a.group x ↔ a.wheel x i ≠ 0:= Stave.mem_supp
lemma vani {x i:Site n}(p:i∉ a.group x):a.wheel x i=0:=not_not.mp ((group_in ..).not.1 p)
def structureC (s:ℕ)(U:Field n K Prop)(g:Field n K (Fin q))(w:K):Wool n q where
 hue:= g w
 wheel:= Pie.cent s q U (plain U g s) w
variable {U:Field n K Prop}{g:Field n K (Fin q)}(t:Note U g s r)
include t
lemma group_uses(w:K)(x:Site n):(structureC s U g w).group x=Pie.supporters U (plain U g s) s q w x:=by
 apply Finset.ext; intro i; rw [t.seam,group_in]; rfl -- underscore no param fails
lemma inducts(w:K): Rub (structureC s U g w) s r:=by
 let a':= structureC s U g w; refine ⟨fun x=>⟨(t.matrix w x).1,(Subset.refl _),(t.matrix w x).2⟩,fun x i hi=> ?_,fun x y d i hi j hj l=> ?_,fun x y d=>?_,fun x y d i=> t.mat_b w x y d i⟩
 · rw [group_uses t] at hi; exact (reg_in ..).1 (t.localMark w x i hi).2
 · change i∈ both _ x y at hi; change j∈ both _ x y at hj; unfold both at *; simp_rw [group_uses t] at hi hj
   have p(i:Site n)(u:i∈ Pie.supporters U (plain U g s) s q w x ∪ Pie.supporters U (plain U g s) s q w y) : U w i:=by -- tune
       rcases mem_union.mp (show i∈ Pie.supporters U (plain U g s) s q w x ∪ Pie.supporters U (plain U g s) s q w y from u) with g|g; exact (t.localMark _ _ _ g).1; exact (t.localMark _ _ _ g).1
   by_contra u; have hx:= t.close0 x y w d i j hi hj; exact t.flag w _ _ (p i hi) (p j hj) u (hx.trans (Nat.mul_le_mul_right _ (show 2*Halo≤King by decide) |>.trans' (le_of_eq (mul_assoc 2 Halo s).symm))) l -- maybe order eq had stuck
 · unfold both; rw [group_uses t,group_uses t]; exact t.union_card w _ _ d
lemma chargeD {r':Signed}{x:Site n}{E:Equiv.Perm K}(p:Transforms (facet r' x) (Policy.Joint U g) E)(w:K) : Equates (facet r' x) (structureC s U g (E w)) (structureC s U g w):= ⟨fun i=> congrArg Prod.snd (p w i), t.sent _ _ _ p w⟩ -- namespaces
lemma use_cost : Uses (Policy.Joint U g) (fun w=> mark (structureC s U g w)) (receipt s q):= by
 intro x y z h; exact Prod.ext (congrArg Prod.snd (Uses.self x y z h)) (t.price_μ x y z h)
end Wool
end YM.CF.BProof.Mesh.Nest
