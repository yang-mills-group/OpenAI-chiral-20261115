import YM.CF.BProof.Grid.System

/-! Uniform purchases for single cubical entities. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Lattice Set MeasureTheory Filter Metric Function Finset Entity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical

variable {n : ℕ} {G : Gauge} {F : Type} [TopologicalSpace F]

structure Fiber (n : ℕ) (G : Gauge) (F : Type) [TopologicalSpace F] where
  cost : F→ F→ℝ
  symm (x y) : cost x y=cost y x
  self (x) : cost x x=0
  triangle (x y z) : cost x z ≤ cost x y+cost y z
  C : ℝ
  C_one : 1≤ C
  diameter (x y): cost x y ≤ C
  move : G.El → F→F -- U transports field at head to tail
  unit (x) : move 1 x=x
  mul (u v x): move (u*v) x=move u (move v x)
  isom (u x y): cost (move u x) (move u y)=cost x y
  pace (u v x): cost (move u x) (move v x)≤ C*cd G u v
  cont_d : Continuous (uncurry cost)
  cont_a : Continuous (uncurry move)
  extend (K : ℝ)(p : 0<K) : ∃ L,0<L ∧ ∀ (S T : Set (Fin n→ℝ)) (f:(Fin n→ℝ)→ F),
    S⊆closedBall 0 1 → T⊆S → T.Nonempty → (∀ x∈T,∀ y∈T,cost (f x) (f y) ≤ K*Dist.dist x y) →
    ∃ g, EqOn f g T ∧ ∀ x∈S,∀ y∈S,cost (g x) (g y) ≤ L*Dist.dist x y

abbrev Floor (F : Type)(n : ℕ)(s : Side):= Cubic n s→F
variable {c s : Side} (g : Ratio c s)

namespace Fiber
variable (X : Fiber n G F) (V : Floor F n s)(U: Wire G n s)

lemma cancelMove (x) (v : G.El) : X.move v (X.move v⁻¹ x)=x := by rw [← X.mul,mul_inv_cancel,X.unit]
def costW (x:Cubic n s)(i:Fin n) := X.cost (V x) (X.move (U (x,i)) (V (slide x i)))
def Fast (p:Entity n c)(e:ℝ) := ∀ x i,p.Mem g x → p.Mem g (slide x i)→ X.costW V U x i ≤ e
lemma Fast.mono {p:Entity n c}{w v:ℝ} {X V U g}(h:@Fast n G F _ c s g X V U p w)(l:w≤v) : X.Fast g V U p v:=fun x i hx hv=> (h x i hx hv).trans l -- tune
lemma zeroD (p:Entity n c)(hc:4≤c.val)(hv:p.dim=0)(e:ℝ) : X.Fast g V U p e:=by
 intro x i h k; have he:= (p.stepMem g i hc h).1 k; rw [Entity.len, Finset.card_eq_zero.mp hv,if_neg (Finset.notMem_empty _)] at he; omega

def flat (p : Entity n c) := fun x=> X.move (p.paths G g U x) (V x)
lemma flat_cost (b:ℝ)(x:Cubic n s)(i:Fin n)(p:Entity n c)(h:p.Mem g x)(l:p.Mem g (slide x i))(hc:4≤c.val)(m:0≤b)(Φ:Wire.Flat G U {x|p.Mem g x} b):
    |X.cost (X.flat g V U p x) (X.flat g V U p (slide x i))-X.costW V U x i| ≤ X.C*(n*g.count.val*b) := by
 let y:=slide x i
 let a:=p.paths G g U x; let w:= U (x,i); let A:=V y; let d:= p.paths G g U y
 have hp: X.cost (X.move (a*w) A) (X.move d A) ≤ X.C*(n*g.count.val*b):= (X.pace ..).trans (mul_le_mul_of_nonneg_left (p.smooth G g U h l hc m Φ) (zero_le_one.trans X.C_one))
 have he: X.cost (X.move a (V x)) (X.move (a*w) A)=X.costW V U x i:=by rw [X.mul,X.isom]; rfl
 change |X.cost (X.move a _) (X.move d A)-_| ≤ _; rw [←he,abs_le]; constructor
 · have h:=X.triangle (X.move a (V x)) (X.move d A) (X.move (a*w) A); rw [X.symm (X.move d A) _] at h; linarith
 linarith [X.triangle (X.move a (V x)) (X.move (a*w) A) (X.move d A)]

-- a use on the sphere or SU will pin the constants after this assertion. require
-- one-step angular input condition even for large constant b (extra smallness after b).
def okay (U : Wire G n s)(m : ℝ) (p:Entity n c) := Wire.Flat G U {x|p.Mem g x} m
abbrev cap (X:Fiber n G F)(b : Side) (m:ℝ): Prop := 0≤m ∧ X.C*((n:ℝ)*b.val*m) ≤ 1/(b.val:ℝ)

def Border (p:Entity n c)(e:ℝ) := ∀ i∈p.axes, ∀ v:Bool, X.Fast g V U (p.wall i v) e
def Rim (p:Entity n c)(x:Cubic n s) := ∃ i∈p.axes,∃ v:Bool,(p.wall i v).Mem g x
-- apply in meter coordinates for the entity; pay `δ/k` per lattice step.
theorem around (p:Entity n c) {u:ℝ}(hv:0<u)(h: X.Border g V U p (u/(g.count.val:ℝ)))
    (hc:4≤c.val) {m:ℝ} (hm : X.cap g.count m)(Φ:okay g U m p) :
    let K:=1+max X.C (2*n*(u+1));
    ∀ x,Rim g p x→∀ y,Rim g p y→ X.cost (X.flat g V U p x) (X.flat g V U p y) ≤ K*Dist.dist (p.chart g x) (p.chart g y) := by
 intro K; let v:ℝ:=g.count.val; have hk:0<v:=by unfold v; exact_mod_cast (show 0<g.count.val from g.count.property)
 let F:=X.flat g V U p
 let L:=(u+1)/v; have hL:0<L:=by dsimp [L]; positivity
 have hu (i)(hi:i∈p.axes)(a:Bool)(x:Cubic n s)(hx:(p.wall i a).Mem g x)(y:Cubic n s)(hy:(p.wall i a).Mem g y): X.cost (F x) (F y) ≤ L*n*Grid.dist x y := by
    let q:=p.wall i a; have he(x) (u:q.Mem g x):= ((p.mem_wall g hc x hi a).mp u).1
    apply (q.bound_of_step g X.cost F X.self X.symm X.triangle (δ:=L) ?_ hc hx hy).trans (by rw [_root_.mul_assoc]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast steps_le x y) hL.le)
    intro x j hx hl; have hk:= abs_le.mp (X.flat_cost g V U m x j p (he _ hx) (he _ hl) hc hm.1 Φ); have ht:X.cost (F x) (F (slide x j))-X.costW V U x j ≤ 1/v:=hk.2.trans hm.2
    have ho:= h i hi a x j hx hl; change X.costW _ _ _ _ ≤ u/v at ho; unfold L; rw [add_div]; linarith
 rintro x ⟨i,hi,a,hx⟩ y ⟨j,hj,b,hy⟩
 rw [p.cost g hc ((p.mem_wall g hc _ hi a).mp hx).1 ((p.mem_wall g hc _ hj b).mp hy).1]
 have hP:max X.C (2*n*(u+1)) ≤ K:=le_add_of_nonneg_left (by norm_num)
 have hZ: X.C ≤ K := (le_max_left ..).trans hP; have he:0<K:=lt_of_lt_of_le one_pos (X.C_one.trans hZ)
 have H : 2*(L*(n:ℝ)) ≤ K/v := by unfold L; rw [show 2*((u+1)/v*n)=2*n*(u+1)/v by ring]; exact div_le_div_of_nonneg_right ((le_max_right ..).trans hP) hk.le
 change X.cost (F x) (F y) ≤ K*(_/v); rw [show K * ((dist x y:ℝ)/v)= K/v*(dist x y:ℝ) by ring]
 by_cases e:i=j
 · subst j; by_cases k:a=b
   · subst b; have h:=hu i hi a x hx y hy; apply h.trans; have hg:= Grid.dist x y; gcongr; have hw:0≤L*(n:ℝ):=by positivity
     linarith
   apply (X.diameter ..).trans; have hp: v≤ Grid.dist x y:= by
      dsimp only [v]; apply Nat.cast_le.mpr; cases a <;> cases b <;> try tauto
      · rw [Grid.dist_symm]; exact tall g p hc hi y x hy hx
      exact tall g p hc hi x y hx hy
   field_simp; nlinarith
 obtain ⟨z,x',y',p',q'⟩:= p.commonPoint g hc hi hj e _ _ hx hy
 have hh:=X.triangle (F x) (F z) (F y); rw [X.symm (F z) (F y)] at hh
 have Q (u v': Cubic n s)(h:Grid.dist u v'≤ Grid.dist x y) : L*n*Grid.dist u v' ≤ L*n*Grid.dist x y:=by gcongr
 apply hh.trans ((add_le_add ((hu i hi a x hx z x').trans (Q x z p')) ((hu j hj b y hy z y').trans (Q y z q'))).trans ?_); linarith [mul_le_mul_of_nonneg_right H (show 0≤(Grid.dist x y:ℝ) by positivity)]
end Fiber
end YM.CF.BProof.Grid
