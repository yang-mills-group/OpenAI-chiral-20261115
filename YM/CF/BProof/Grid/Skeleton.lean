import YM.CF.BProof.Grid.Mesh

/-! Build entities with Borel decisions, finite stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Lattice Entity Function Set MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal Matrix.Norms.Frobenius BigOperators Classical
variable {n : ℕ} {c s : Side} (g : Ratio c s)

abbrev Settle (W : Set (Entity n c)) := ∀ p∈W,∀ q,q.Under p→ q∈W

variable {G : Gauge} {F : Type} [TopologicalSpace F]
namespace Fiber
variable [MeasurableSpace F][BorelSpace F][MetrizableSpace F][SecondCountableTopology F][CompactSpace F] [Nonempty F]
variable (X:Fiber n G F) (V : Set (Entity n c))

def pay : ℕ→ℝ
 | 0 => 1
 | n+1=> max (pay n) (X.toll (pay n)+1)
lemma pay_m : Monotone X.pay := monotone_nat_of_le_succ (fun i=> le_max_left ..)
lemma pay_p (n:ℕ) : 0<X.pay n:=lt_of_lt_of_le (show 0<X.pay 0 from one_pos) (X.pay_m n.zero_le)

def lay (z : ℕ)(A : Preg (n:=n) (s:=s) (G:=G) (F:=F)) (x : Cubic n s) := let p:= chief g x; if p∈ V ∨ p.dim≠z then A.2 x else X.fill g p (X.pay z/g.count.val) A x

def enter (A : Preg (n:=n) (s:=s) (G:=G) (F:=F)) : ℕ → Floor F n s
 | 0=> A.2
 | k+1=>lay g X V (k+1) (A.1,enter A k) -- tune param order recur

lemma fix_old (A : Preg (n:=n) (s:=s) (G:=G) (F:=F)) (k : ℕ)(x:Cubic n s)(h:chief g x∈V): X.enter g V A k x=A.2 x:= by induction k with|zero=>rfl|succ k ih=> rw [enter]; simp [lay,h,ih]

lemma fast_ext {p:Entity n c}{A B : Floor F n s}{U: Wire G n s}{d : ℝ}(h:EqOn A B {x|p.Mem g x})(hp:X.Fast g A U p d): X.Fast g B U p d:=fun x i hx l=> by unfold costW; rw [← h hx, ← h l]; exact hp x i hx l

private lemma steady (A : Preg (n:=n) (s:=s) (G:=G) (F:=F)) (k : ℕ) (p:Entity n c)(h:p.dim≤k)(hc:4≤c.val) : EqOn (X.enter g V A k) (X.enter g V A (k+1)) {x|p.Mem g x}:=by
 intro x hx; have he : (chief g x).dim ≤ k:= (Entity.chief_sub g p hc x hx).rank.trans h; rw [enter]; unfold lay; dsimp only; rw [if_pos (Or.inr (by omega))]

theorem stroll (A : Preg (n:=n) (s:=s) (G:=G) (F:=F)) (W : Set (Entity n c))(hc:4≤c.val)
    (u:Settle V)(h:Settle W)(t:∀ p∈V,X.Fast g A.2 A.1 p (1/g.count.val)) {m:ℝ} (hm:X.cap g.count m)
    (U:∀ p∈ W,okay g A.1 m p) (k:ℕ) : ∀ p ∈ W, p.dim≤k → X.Fast g (X.enter g V A k) A.1 p (X.pay k/g.count.val) := by
 induction k with
 | zero=> exact fun p _ vp=> X.zeroD g _ A.1 p hc (by omega) _
 | succ k ih=>
  intro p hp v; have hk:0<(g.count.val:ℝ):=by exact_mod_cast (show 0<g.count.val from g.count.property)
  rw [pay]
  rcases v.lt_or_eq with v|v
  · apply X.fast_ext g (X.steady g V A k p (by omega) hc); apply (ih p hp (by omega)).mono; gcongr; exact le_max_left ..
  by_cases hg:p∈V
  · apply X.fast_ext g (A:=A.2); intro x hx; exact (X.fix_old g V A _ x (u _ hg _ (Entity.chief_sub g p hc x hx))).symm
    apply (t p hg).mono; gcongr; exact (X.pay_m (show 0 ≤ k+1 from by omega)) -- tune
  let d := X.pay (k+1)/g.count.val; let B := X.enter g V A k; let T := X.fill g p d (A.1,B)
  have hB:X.Border g B A.1 p (X.pay k/g.count.val):=by intro i hh x; exact ih (p.wall i x) (h p hp _ (.wall hh x (.refl _))) (by have := p.wall_dim hh x; omega)
  have hy : X.Birth g p d A.1 B T:=by apply X.fill_p g p d (A.1,B) hc; obtain ⟨Z,H,Y⟩:= X.leads g p A.1 B (X.pay k) (X.pay_p _) hB hc hm (U p hp); exact ⟨Z,H.mono (div_le_div_of_nonneg_right (le_max_right ..) hk.le),Y⟩
  refine X.fast_ext g ?_ hy.1; intro x hx
  by_cases t:p.Proper g x
  · rw [enter]; simp only [lay,p.chosen g x t,hg,v,Ne,not_true_eq_false,or_self,↓reduceIte]; rfl -- using T
  obtain ⟨i,u,b,y⟩:=p.smaller g hc (show p.Mem g x from hx) t; rw [← steady g X V A k (p.wall i b) (by have := p.wall_dim u b; omega) hc y]; exact (hy.2 x ⟨i,u,b,y⟩).symm

lemma enter_c (k:ℕ) : Measurable (fun A=>X.enter g V A k):=by induction k with|zero=>exact measurable_snd|succ k ih=> refine measurable_pi_lambda _ fun i=>?_ ; unfold enter lay; dsimp only; split_ifs; exact (measurable_pi_apply i).comp ih; exact (measurable_pi_apply i).comp ((X.fill_m g _ _).comp (measurable_fst.prodMk ih))

/-- No dependence on the extent of the permitted region or undecided selections on other
entities. Locality on all data, including failed estimates. -/
lemma enter_eq {W : Set (Entity n c)} {A B : Preg (n:=n) (s:=s) (G:=G) (F:=F)} (p : Entity n c)(hc:4≤c.val) (h : ∀ q, Under q p → (q∈V ↔ q ∈W))(ht:Wire.Agrees G {x|p.Mem g x} A.1 B.1)(hl: EqOn A.2 B.2 {x|p.Mem g x}) (k:ℕ) : EqOn (X.enter g V A k) (X.enter g W B k) {x|p.Mem g x}:=by
 induction k with
 | zero=> exact hl
 | succ k ih=>
   intro x hx; have hu:=Entity.chief_sub g p hc x hx
   rw [enter,enter]; unfold lay; simp only [h _ hu]; split_ifs; exact ih hx
   simp only [fill,Function.comp_apply]; refine congrFun (congrArg (X.sally g _ _).choose ?_) x; apply cut_eq g (chief g x); rintro i ⟨hx,hy⟩; exact ht i ⟨hu.sites g hc hx,hu.sites g hc hy⟩; intro x hx; exact ih (hu.sites g hc hx)
end Fiber
end YM.CF.BProof.Grid
