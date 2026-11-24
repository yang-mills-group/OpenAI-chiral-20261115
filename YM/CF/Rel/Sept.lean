import YM.CF.Rel.Crests
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
abbrev Salt(n:Side)(G:Gauge):= InputZ G n→ℂ
abbrev prism(m:ℕ)(f:SpaceX G n)(X:Salt n G):Prop:=crystal m (satX f) X
variable {f g : SpaceX G n}{X V:Salt n G}
abbrev stroll (k y:Site n)(f:SpaceX G n):SpaceX G n:= Sean k f y
abbrev courseC (k y:Site n)(X:Salt n G): Salt n G:= fun x=> pulseP k y*X (te x y)
@[simp] lemma zero_a(k y:Site n):stroll k y (G:=G) 0=0:=by ext1; simp [stroll,Sean]
@[simp] lemma stride_z(k y:Site n):courseC k y (G:=G) 0=0:=by ext1; simp [courseC]
lemma prism.add (h:prism m f X)(he:prism m g V):prism m (f+g) (X+V):=by intro p; apply (h p |>.add (he p)).congr; intro z; exact (smul_add ((z^m)⁻¹) ((satX f) (z • p)) ((satX g) (z • p))).symm
lemma prism.sub (h:prism m f X)(he:prism m g V):prism m (f-g) (X-V):=by intro p; apply (h p |>.sub (he p)).congr; intro z; exact (smul_sub ((z^m)⁻¹) ((satX f) (z • p)) ((satX g) (z • p))).symm
lemma prism.mul(c:ℂ)(h:prism m f X):prism m (c • f) (c • X):=by intro p; apply ((h p).const_smul c).congr; intro z; exact smul_comm c _ _
lemma prizeC(k y:Site n)(h:prism m f X):prism m (stroll k y f) (courseC k y X):=by
 intro p; apply ((prism.mul (pulseP k y) h) (te p y)).congr; intro z
 change _=(z^m)⁻¹ • (pulseP k y * f (Lattice.translate y _)); rw [←trn]; rfl
lemma prismZ:prism m (G:=G) (n:=n) 0 0:=fun _=>tendsto_const_nhds.congr fun i=> (smul_zero _).symm -- tune
lemma prism.sumZ {α:Type}(s:Finset α)(f:α→ SpaceX G n)(X:α→Salt n G)(h:∀ i∈s,prism m (f i) (X i)):prism m (∑ i∈s,f i) (∑ i∈s,X i):=by
 induction s using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; exact prismZ
 | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact prism.add (h i (by simp)) (ih (fun i hij=>h i (by simp [hij])))
lemma strollX(k y: Site n)(r l:ℕ)(h:CakeF f 0 r m σ A) (hp:separation 0 y+r ≤ l): CakeF (stroll k y f) 0 l m σ A:= by
 have ht:0+y=y:=zero_add y; have he:=((h.rotate y).pay (pulseP k y)).widen 0; rw [pulse_a,one_mul,ht] at he; exact he.under le_rfl hp le_rfl
structure Travel(k:Site n)(m j:ℕ)(s M:ℕ)(ε C:ℝ)(f:SpaceX G n): Prop where
 profit:∃ (P:Site n→SpaceX G n) (X:Site n→ℝ), (∀ i,0≤ X i)∧ (∑ i,X i)≤ C ∧ (∀ i,P i≠0→ separation 0 i ≤ M)∧
    (∀ i,CakeF (P i) 0 s m ε (X i) ∧ CakeF (stroll k i (P i)) 0 s m ε (X i) ∧ cFoot j (satX (P i))) ∧ f=∑ i,(stroll k i (P i)-P i)
variable {E B A₀: ℝ}{j s:ℕ}
open Jet
lemma prism_food (k:Site n)(x:Site n)(h: cFoot j (satX f))(he:ContDiffAt ℝ j (satX f) 0)(hs:ContDiffAt ℝ j (satX (stroll k x f)) 0): cFoot j (satX (stroll k x f)):= (asideF hs _ (prizeC k x ((argent he).mp h))).1
lemma hatZ: cFoot j (satX (n:=n) (G:=G) 0):=by intro i hi; change iteratedFDeriv ℝ i (fun _:InputZ G n=>(0:ℂ)) 0 = _; rw [iteratedFDeriv_fun_zero]; rfl
lemma Travel.stilt {k:Site n}(hp:r ≤ l)(ht:0 ≤ C):Travel k m j r l σ C (0:SpaceX G n):=⟨by refine ⟨0,0,fun i=>le_rfl,(by simpa),fun i h=>False.elim (h rfl),fun i=> ⟨CakeF.zeroP le_rfl,by rw [Pi.zero_apply,zero_a];exact CakeF.zeroP le_rfl,hatZ⟩,?_⟩; simp⟩
lemma scroll_p(k i:Site n):stroll k i (f+g)=stroll k i f+ stroll k i g:=by ext1; exact mul_add ..
lemma Travel.plus {k:Site n}(p:Travel k m j r l σ C f)(h:Travel k m j r l σ A g)(ht:0<σ)(hj:j ≤ m):Travel k m j r l σ (C+A) (f+g):=by
 obtain ⟨P,X,h1,h2,h3,hH,h4⟩:=p.profit; obtain ⟨Q,Y,j1,j2,j3,H,j4⟩:=h.profit; let L(i:Site n):= P i+Q i; refine ⟨L,X+Y,fun i=>add_nonneg (h1 i) (j1 i),?_,fun i hi=> ?_,fun i=>?_,?_⟩
 · simp only [Pi.add_apply,sum_add_distrib]; exact add_le_add h2 j2
 · by_cases he:P i=0
   · unfold L at hi; rw [he,zero_add] at hi; exact j3 i hi
   exact h3 i he
 · obtain ⟨h,h',hu⟩:=H i; obtain ⟨p,p',hv⟩:= hH i
   unfold L; rw [scroll_p]; have hp : ‖(0:InputZ G n)‖<σ:=by simpa using ht
   refine ⟨p.add h,p'.add h',fun l hl=>?_⟩
   rw [show satX (P i+Q i)=satX (P i)+satX (Q i) from rfl,iteratedFDeriv_add_apply ((p.ledger _ hp).smooth.of_le (by exact_mod_cast hl.le.trans hj)) ((h.ledger _ hp).smooth.of_le (by exact_mod_cast hl.le.trans hj)),hv _ hl,hu _ hl, add_zero]
 unfold L; simp_rw [scroll_p,h4,j4,sum_sub_distrib,sum_add_distrib]; abel
end YM.CF.Rel
