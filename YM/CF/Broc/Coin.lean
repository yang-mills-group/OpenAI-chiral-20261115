import YM.CF.Paige.Vacate
/-! Local scalar collection. (Topological version for now). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Y Z D G: Type*} [Fintype Y][DecidableEq Y]
structure Light (Y D G : Type*) where
  frame : Branch.Field Y
  rel : Seal Y → D→ D→Prop
  expands (s t: Seal Y): s⊆t→∀ x y, rel t x y→ rel s x y
  dress : G→ D → D
variable [TopologicalSpace D]
variable {b:Light Y D G}
structure Peak (b: Light Y D G)(S: Seal Y)(F:D→ℂ)(w:ℝ):Prop where
 pos : 0≤w
 travel : w ≠0 → Grove b.frame S
 cont : Continuous F
 sumline x : ‖F x‖ ≤ w
 reads x y : b.rel S x y → F x=F y
 gauge x g : F (b.dress g x)=F x
structure Brunt (b: Light Y D G)(F: Seal Y → D→ℂ)(K:Seal Y →ℝ)(a C:ℝ):Prop where
 ordered(S):Peak b S (F S) (K S)
 pays(o): hitE a K o ≤ C
def Seat (b:Light Y D G)(F:D→ℂ)(a C: ℝ):Prop:=∃ M X,Brunt b M X a C ∧ ∀ x,F x=∑ i,M i x
variable {S: Seal Y}{F f:D→ℂ}{a c w u:ℝ}
namespace Peak
lemma emptyB :Peak b S (fun _=>0) 0:=⟨le_rfl,False.elim ∘ (· rfl),continuous_const,by simp,fun _ _ _=> rfl,fun _ _=>rfl⟩ -- tune
lemma tone(h:Peak b S F w)(p:Peak b S f u):Peak b S (fun x=> F x+f x) (w+u) := by
 refine ⟨add_nonneg h.pos p.pos,?_,h.cont.add p.cont,fun x=>(norm_add_le ..).trans (add_le_add (h.sumline x) (p.sumline x)),fun x y g=>congrArg₂ _ (h.reads x y g) (p.reads x y g),fun x y=> congrArg₂ _ (h.gauge x y) (p.gauge x y)⟩
 intro g; by_cases he:w=0; exact p.travel (by simpa [he] using g); exact h.travel he
lemma traceF(h:Peak b S F w)(H:ℂ→L[ℝ] ℂ)(x:ℝ)(p: ‖H‖≤x): Peak b S (H ∘ F) (x*w) :=by
 have he:0≤x:= (norm_nonneg H).trans p
 exact ⟨mul_nonneg he h.pos,fun g=>h.travel (right_ne_zero_of_mul g),H.continuous.comp h.cont,fun t=>(H.le_opNorm _).trans (mul_le_mul p (h.sumline _) (norm_nonneg _) he), fun x y g=>congrArg H (h.reads x y g),fun x y=>congrArg H (h.gauge x y)⟩
lemma collects {ι:Type*}[DecidableEq ι](s:Finset ι)(K:ι→D→ℂ)(k:ι→ℝ)(h:∀ i∈s,Peak b S (K i) (k i)):Peak b S (fun x=>∑ i∈s,K i x) (∑ i∈s,k i):=by
 induction s using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact emptyB
 | @insert a s ha ih=> simp only [sum_insert ha]; exact (h _ (by simp)).tone (ih (fun i hi=>h _ (by simp [hi])))
end Peak
namespace Seat
lemma gauge_t(h:Seat b F a c)(x g): F (b.dress g x)= F x:=by obtain ⟨M,K,h,hE⟩:=h; rw [hE,hE]; exact sum_congr rfl fun i _=> (h.ordered i).gauge ..
lemma continuous(h:Seat b F a c):Continuous F:=by obtain ⟨M,K,h,hE⟩:=h; rw [show F=fun x=>∑ i,M i x from funext hE]; exact continuous_finsetSum _ fun i _=>(h.ordered i).cont
lemma solid(h:Seat b F a c)(p:a≥w)(g:c ≤ u): Seat b F w u:=by
 obtain ⟨M,K,h,k⟩:=h; exact ⟨M,K,⟨h.ordered,fun o=>(Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_right (rent_up p _) (h.ordered i).pos)).trans ((h.pays o).trans g)⟩,k⟩
lemma adds(h:Seat b F a c)(p:Seat b f a w): Seat b (fun x=>F x+f x) a (c+w):=by
 obtain ⟨M,K,h,v⟩:=h; obtain ⟨P,V,p,f⟩:=p
 refine ⟨_,_,⟨fun i=>(h.ordered i).tone (p.ordered i),fun i=>?_⟩,fun x=> ?_⟩
 · simp only [hitE,mul_add,sum_add_distrib]; exact add_le_add (h.pays i) (p.pays i)
 dsimp only; rw [sum_add_distrib, v x, f x]
lemma frameH(h:Seat b F a c)(H:ℂ→L[ℝ] ℂ)(x:ℝ)(p:‖H‖≤x): Seat b (H ∘ F) a (x*c):=by
 obtain ⟨M,K,h,hB⟩:=h
 refine ⟨_,_,⟨fun i=>(h.ordered i).traceF H x p,fun i=>?_⟩,fun x=>?_⟩
 · unfold hitE; simp_rw [mul_left_comm _ x (K _),← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (h.pays i) ((norm_nonneg _).trans p)
 change H (F x)=_; rw [hB, map_sum]; rfl -- tune
end Seat
end YM.CF.Broc
