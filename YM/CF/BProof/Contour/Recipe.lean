import YM.CF.BProof.Contour.Margin
import YM.CF.BProof.Contour.Yarn

/- complex integrated contour, only test total weight on compatible core families,
retain all overlaps of potentials. Visible functions may be extended Borel if required. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Contour
open Function Filter Moment RG MeasureTheory Finset Relation Push.AbsoluteSums
open scoped Topology BigOperators Classical ENNReal
variable {B I J: Type*}(X:B→Type*) [Fintype B][DecidableEq B][∀ i,MeasurableSpace (X i)]
structure Pot(X:B→Type*) [∀ i,MeasurableSpace (X i)] where
 μ : ∀ i, Measure (X i)
 ν : ∀ i, Measure (X i)
 [prob : ∀ i, IsProbabilityMeasure (μ i)]
 [fin : ∀ i,IsFiniteMeasure (ν i)]
attribute [instance] Pot.prob Pot.fin
variable {X}
variable [Fintype I][DecidableEq I][Fintype J][DecidableEq J][∀ i,Nonempty (X i)]
structure GeomT (B I:Type*) where
 S : I→ Finset B
 T : I→ Finset B
 sub (i:I) : S i⊆ T i
 pos (i:I) : (S i).Nonempty
variable {K:GeomT B I}
def see (K: GeomT B I)(T:Finset B)(Q:Finset I):= Q.filter fun q=> ¬ Disjoint (K.T q) T
def comfort (K:GeomT B I)(T:Finset B)(Q:Finset I):= T ∪ hull K.T (see K T Q)
structure Course (D:Pot X)(K:GeomT B I) where
 G : I→ (∀ i,X i)→ℂ
 bound (i:I): Envelope (G i)
 obey (i:I) : reads X (G i) (K.T i)
structure Spice (X:B→Type*) [∀ i,MeasurableSpace (X i)] (K:GeomT B I) (J:Type*) where
 t:J→Finset B
 pos(j:J) : (t j).Nonempty
 A:J→ Finset I→ (∀ i,X i)→ ℂ
 w : J→ℝ
 scope (j:J)(Q Q':Finset I)(h:flock K.T Q)(p:flock K.T Q')(g:see K (t j) Q=see K (t j) Q') : A j Q=A j Q'
 debt (j:J)(Q:Finset I)(p:flock K.T Q) : reads X (A j Q) (comfort K (t j) Q)
 bill(j:J)(Q:Finset I)(p:flock K.T Q): Measurable (A j Q)
 pay(j:J)(Q:Finset I)(p:flock K.T Q)(x:∀ i,X i): ‖A j Q x‖≤ w j
variable (P:Pot X) (C:Course P K)(R:Spice X K J)
abbrev food(K:GeomT B I)(Q:Finset I):= πμ X P.μ P.ν (hull K.S Q) -- K undeclared auto?
def eye(Q:Finset I)(x:∀ i,X i):=∏ i∈ Q,C.G i x
def tunic(Q:Finset I)(x:∀ i,X i):= eye P C Q x * Complex.exp (∑ j,R.A j Q x) -- P used?
def contour : ℂ:=∑ Q:Finset I with flock K.T Q,∫ x,tunic P C R Q x ∂food P K Q
def vision : I⊕J→ Finset B:= Sum.elim K.T R.t
def ease(P':Finset I)(j:J)(x:∀ i,X i):=Complex.exp (R.A j P' x)-1
def focus(Q:Finset I)(U:Finset J)(x:∀ i,X i):= eye P C Q x * ∏ j∈ U,ease R Q j x
def work(Q:Finset I)(U:Finset J):=if flock K.T Q then ∫ x,focus P C R Q U x ∂food P K Q else 0 -- need K inference from C?
def dish (v:Finset (I⊕ J)):= work P C R v.toLeft v.toRight
-- geometry helpers
lemma tissueLeft(a:Finset (I⊕J)): hull K.T a.toLeft ⊆ hull (vision R) a:= fun i t=>by obtain ⟨j,u,h⟩:= mem_biUnion.mp t; exact mem_biUnion.mpr ⟨_,mem_toLeft.mp u,h⟩
lemma tissueRight(a:Finset (I⊕J)): hull R.t a.toRight ⊆ hull (vision R) a:=fun i t=>by obtain ⟨j,u,h⟩:= mem_biUnion.mp t; exact mem_biUnion.mpr ⟨_,mem_toRight.mp u,h⟩
lemma hull_comfort(a:Finset (I⊕J))(j:J)(h:j∈a.toRight):comfort K (R.t j) a.toLeft ⊆ hull (vision R) a:=union_subset ((hull_sub R.t _ j h).trans (tissueRight R a)) ((hull_down K.T _ a.toLeft (filter_subset ..)).trans (tissueLeft R a))
lemma focus_read (a:Finset (I⊕J))(p:flock K.T a.toLeft): reads X (focus P C R a.toLeft a.toRight) (hull (vision R) a):=by
 apply reads_prod; exact fun x y v=> prod_congr rfl fun i l=> C.obey i x y (fun j e=>v j (tissueLeft R a (hull_sub K.T _ i l e)))
 exact fun x y v=> prod_congr rfl fun j h=> reads_comp X (R.A j a.toLeft) (fun u=>Complex.exp u-1) _ (R.debt j _ p) _ _ (fun i l=>v i (hull_comfort R a j h l))
lemma union_food(K: GeomT B I)(a b:Finset I):hull K.S (a∪ b)=hull K.S a ∪ hull K.S b:=Finset.union_biUnion ..
lemma hull_portions(a:Finset (I⊕J)): hull K.S a.toLeft⊆ hull (vision R) a:= (biUnion_mono (s:=a.toLeft) (fun i _=> K.sub i)).trans (tissueLeft R a)
lemma blind(K:GeomT B I)(T:Finset B)(P' Q:Finset I)(p:Disjoint T (hull K.T Q)): see K T (P'∪Q)=see K T P':=by
 ext i; simp only [see,mem_filter, Finset.mem_union]; refine and_congr_left (fun v=> or_iff_left (fun e=> v (Disjoint.mono_left (hull_sub _ _ _ e) p.symm))) -- tune iff ¬
private lemma split_focus(a b:Finset (I⊕ J))(p:Disjoint (hull (vision R) a) (hull (vision R) b))(h:Disjoint a b)(t:flock K.T (a∪ b).toLeft)(x:∀ i,X i): focus P C R (a∪ b).toLeft (a∪ b).toRight x=focus P C R a.toLeft a.toRight x*focus P C R b.toLeft b.toRight x:=by
 have ha:flock K.T a.toLeft:=flock_down K.T _ _ (toLeft_subset_toLeft subset_union_left) t; have hb:flock K.T b.toLeft:=flock_down K.T _ _ (toLeft_subset_toLeft subset_union_right) t; have hk: Disjoint a.toLeft b.toLeft:= disjoint_left.mpr fun _ l v=> disjoint_left.mp h (mem_toLeft.mp l) (mem_toLeft.mp v); have hh: Disjoint a.toRight b.toRight:= disjoint_left.mpr fun _ l v=> disjoint_left.mp h (mem_toRight.mp l) (mem_toRight.mp v)
 unfold focus eye; rw [toLeft_union] at t ⊢; rw [toRight_union,prod_union hk,prod_union hh]; let z(j):=ease R (a.toLeft ∪ b.toLeft) j x
 have hl:∏ j∈a.toRight,z j=∏ j∈a.toRight,ease R a.toLeft j x:=by apply prod_congr rfl; intro i g; unfold z ease; rw [R.scope i _ _ t ha (blind _ _ _ _ (Disjoint.mono ((hull_sub R.t _ i g).trans (tissueRight R a)) (tissueLeft R b) p))]
 have hz: ∏ j∈ b.toRight,z j=∏ j∈b.toRight, ease R b.toLeft j x := by
    apply prod_congr rfl; intro i g; unfold z ease; rw [R.scope i _ _ t hb]; rw [Finset.union_comm]; exact blind _ _ _ _ (Disjoint.mono ((hull_sub R.t _ i g).trans (tissueRight R b)) (tissueLeft R a) p.symm)
 rw [←hl,←hz]; unfold z; ring
lemma yarnD : Yarn (vision R) (dish P C R):=by
 refine ⟨?_,?_⟩
 · simp [dish,work,toLeft,toRight,focus,eye,food,hull,flock_zero]
 intro a b p h; unfold dish work; have hp : flock K.T (a∪ b).toLeft ↔ flock K.T a.toLeft∧ flock K.T b.toLeft:=by rw [toLeft_union]; exact flock_union K.T _ _ (Disjoint.mono (tissueLeft R a) (tissueLeft R b) p)
 split
 next H=>
   obtain ⟨u,v⟩:= hp.mp H; rw [if_pos u,if_pos v, funext (split_focus P C R a b p h H)]; unfold food; -- tune toLeft targeted in subscript before rewrites t?
   rw [toLeft_union,union_food]; exact portion X P.μ P.ν _ _ _ _ _ _ (hull_portions R _) (hull_portions R _) (focus_read _ _ _ _ u) (focus_read _ _ _ _ v) p
 next H=>
   by_cases g: flock K.T a.toLeft; · rw [if_neg (fun v:flock K.T b.toLeft=>H (hp.mpr ⟨g,v⟩)),mul_zero]
   rw [if_neg g,zero_mul]
end YM.CF.BProof.Contour
