import YM.CF.Phase.Cove

/-! Marginal comparison for the subtracted exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Sample
open Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {f g : Tide m B→X} {e r s : ℝ}
lemma Cargo.less (h : Cargo f e r) (g : r≤s) : Cargo f e s := ⟨fun x b=>(h.normC x b).trans g,h.cont⟩
lemma Cargo.zero : Cargo (fun _:Tide m B=> (0:X)) e 0 := ⟨fun x _=> le_of_eq norm_zero,continuousOn_const⟩
lemma Cargo.add (h : Cargo f e r) (g' : Cargo g e s) : Cargo (fun x=>f x+g x) e (r+s) := ⟨fun x k=> (norm_add_le ..).trans (add_le_add (h.normC x k) (g'.normC x k)),h.cont.add g'.cont⟩
lemma Cargo.sub (h : Cargo f e r) (g' : Cargo g e s) : Cargo (fun x=>f x-g x) e (r+s) := ⟨fun x k=> (norm_sub_le ..).trans (add_le_add (h.normC x k) (g'.normC x k)),h.cont.sub g'.cont⟩
variable {t : Pack m B} (k : t∈payer m B e)
lemma Coastal_plus (k : t∈payer m B e) (h : Cargo f e r) (g' : Cargo g e s) : coastal m B (fun x=> f x+g x) t=coastal m B f t+coastal m B g t := by
  unfold coastal; rw [←integral_add (net_compact (h.flowerC t k)) (net_compact (g'.flowerC t k))]; apply integral_congr_ae; apply Eventually.of_forall; intro x
  by_cases H : cot m B (t,x)=0
  · simp [flower,H]
  have hx : (t,x)∈roster m B e := ⟨k,law_rich m B t.1 x H⟩
  unfold flower trip; dsimp only; rw [←smul_add, ←integral_add (net_compact (h.shadeC _ hx)) (net_compact (g'.shadeC _ hx))]; apply congrArg
  apply integral_congr_ae; apply Eventually.of_forall; intro y; simp only [shade,smul_add]
lemma Coastal_minus (m B : Side) (f : Tide m B→X) (t : Pack m B) : coastal m B (fun x=> -f x) t = -coastal m B f t := by simp [coastal,flower,trip,shade,integral_neg]
lemma Coastal_sub (k : t∈payer m B e) (h : Cargo f e r) (g' : Cargo g e s) : coastal m B (fun x=> f x-g x) t=coastal m B f t-coastal m B g t := by
  simp_rw [sub_eq_add_neg]; rw [←Coastal_minus]; apply Coastal_plus k h (show Cargo _ _ s from ⟨fun _ hx=>by rw [Pi.neg_apply,norm_neg]; exact g'.normC _ hx,g'.cont.neg⟩)
lemma Cargo.closeC (k : t∈payer m B e) (h : Cargo f e r) (g' : Cargo g e s) (d : ℝ) (H : ∀ x∈checked m B e, ‖f x-g x‖≤d) :
    ‖coastal m B f t-coastal m B g t‖≤d := by rw [←Coastal_sub k h g']; exact (show Cargo (fun x=>f x-g x) e d from ⟨H,(h.sub g').cont⟩).portC t k
lemma Cargo.collections {I : Type*} (F : Finset I) (x : I→ Tide m B→X) (w : I→ℝ) (h : ∀ i∈F,Cargo (x i) e (w i)) : Cargo (fun i=>∑ f∈F,x f i) e (∑ f∈F,w f) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [sum_empty]; exact Cargo.zero
  | @insert a f l ih => simp only [sum_insert l]; exact (h a (mem_insert_self ..)).add (ih (fun i hi=>h i (mem_insert_of_mem hi)))
lemma freighted {I : Type*} (t : Pack m B) (k : t∈payer m B e) (F : Finset I) (x : I→ Tide m B→X) (w : I→ℝ) (h : ∀ i∈F,Cargo (x i) e (w i)) :
    coastal m B (fun i=>∑ y∈F,x y i) t=∑ y∈F,coastal m B (x y) t := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [coastal,flower,trip,shade]
  | @insert a f l ih =>
    have hi i (p:i∈f) := h i (mem_insert_of_mem p); simp only [sum_insert l]; rw [Coastal_plus k (h a (mem_insert_self a f)) (Cargo.collections f x w hi), ih hi]

-- U and x-agreement local at every input path.
lemma voyage_eq (h : Cargo f e r) (u v : Pack m B) (k₁ : u∈payer m B e) (k₂ : v∈payer m B e) (S : Finset (Index m)) (d : Down m S)
    (q : ∀ a∈S, Agrees (room m B a) u.1 v.1) (w : AgreeF S u.2 v.2)
    (e₁ : ∀ x y z t:Cue m, AgreeF S x y→AgreeF S z t→Arch m B u.1 u.2 x z→ Arch m B v.1 v.2 y t→ f ((u,x),z)=f ((v,y),t)) :
    coastal m B f u=coastal m B f v := by
  change (∫ x, bet (rock m B u.1) (fun x=>trip m B f (u,x)) x ∂fares _ cloud)=∫ x, bet (rock m B v.1) (fun x=>trip m B f (v,x)) x ∂fares _ cloud
  apply banks_like (s:=S) (rock m B u.1) (rock m B v.1) (fun x=>trip m B f (u,x)) (fun x=>trip m B f (v,x)) d d ?_ ?_ (h.flowerC u k₁) (h.flowerC v k₂)
  · intro z; exact prod_congr rfl (fun i k=> water_limit u.1 v.1 i z z (fun _ _=>rfl) (q i k))
  intro x y l a b
  change trip m B f (u,x)=trip m B f (v,y)
  have he := law_rich m B u.1 x a; have hx := law_rich m B v.1 y b
  apply (banks_like (s:=S) (loft m B u.1 u.2 x) (loft m B v.1 v.2 y) (fun z=>f ((u,x),z)) (fun z=>f ((v,y),z)) d d ?_ ?_ (h.shadeC (u,x) ⟨k₁,he⟩) (h.shadeC (v,y) ⟨k₂,hx⟩)) -- tune apply
  · intro z; exact prod_congr rfl fun i e=> bid_limit i (q i e) (w.less (d i e)) (l.less (d i e)) (fun _ _=>rfl)
  intro z t A B' V; exact e₁ x y z t l A (bid_ready u.1 _ _ k₁.2 he B') (bid_ready v.1 _ _ k₂.2 hx V)
-- gauge invariance forms
lemma oriented (m B : Side) (U : Skin m B) (x y z : Cue m) (v : Site (Domain m B)→E) : bid m B (Lattice.gauge v U) (partner m B v x) (partner m B v y) (partner m B v z)=bid m B U x y z := by
  unfold bid; rw [show request m (partner m B v x) (partner m B v y)=(fun i=>onF v (request m x y i)) by funext i; unfold request; split <;> rfl]; exact remits ..
lemma Cargo.gauged (h : Cargo f e r) (k : Site (Domain m B)→E) (z : Pack m B) (g : z∈payer m B e) (H : ∀ x y, ((z,x),y)∈checked m B e →
    f (((Lattice.gauge k z.1,partner m B k z.2),partner m B k x),partner m B k y)=f ((z,x),y)) :
    coastal m B f (Lattice.gauge k z.1, partner m B k z.2)=coastal m B f z := by
  unfold coastal; rw [←rain_subst m B k]; apply integral_congr_ae; apply Eventually.of_forall; intro x
  unfold flower cot; dsimp only; rw [law_g]; by_cases hz : law m B z.1 x=0; simp [hz]
  apply congrArg (fun v:X=> law m B z.1 x • v); unfold trip; rw [←rain_subst m B k]; apply integral_congr_ae; apply Eventually.of_forall; intro y
  unfold shade lifted; dsimp only; rw [oriented]; by_cases he:bid m B z.1 z.2 x y=0; simp [he]
  have ht := law_rich m B z.1 x hz; rw [H x y ⟨⟨g,ht⟩,bid_ready z.1 z.2 x g.2 ht he⟩]
-- expectation of unweighted bill comparison
lemma returns (c : Part m B) (h : Room B e) (k : t∈payer m B e) (F : Tide m B→ℂ) (q : ∀ i∈checked m B e, F i=bill m B c i.1.1.1 i.1.2 i.1.1.2 i.2) :
    coastal m B F t=accord m B c t.1 t.2 := by
  unfold coastal accord; apply integral_congr_ae; apply Eventually.of_forall; intro x
  by_cases e' : law m B t.1 x=0
  · simp [flower,cot,lyre,e']
  have he := law_rich m B t.1 x e'
  have hx : trip m B F (t,x)=logs m B c t.1 x t.2 := by
    unfold trip
    have heq (y) : shade m B F (t,x) y=bid m B t.1 t.2 x y • logs m B c t.1 x t.2 := by
      unfold shade lifted; dsimp only; by_cases l:bid m B t.1 t.2 x y=0
      · simp [l]
      have hb:=bid_ready t.1 t.2 x k.2 he l
      have ht : F ((t,x),y)=bill m B c t.1 x t.2 y := q _ (show ((t,x),y)∈checked m B e from ⟨⟨k,he⟩,hb⟩)
      rw [ht, echoes c h (show Guard t.1 e from k.1) x t.2 y ⟨hb.2,hb.1⟩]
    simp_rw [heq]; rw [integral_smul_const,bid_norm t.1,one_smul]
  change flower m B F (t,x)=lyre m B c t.1 t.2 x; rw [flower, hx]; simp [lyre,cot,Complex.real_smul]
end YM.CF.Phase
