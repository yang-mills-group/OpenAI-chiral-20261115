import YM.CF.BProof.Shore.Mark
/-! Authentic near minimizer. Use orientation and charge bits per link,
not relying on any of its uniqueness. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Function Metric MeasureTheory Finset Lattice Wilson Nest Stave Gallery Spire
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {I:Type*}[Fintype I]
-- inst.Borel Shore
local notation "G_"=>SU.group
private lemma roll_c : Continuous (Function.uncurry (@roll I)):=by
 apply continuous_matrix; intro i j; change Continuous (fun p:plate I × SU.E=> (p.1*SU.fund p.2) i j); simp only [Matrix.mul_apply]; have := SU.group.continuous_mat; have hm:Continuous SU.fund:=this; fun_prop
private lemma bank : ∃ f:plate I×plate I→ SU.E, Measurable f ∧∀ x:plate I×plate I,∀ g:SU.E,dist (roll x.1 (f x)) x.2≤ dist (roll x.1 g) x.2:=by
 letI : ProperSpace (plate I) := FiniteDimensional.proper ℂ _
 letI : SecondCountableTopology (plate I) := secondCountable_of_proper (α:=plate I)
 let S:= {p:(plate I × plate I) × SU.E|∀ g:SU.E,dist (roll p.1.1 p.2) p.1.2≤dist (roll p.1.1 g) p.1.2}; refine closed_choice S ?_ ?_
 · unfold S; rw [Set.setOf_forall]; apply isClosed_iInter; intro g; exact isClosed_le ((roll_c.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).dist (continuous_snd.comp continuous_fst)) ((roll_c.comp ((continuous_fst.comp continuous_fst).prodMk continuous_const)).dist (continuous_snd.comp continuous_fst))
 rintro ⟨a,b⟩; obtain ⟨v,_,h⟩:= isCompact_univ.exists_isMinOn Set.univ_nonempty (f:=fun g=>dist (roll a g) b) (((roll_c.comp (continuous_const (y:=a) |>.prodMk continuous_id)).dist continuous_const).continuousOn); exact ⟨v,fun t=>h (Set.mem_univ t)⟩ -- tune

def call(A B:plate I):= (bank (I:=I)).choose (A,B)
def lift_g (b:Bool)(A B:plate I): SU.E:= polarT b (call (dye b A) (dye b B))
def decideG(t:Bool×Bool)(A B:plate I):= if t.1 then (lift_g t.2 B A)⁻¹ else lift_g t.2 A B -- orientation-charge pair
theorem call_m : Measurable (Function.uncurry (@call I _)):= (bank (I:=I)).choose_spec.1
theorem backdist(A B:plate I)(g:SU.E): dist (roll A g⁻¹) B=dist (roll B g) A:=by rw [← roll_dist _ _ g,roll_mul,inv_mul_cancel,roll_one,dist_comm]
lemma pol_self(b:Bool)(x:SU.E): polarT b (polarT b x)=x:=by rw [polar_t,Bool.xor_self]; rfl
lemma lift_m(b:Bool):Measurable (Function.uncurry (@lift_g I _ b)):= by
 have he:Measurable (dye b : plate I→ plate I):=(show Continuous (dye b : plate I→plate I) from (Isometry.of_dist_eq (dye_dist b)).continuous).measurable
 exact (Skye.rev_C b).measurable.comp (call_m.comp ((he.comp measurable_fst).prodMk (he.comp measurable_snd)))
lemma decide_m(k:Bool× Bool): Measurable (Function.uncurry (@decideG I _ k)):= by
 cases k with|mk a b=> cases a; exact lift_m b; exact ((lift_m b).comp (measurable_snd.prodMk measurable_fst)).inv
lemma lift_p (p:Bool)(A B:plate I)(g:SU.E):dist (roll A (lift_g p A B)) B ≤ dist (roll A g) B:=by unfold lift_g; rw [←dye_dist p,← dye_dist p (roll A g),dye_roll,dye_roll,pol_self]; exact (bank (I:=I)).choose_spec.2 (dye p A,dye p B) (polarT p g) -- pair infer
lemma decide_p(k:Bool×Bool)(A B:plate I)(g:SU.E): dist (roll A (decideG k A B)) B ≤ dist (roll A g) B:=by
 obtain ⟨a,b⟩:=k; cases a; exact lift_p b ..; unfold decideG; rw [if_pos rfl]; rw [backdist, ← inv_inv g, backdist]; exact lift_p b ..
lemma lift_spin (a p:Bool)(A B:plate I): lift_g (p.xor a) (dye p A) (dye p B)=polarT p (lift_g a A B):= by
 cases p; · rw [Bool.false_xor]; rfl
 unfold lift_g; cases a <;> simp only [Bool.xor,dye, ↓reduceIte, Bool.false_eq_true, polar_t,blink_blink] <;> rfl
-- selecting after frame under Opts.
@[simp] lemma decide_spin (a p:Bool)(b:Bool)(A B:plate I): decideG (a,p.xor b) (dye p A) (dye p B)= polarT p (decideG (a,b) A B):= by cases a; exact lift_spin b p A B; unfold decideG; simp [lift_spin]
lemma flip_spin (a b:Bool)(A B:plate I): decideG (!a,b) B A=(decideG (a,b) A B)⁻¹:= by unfold decideG; cases a <;> simp
end YM.CF.BProof.Mesh.Shore
