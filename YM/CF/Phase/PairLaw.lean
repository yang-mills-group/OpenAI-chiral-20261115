import YM.CF.Phase.Replica
import YM.CF.Sample.Nook

/-! Comparison laws, parameter regularity, planar dependency. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Sample
attribute [local instance] opCStarAlgebra
variable {m B : Side}
-- improve the strict locality of rates to closed faces
variable {I : Type} [Fintype I] [DecidableEq I] (A : Finset I) (U V : Skin m B) (p q : I → ArrayF m) (r : I→Zone) (j : Row) (a : Index m) (x y : Cue m)
lemma inner_fund (u v : ArrayF m) (t : Zone) (f : AgreeF ((faces m a) ×ˢ Finset.univ) u v) (g : Agrees (room m B a) U V) : fundF m B U u t (a,j)=fundF m B V v t (a,j) := by
  unfold fundF; apply prod_congr rfl; intro l hl
  unfold rateF; rw [f (a,j) (by simp [faces,fits_id]),train_local a (fits_id m a) l (permits_iff.mp hl).1 g] -- tune
  intro i hi; have he := move_mem (permits_iff.mp hl).1 _ hi; exact f i.1 (by rw [mem_product]; exact ⟨mem_filter.mpr ⟨mem_univ _,he.1⟩,mem_univ _⟩)
lemma inner_rate (h : ∀ i∈A, AgreeF ((faces m a) ×ˢ Finset.univ) (p i) (q i)) (f : AgreeF (faces m a) x y) (g : Agrees (room m B a) U V) : priceW m B A U p r j a x=priceW m B A V q r j a y := by
  have ht x y (f : AgreeF (faces m a) x y) : draw m B A U p r j a x=draw m B A V q r j a y := by
    apply prod_congr rfl; intro i hi; unfold dry; apply inner_fund _ _ _ _ _ _ _ _ g
    intro z hz; unfold capRow; split <;> first | exact f _ (mem_product.mp hz).1 | exact h i hi z hz
  unfold priceW; rw [ht x y f,limitW,limitW]; congr 1; apply integral_congr_ae; apply Eventually.of_forall; intro i
  apply ht; intro v hv; by_cases he:v=a <;> simp [he,f v hv]
lemma water_limit (f : AgreeF (faces m a) x y) (g : Agrees (room m B a) U V) : water m B U a x=water m B V a y := inner_rate _ _ _ _ _ _ _ a x y (fun _ _ i w=> f i.1 (mem_product.mp w).1) f g
lemma water_base (u : ArrayF m) : water m B U a x=priceW m B Finset.univ U (fun _:Unit=>u) (fun _=>∅) 0 a x := (vacant_price m B U a x u).symm
lemma water_norm : ∫ v:Ballot, water m B U a (update x a v) ∂cloud=1 := by
  simp_rw [water_base U a _ (slot m x)]; exact price_integral _ _ _ _ _ _ _ _ x (by simp)
lemma water_cont (m B a) : Continuous (fun x:Skin m B×Cue m=>water m B x.1 a x.2) := by
  let u := Classical.arbitrary (ArrayF m)
  simp_rw [water_base _ _ _ u]; let f := fun x:Skin m B × Cue m=>(x.1,(fun _:Unit=>u),x.2)
  let F := fun t:Skin m B×(Unit→ArrayF m) × Cue m=>priceW m B Finset.univ t.1 t.2.1 (fun _=>∅) 0 a t.2.2
  change Continuous (F ∘ f); exact (show Continuous F from price_cont _ _ _ _ _ _ (by simp)).comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)) -- tune syntax
lemma water_pos : 0≤water m B U a x := price_pos _ _ _ _ _ _ _ _ _ (by simp)
def rock (m B : Side) (U : Skin m B) : Plan (Index m) cloud where
  orderF := degree m
  indexF := faces m
  run a := water m B U a
  polite a := by
    let F := fun t:Skin m B × Cue m => water m B t.1 a t.2
    change Continuous (F ∘ fun v=> (U,v)); exact (show Continuous F from water_cont m B a).comp (continuous_const.prodMk continuous_id)
  normalize i v := water_norm U i v
  readF i v w h := water_limit U U i v w h (fun _ _ _=>rfl)
  rightF := fun i v=> water_pos U i v
  before i j p l := fits_degree (mem_filter.mp p).2 l.symm
lemma base_pl : law m B U x=fall (rock m B U) x := rfl
def Down (m : Side) (s : Finset (Index m)) := ∀ x∈s,(faces m x)⊆s
lemma base_down {s} (h : Down m s) : Bank (rock m B U) s := h
lemma nested_ch (S : Seal (Site (Domain m B))) : Down m (chairs m B S) := by
  intro i g a h
  obtain ⟨x,e,y,l,K⟩ := chaff.mp g; exact chaff.mpr ⟨x,e,y,l,fits_trans (mem_filter.mp h).2 K⟩
lemma faces_down : Down m (faces m a) := fun i l j k => mem_filter.mpr ⟨mem_univ _,fits_trans (mem_filter.mp k).2 (mem_filter.mp l).2⟩

def request (m : Side) (x y : Cue m) : Bool→ArrayF m := fun b=> if b then slot m x else slot m y
def bidW (m B : Side) (U : Skin m B) (x y : Cue m) (a : Index m) (z : Cue m) := priceW m B Finset.univ U (request m x y) (fun _=>{0}) 1 a z
def bid (m B : Side) (U : Skin m B) (x y z : Cue m) := rates m B Finset.univ U (request m x y) (fun _=>{0}) 1 z
lemma bid_norm : ∫ z:Cue m,bid m B U x y z ∂rains m=1 := launched _ _ _ _ _ _ _ (by simp)
lemma bid_live (z : Cue m) : 0≤bid m B U x y z := live_rate _ _ _ _ _ _ _ _ (by simp)
lemma bid_js (m B a) : Continuous (fun t : ((Skin m B × Cue m) × Cue m)× Cue m => bidW m B t.1.1.1 t.1.1.2 t.1.2 a t.2) := by
  let f := fun t:((Skin m B × Cue m) × Cue m)× Cue m=> (t.1.1.1,request m t.1.1.2 t.1.2,t.2)
  let F := fun t:Skin m B ×(Bool→ArrayF m) × Cue m=> priceW m B Finset.univ t.1 t.2.1 (fun _=>{0}) 1 a t.2.2
  change Continuous (F ∘ f); apply (show Continuous F from price_cont m B _ _ _ a (by simp)).comp
  unfold f; refine Continuous.prodMk (by fun_prop) (Continuous.prodMk (continuous_pi (fun i=>?_)) continuous_snd)
  cases i <;> simp only [request, Bool.false_eq_true,ite_false,ite_true] <;> exact (slot_cont _).comp (by fun_prop)
lemma bid_conn (m B) : Continuous (fun t : ((Skin m B × Cue m) × Cue m)× Cue m => bid m B t.1.1.1 t.1.1.2 t.1.2 t.2) := continuous_finsetProd _ (fun i _=>bid_js m B i)
lemma bid_limit {U V : Skin m B} {x x' y y' z z' : Cue m} (g : Agrees (room m B a) U V) (e : AgreeF (faces m a) x x') (l : AgreeF (faces m a) y y') (v : AgreeF (faces m a) z z') : bidW m B U x y a z=bidW m B V x' y' a z' := inner_rate Finset.univ U V _ _ _ _ a z z' (fun i _ k hk=>by
  unfold request; split; exact e k.1 (mem_product.mp hk).1; exact l k.1 (mem_product.mp hk).1) v g

-- robust law wherever caps active.
lemma ready_vertex {z : Cue m} (h : bid m B U x y z≠0) (a : Index m) : fundF m B U (twin m x z) (insert 1 {0}) (a,1)≠0 ∧ fundF m B U (twin m y z) (insert 1 {0}) (a,1)≠0 := by
  have ht : rates m B univ U (request m x y) (fun _=>{0}) 1 z ≠ 0 := h
  have he := lt_of_le_of_ne (live_rate m B _ _ _ _ _ _ (by simp)) ht.symm
  have hp := germ m B _ _ _ _ _ _ (by simp) he a
  have hx i := (price_live m B _ _ _ _ _ _ _ (by simp) hp i (mem_univ _)).ne'
  exact ⟨hx true, hx false⟩
lemma checksX {z : Cue m} (g : ZeroF m B U x) (h : ∀ a:Index m, Check m B margin U (twin m x z) (insert 1 {0}) (a,1)) : EdgeP m B U x z := by
  rintro ⟨i,j⟩ p; simp only [Finset.mem_insert,Finset.mem_singleton] at p; rcases (show j=1 ∨ j=0 from p) with e|e <;> subst j
  · exact h i
  intro l hl; rcases (permits_iff.mp hl) with ⟨p,r⟩
  have he (w) (e:w∈l) : (w :Ramp m).1.2=0 := by
    have hk : w.1.2 ≤ 0 := (move_mem p _ e).2.1; exact le_antisymm hk (Fin.zero_le _) -- tune
  have hf := g (i,0) (mem_singleton_self (0:Row)) l (permits_iff.mpr ⟨p,fun w h=> mem_singleton.mpr (he w h)⟩)
  rw [show twin m x z (i,0)=slot m x (i,0) by simp [twin,capRow], train_eq m B U (slot m x) i l _]
  · exact hf
  intro w hw; simp [twin, capRow, he w hw]
lemma bid_ready {z : Cue m} (g : ZeroF m B U x) (e : ZeroF m B U y) (h : bid m B U x y z≠0) : Arch m B U x y z := by
  constructor
  · apply checksX U x g; intro a; apply pay_check; intro l hl; exact (pay _ _ _ _ _ _ (lt_of_le_of_ne (fund_pos ..) (ready_vertex U x y h a).1.symm) l hl).le
  apply checksX U y e; intro a; apply pay_check; intro l hl; exact (pay _ _ _ _ _ _ (lt_of_le_of_ne (fund_pos ..) (ready_vertex U x y h a).2.symm) l hl).le
end YM.CF.Phase
