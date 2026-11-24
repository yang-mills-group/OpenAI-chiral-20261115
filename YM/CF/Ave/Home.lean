import YM.CF.Ave.Current
/-! Nonperturbative finite statements through Fock measure. No continuum limit is asserted in this file. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ave
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder
open Fock SU Lat Cube Phase Phase.Sample Mir RP MeasureTheory NormedSpace Branch Lattice Tenant Function Pastry Petal Manifest Filter Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Foot m B} {W : Scroll m B c} {e v H σ A d r β b k t : ℝ}
-- pull on cylinder expectations
noncomputable def render (t : ℝ) (W : Scroll m B c) {e : ℝ} (V : Room B e) (b β : ℝ) (K : Seal (Index m)→ Briar m B e→ Ewe m B) (f : Readers m B) (x : Skin m B) : ℂ :=
    @dite ℂ (Guard x e) (Classical.propDecidable _) (fun h=> stroll (m:=m) (B:=B) ⟨x,h⟩ W V b t β K f) (fun _=>0)
lemma vintage {p : 1≤H} (g : ScaleK A d W) (v : Budget B e r) {K w} (y : FormR W H p e k K w t b) (f : Readers m B) (h : Continuous f) : rawE W e β t b c (fun x=> f x.1)=∫ x, render t W v.1 b β K f x ∂barrow m B := by
  let t' := ratioR W e β t b c (fun x=>f x.1)
  refine (show (∫ x,t' x ∂wheel m B)=(∫ y, ∫ z,t' (y,z) ∂rains m ∂barrow m B) from integral_prod _ (μ:=barrow m B) (ν:=rains m) (hf:=sojourn g v (h.comp continuous_fst) β t b c)).trans ?_; apply integral_congr_ae; apply Eventually.of_forall; intro x
  change ∫ z, ratioR W e β t b c (fun x=>f x.1) (x,z) ∂rains m= render t W v.1 b β K f x; unfold render; split_ifs with p
  · exact mileage y v.1 (⟨x,p⟩:Briar m B e) f β
  let T:= TallyR m B e β; have ht (z:Cue m) : (x,z)∉TallyR m B e β := fun k=>p k.1; simp [ratioR,ht] -- tune
-- tie log densities and effective insertion to one wedge
structure Effect (s : 1≤H) (m B : Side) (e β : ℝ) (R : Reg β e B) (n : ℕ) (k σ : ℝ) (K : Seal (Index m)→ Briar m B e→ Ewe m B) (w : Seal (Index m)→ℝ) (p : Room B e) : Prop where
  scalar : Charge (moneyW m B e) (terr _) (k/2) (bulk k 16*(1/3)) (fun S x=>pane (K S x)) w
  occurrence : Charge (welter m B e H s) (terr _) (k/2) ((σ^n)*(bulk k 16*(1/3))) (fun S x=>cloudless (K S x)) (fun S=>σ^n*w S)
  degree (x : Briar m B e) : pane (cloudD K x)=0
  scalarExp x : pigment (R.W m) R.knob x.val=Complex.exp (scalarD K x)
  state (x : Briar m B e) : (zeroOf x (R.c m) p).cook (motor (travel m B e H s) (fun z=> exp (chili (R.W m) R.knob (R.time n) z)) x)=pigment (R.W m) R.knob x.val • exp ((zeroOf x (R.c m) p).cook (cloudD K x))
  atFiber x f : ∫ z, ratioR (R.W m) e β (R.time n) R.knob (R.c m) (fun x=>f x.1) (x.val,z) ∂rains m = stroll (m:=m) (B:=B) x (R.W m) p R.knob (R.time n) β K f -- binder types
  assemblyV f (z : Continuous f) : rawE (R.W m) e β (R.time n) R.knob (R.c m) (fun x=> f x.1)=∫ x, render (R.time n) (R.W m) p R.knob β K f x ∂barrow m B
lemma morals {R : Reg β e B} (f : 1 ≤ H) (p : Budget B e d) (g : ScaleK A v (R.W m)) (h : 0<σ) (q : σ<1) (n : ℕ) (b : 1≤bond σ H n) {K w} (L : FormR (R.W m) _ b e k K w (R.time n) R.knob) : Effect f m B e β R n k σ K w p.1 := by
  refine ⟨gradeZero L.fine,pirates (σ^n) f (pow_pos h _) (pow_le_one₀ h.le q.le) b L.fine,fun x=> ?_,pitchF L,fun x=>finale L p.1 x,fun x y=>mileage L p.1 x y β,fun f q=>vintage g p L f q⟩
  rw [cloudD,pane_f,sum_eq_zero]; intro i _; exact cloudless_two _
lemma cupSize (B : Side) (x : ℝ) (l : 0<x) (p : 0<k) (f : 0<r) : ∃ v:ℝ, 0<v ∧ v≤r ∧ ∀ b:ℝ,1-v<b→b<1→ ‖b‖≤1 ∧ ∀ m:Side, ‖1-b‖*hover m B (k+2) x ≤ 1/32 := by
  let X := hover 1 B (k+2) x; have hX : 0<X := by unfold X hover; positivity
  let v := min r (min 1 ((1/32)/X)); refine ⟨v,by unfold v; positivity, min_le_left ..,?_⟩; intro b t q
  have hp : v≤1 := (min_le_right ..).trans (min_le_left ..)
  have hb : 0<b := by linarith
  refine ⟨by rw [Real.norm_of_nonneg hb.le]; exact q.le,?_⟩; intro m
  change ‖1-b‖*X≤_; rw [Real.norm_of_nonneg (sub_nonneg.mpr q.le)]; apply (le_div_iff₀ hX).mp
  exact (show 1-b≤v by linarith).trans ((min_le_right ..).trans (min_le_right ..))
structure Warranty (B : Side) (e β : ℝ) (k σ : ℝ) (p : Room B e) (Y : ℝ) (R : Reg β e B) : Prop where
  passesP : R.Works
  cont m : ContinuousOn (sound m B (R.c m)) {U : Skin m B| Guard U e}
  val (m : Side) (U : Briar m B e) : Sea (P:=lens m B (R.c m) U.val) (sound m B (R.c m) U.val) -- tune binder
  upstairs (m : Side) (U : Briar m B e) (g : Court m B) : sound m B (R.c m) (Lattice.gauge g U.val) = acts (quantU (n:=Elf m B) (balls m B g)).val (sound m B (R.c m) U.val)
  payroll m : Intensive (m:=m) (B:=B) e (R.c m) k Y
  well (s:ℝ) (v:1≤s) : ∃ J:ℕ, ∀ n:ℕ,J≤n→∀ m:Side,∃ K w, Effect v m B e β R n k σ K w p
-- regime choices
lemma major (p : 0<k) : ∃ σ:ℝ,0<σ∧σ<1∧∃ N:ℕ,∀ B:Side,N≤B.val→∃ ε Y:ℝ,0<ε∧∀ e:ℝ, 0<e→ e≤ ε→ ∃ b:Room B e,∀ β:ℝ, ∀ r:ℝ,0<r→ ∃ R:Reg β e B, 1-r<R.knob ∧ Warranty B e β k σ b Y R := by
  let z:= k+2; have hx : 0<z:= by unfold z; linarith
  obtain ⟨u,c,t,v,o,X⟩:= regulated z (1/32) hx (by norm_num)
  obtain ⟨σ,h,g,l,A⟩:= insurable hx
  obtain ⟨w,N⟩:= thermal p
  obtain ⟨j,P⟩:= exists_nat_gt (z*21^4/u)
  refine ⟨σ,h,g,o+w+l+j,?_⟩; intro B hb
  have hp (e : ℝ) : z*21^4≤ u* (B.val:ℝ) := (le_of_lt ((div_lt_iff₀ t).mp P)).trans (by
    rw [mul_comm]; have he : j≤B.val:= by omega
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast he) t.le)
  obtain ⟨ε,q,E⟩:= X B (by omega); obtain ⟨Y,hY,gY⟩:= N B (by omega)
  refine ⟨ε,Y,q,?_⟩; intro e l' a
  let e₀:= E e l' a; have he : Budget B e (quantile u B) := ((e₀ 0 1 zero_lt_one).choose_spec.2.2.1 1).budget
  refine ⟨he.1,?_⟩; intro β r hr
  obtain ⟨J,r',hJ,hj⟩:= cupSize B c v p hr
  obtain ⟨R,T,y,V,b⟩:= E e l' a β J r'
  obtain ⟨d,W⟩:= hj _ T y
  refine ⟨R,lt_of_le_of_lt (by linarith) T,⟨b,fun _=>melody _ he.1,fun m U=>?_,fun m U g=>?_,fun m=>gY _ he.1 m (R.c m),fun s v'=>?_⟩⟩
  · -- from existence ZeroF
    exact unity (R.c m) he.1 U.property -- tune
  · exact band_g (R.c m) he.1 U.property g -- tune
  obtain ⟨K,P⟩:= A B (by omega) s v'
  refine ⟨K,fun n k m=>?_⟩
  obtain ⟨t,Q,F,U⟩:= P n k (R.time n) (R.charges n).1.le (R.charges n).2.le e he.1 m (R.c m)
  obtain ⟨A,L,x⟩:= accordR (V m) t U d (W m) (hp e) v.le p
  exact ⟨A,L,morals v' he (V m).scaleK h g n t x⟩
end YM.CF.Ave
