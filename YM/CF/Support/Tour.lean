import YM.CF.Support.Ln

/-! Support bounds uniform over arbitrary volume and chosen input domains. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter NormedSpace
attribute [local instance] opCStarAlgebra
structure Tour (Z : Type*) where
  Y : Z → Type
  I : Z → Type
  D : Z → Type
  G : Z → Type
  ys : ∀ z,Fintype (Y z)
  yt : ∀ z,DecidableEq (Y z)
  is : ∀ z,Fintype (I z)
  it : ∀ z,DecidableEq (I z)
  ine : ∀ z,Nonempty (I z)
  dt : ∀ z, TopologicalSpace (D z)
  stageK : ∀ z, Stage (Y z) (I z) (D z) (G z)
attribute [instance] Tour.ys Tour.yt Tour.is Tour.it Tour.ine Tour.dt
namespace Tour
variable {Z : Type*} {y : Tour Z}
def ample (y : Tour Z) : Prop := ∃ C:ℝ, 0≤C ∧ ∀ z,Capacity (y.stageK z) C
abbrev MapW (y : Tour Z) := ∀ z, Raw (y.D z) (y.I z)
abbrev ChartW (y : Tour Z) := ∀ z, Tag (y.stageK z)
abbrev partner (s : ChartW y) : ChartW y := fun z=> (s z).reverseV
def Enters (y : Tour Z) (s t : ChartW y) (F : MapW y) := ∃ a K : ℝ, 0<a ∧ 0<K ∧ ∀ z, RootedK (s z) (t z) a K (F z)
variable {s t u : ChartW y} {A B : MapW y}
lemma make (a K : ℝ) (e : 0 < a) (h : ∀ z, RootedK (s z) (t z) a K (A z)) : Enters y s t A :=
  ⟨a,max 1 K,e,lt_max_of_lt_left zero_lt_one,fun z=> (h z).books (le_max_right ..)⟩
namespace Enters
lemma scale (h : Enters y s t A) (c : ℂ) : Enters y s t (fun z x=>c • A z x) := by
  obtain ⟨a,K,h,p,L⟩ := h; exact make a _ h fun z=>(L z).raise c
lemma scaleV (h : Enters y s t A) (c : Z→ℝ) (w : ℝ) (e : ∀ z, ‖c z‖≤w) : Enters y s t (fun z x=>c z • A z x) := by
  obtain ⟨a,K,h,p,L⟩ := h
  apply make a (w*K) h; intro z
  have he (x) : (↑(c z):ℂ) • A z x=c z • A z x := by ext i j; simp [Complex.real_smul]
  have ht := (L z).raise (↑(c z):ℂ)
  simp_rw [he] at ht
  rw [Complex.norm_real] at ht; exact ht.books (mul_le_mul_of_nonneg_right (e z) p.le)
lemma scaleR (h : Enters y s t A) (c : ℝ) : Enters y s t (fun z x=>c • A z x) := h.scaleV _ ‖c‖ (fun _=>le_rfl)
lemma join (h : Enters y s t A) (g : Enters y t u B) : Enters y s u (fun z x=>A z x*B z x) := by
  obtain ⟨a,K,h,p,L⟩ := h; obtain ⟨d,m,g,e,F⟩ := g; exact make (min a d) _ (lt_min h g) fun z=> ((L z).drop (min_le_left ..)).product ((F z).drop (min_le_right ..)) (le_min h.le g.le)
lemma plus (h : Enters y s t A) (g : Enters y s t B) : Enters y s t (fun z x=> A z x+B z x) := by
  obtain ⟨a,K,h,p,L⟩ := h; obtain ⟨d,m,g,e,F⟩ := g; exact make (min a d) _ (lt_min h g) fun z=> ((L z).drop (min_le_left ..)).plus ((F z).drop (min_le_right ..))
lemma neg (h : Enters y s t A) : Enters y s t (fun z x=> -A z x) := by obtain ⟨a,K,h,p,L⟩ := h; exact make a _ h fun z=>(L z).minus
lemma sub (h : Enters y s t A) (g : Enters y s t B) : Enters y s t (fun z x=> A z x-B z x) := by simp_rw [sub_eq_add_neg]; exact h.plus g.neg
lemma starL (h : Enters y s t A) : Enters y t s (fun z x=> star (A z x)) := by obtain ⟨a,K,h,p,L⟩ := h; exact make a _ h fun z=>(L z).starUp
lemma ccL (h : Enters y s t A) : Enters y (partner s) (partner t) (fun z x=>cc (A z x)) := by obtain ⟨a,K,h,p,L⟩ := h; exact make a _ h fun z=>(L z).ccUp
lemma identity (s : ChartW y) : Enters y s s (fun _ _=> 1) := make 1 _ zero_lt_one (fun _=> RootedK.oneK ..)
lemma fans (h : Enters y s s A) : Enters y s s (fun z x=> exp (A z x)) := by
  obtain ⟨a,K,h,p,L⟩ := h; exact make a _ h fun z=> (L z).wind h.le p.le -- tune
lemma orderV (p : ample y) (h : Enters y s s A) (r : ℝ) (he : 0<r) (hu : r<1) (g : ∀ z x, ‖A z x‖ ≤ r) :
    ∃ a c M : ℝ, 0 < a ∧ 0<c ∧ c<1 ∧ 0<M ∧ ∀ z i, RootedK (s z) (s z) a (M*c^i) (fun x=>A z x^i) := by
  obtain ⟨C,H,L⟩ := p; obtain ⟨a,K,h,k,w⟩ := h
  obtain ⟨q,hp,hQ⟩ := exists_between hu
  obtain ⟨n,hN,v,d,e,p,A₀,U⟩ := grouping H h k hp (he.trans hp) hQ (show 0<(1:ℝ)/4 by norm_num)
  obtain ⟨t,j,f,B⟩ := drift_name hN (show 0<(1:ℝ)/2 by norm_num) (by norm_num)
  refine ⟨d,t,2 * (Real.exp d * (t^n)⁻¹ * (Real.exp d*(max 1 (2*K))^n)),e,j,f,?_,fun z i=>?_⟩; swap -- tune metaflow
  · have ht : RootedK (s z) (s z) d (1/4) (fun x=>A z x^n) := power_low C a K q _ r n v d H h.le (he.trans hp).le e.le p A₀ U (L z) (w z) (g z) -- inference of implicit params?
    exact tariff hN (w z) ht (p.trans (half_le_self h.le)) e j B i
  positivity
lemma geometricV (p : ample y) (h : Enters y s s A) (r : ℝ) (he : 0<r) (hu : r<1) (g : ∀ z x, ‖A z x‖ ≤ r) (j : ℕ) (c : ℕ→ℝ) (e : ∀ k, ‖c k‖≤1) :
    Enters y s s (fun z x=> ∑' k:ℕ, c k • A z x^(k+j)) := by
  obtain ⟨a,q,m,p,h,v,u,k⟩ := orderV p h r he hu g
  let M := fun k:ℕ=>m*q^(k+j)
  have H : Summable M := ((summable_nat_add_iff j).mpr (summable_geometric_of_lt_one h.le v)).mul_left _
  apply make a (∑' k,M k) p; intro z
  refine RootedK.tsK M (fun i=>?_) p.le H
  have hx := (k z (i+j)).raise (↑(c i):ℂ)
  simp only [Complex.norm_real] at hx
  have ht x : (↑(c i):ℂ) • A z x^(i+j)=c i • A z x^(i+j) := by ext l t; simp [Complex.real_smul]
  simp_rw [ht] at hx; exact hx.books ((mul_le_mul_of_nonneg_right (e i) (by positivity)).trans (by unfold M; rw [one_mul]))
lemma inverted (p : ample y) (h : Enters y s s A) (r : ℝ) (he : 0<r) (hu : r<1) (g : ∀ z x, ‖A z x‖≤r) : Enters y s s (fun z x=> (1-A z x)⁻¹) := by
  have H := geometricV p h r he hu g 0 (fun _=>1) (by simp); simp only [add_zero,one_smul,route_inv ((g _ _).trans_lt hu)] at H -- tune
  exact H
lemma scrolled (p : ample y) (h : Enters y s s A) (r : ℝ) (he : 0<r) (hu : r<1) (g : ∀ z x, ‖A z x‖≤r) : Enters y s s (fun z x=> pencil (A z x)) := geometricV p h r he hu g 1 bcoef bc_norm
lemma rs (p : ample y) (h : Enters y s s A) (e : ∀ z x, Safe (A z x)) : Enters y s s (fun z x=>rsEval (A z x)) := by
  let L : MapW y := fun z x=> slack (A z x)
  have ht : Enters y s s L := by unfold L slack; simp_rw [pow_two]; exact (identity s).sub ((h.join h).scaleR _)
  have H := geometricV p ht rho rho_pos rho_lt (fun z x=>(e z x).good) 0 SignScalar.c SignScalar.c_norm
  unfold rsEval rsTerm; simpa only [add_zero] using H
lemma hood (p : ample y) (h : Enters y s s A) (e : ∀ z x, Safe (A z x)) : Enters y s s (fun z x=> polarity (A z x)) := (h.scaleR _).join (rs p h e)
lemma site (p : ample y) (h : Enters y s s A) (e : ∀ z x, Safe (A z x)) : Enters y s s (fun z x=> projector (A z x)) := ((identity s).plus (hood p h e)).scaleR _
lemma bodyV (h : Enters y s s A) (e : Enters y s (partner s) B) : Enters y s (partner s) (fun z x=> body (A z x) (B z x)) := (h.join e).join h.ccL
lemma stageV (h : Enters y s s A) (e : Enters y s (partner s) B) : Enters y s (partner s) (fun z x=>stage (A z x) (B z x)) := (h.bodyV e).plus (((identity s).sub h).bodyV e)
lemma stageI (p : ample y) (h : Enters y s s A) (e : Enters y s (partner s) B) (q : ∀ z x, ‖stage (A z x) (B z x)-B z x‖≤1/3) (f : ∀ z x,B z x∈unitary _) :
    Enters y (partner s) s (fun z x=> (stage (A z x) (B z x))⁻¹) := by
  let T : MapW y := fun z x=>stage (A z x) (B z x)
  let N : MapW y := fun z x=>1-star (B z x)*T z x
  have he := (identity (partner s)).sub (e.starL.join (h.stageV e))
  have hu z x : ‖N z x‖≤1/3 := by
    let V : UNI (y.I z) := ⟨B z x,f z x⟩; rw [← CStarRing.norm_coe_unitary_mul V]; unfold N; rw [mul_sub,mul_one]; change ‖V.val-V.val*(star V.val*T z x)‖≤_
    rw [←mul_assoc,show V.val*star V.val=1 from V.property.2,one_mul,norm_sub_rev]; exact q ..
  have ht := inverted p (show Enters y (partner s) (partner s) N from he) _ (show 0<(1:ℝ)/3 by norm_num) (by norm_num) hu
  have hk (z x) : (1-N z x)⁻¹*star (B z x)=(stage (A z x) (B z x))⁻¹ := by
    let S := T z x
    have hi : IsUnit S := closeUnit (A:=S) (⟨B z x,f z x⟩:UNI (y.I z)) ((q z x).trans_lt (by norm_num))
    have hg : 1-N z x=star (B z x)*S := sub_sub_cancel ..
    have hB : IsUnit (1-N z x) := by apply nearOne; rw [sub_sub_cancel]; exact (hu _ _).trans_lt (by norm_num)
    change _=S⁻¹
    calc _ = ((1-N z x)⁻¹*star (B z x)*S)*S⁻¹ := by rw [mul_assoc (_ * _), (live hi).1,mul_one] -- tune
         _ = S⁻¹ := by rw [mul_assoc ((1-N z x)⁻¹), ←hg,(live hB).2,one_mul]
  have hL := ht.join e.starL; simpa only [hk] using hL
end Enters
end Tour
end YM.CF.Branch
