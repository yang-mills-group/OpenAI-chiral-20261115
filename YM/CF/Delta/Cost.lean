import YM.CF.Delta.Rebase

/-! Uniform radius for four-dimensional links. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Delta
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Fock SU Lat Cube Phase NormedSpace Branch Tenant Function Finset MeasureTheory Filter Lattice
attribute [local instance] opCStarAlgebra
variable {N m B : Side} {p e : ℝ}
lemma costsV (p : ℝ) {I : Type*} [Fintype I] [DecidableEq I] (R : E→*UNI I) (U V : Bkg N) (u : ∀ x, Cube.cmp R (U x) (V x)≤p) (x : Site N) (t : Walk) : Cube.cmp R (Lattice.travel U x t) (Lattice.travel V x t) ≤ (t.length:ℝ)*p := by
  induction t generalizing x with
  | nil=> simp [Cube.cmp,Lattice.travel]
  | cons s t ih=>
    let a := s.read U x; let b := s.read V x; let A := Lattice.travel U (x+s.vec) t; let B := Lattice.travel V (x+s.vec) t
    have ha : Cube.cmp R a b ≤ p := by
      unfold a b Step.read; split_ifs; swap; exact u _
      have hv (x y:E) : Cube.cmp R x⁻¹ y⁻¹=Cube.cmp R x y := by
        unfold Cube.cmp; rw [map_inv,map_inv]; change ‖star (R x).val-star (R y).val‖ = _; rw [←star_sub,norm_star]
      rw [hv]; exact u _
    change Cube.cmp R (a*A) (b*B) ≤ _; apply (cmp_triangle R _ (b*A) _).trans; rw [cmp_right,cmp_left]
    apply (add_le_add ha (ih _)).trans; rw [List.length_cons]; push_cast; linarith

def CloseP (p : ℝ) (U V : Bkg N) := (∀ i, Cube.cmp firstF (U i) (V i) ≤ p) ∧ (∀ i, Cube.cmp matter (U i) (V i) ≤ p)
variable {U V : Skin m B}
lemma pose (R : E→*UNI Slot) {g k : E} : ‖color R g-color R k‖ ≤ Cube.cmp R g k := by rw [color,color, ←op_kron_sub]; apply replicas_bound
lemma shift_t (i : Axis) (cut) (k:0 ≤ p) (h : CloseP p U V) : ‖shift matter (links U) cut i-shift matter (links V) cut i‖≤2*p := by
  unfold shift; rw [←jump_sub]; apply jump_bound _ _ (by positivity); intro x
  change ‖seam cut x i • color matter (links U (x,i))-seam cut x i • color matter (links V (x,i))‖≤_
  rw [←smul_sub,norm_smul,seam_norm,one_mul]; apply (pose matter).trans; unfold links
  apply (cmp_triangle matter _ (V (node x,i)*U (node x+step i,i)) _).trans; rw [cmp_right,cmp_left,two_mul]; exact add_le_add (h.2 _) (h.2 _)
lemma frame_t (cut) (k:0≤p) (h : CloseP p U V) : ‖wiel m B cut U - wiel m B cut V‖≤16*p := by
  let P := frame matter (links U) cut; let Q := frame matter (links V) cut
  have he i : ‖P.inc i-Q.inc i‖≤4*p := by
    have hk : ‖P.T i - Q.T i‖ ≤ 2*p := shift_t i cut k h
    have hv : ‖star (P.T i)-star (Q.T i)‖≤ 2*p := by rw [←star_sub,norm_star]; exact hk
    have hl {x y:Op (Ave.Elf m B)} (h : ‖x-y‖ ≤ 2*p+2*p) : ‖(1/2:ℝ) • x-(1/2:ℝ) • y‖ ≤ 2*p := by
      rw [←smul_sub,norm_smul]; apply (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans; rw [WilsonFrame.half_step]
    change ‖1-(1/2:ℝ) • (P.T i+star (P.T i)) + P.gamma i*((1/2:ℝ) • (P.T i-star (P.T i))) - (1-(1/2:ℝ) • (Q.T i+star (Q.T i)) + P.gamma i*((1/2:ℝ) • (Q.T i-star (Q.T i))))‖≤_
    rw [add_sub_add_comm,←mul_sub,sub_sub_sub_cancel_left] -- tune
    apply (norm_add_le ..).trans
    apply (add_le_add (?_ : _ ≤ 2*p) ((norm_mul_le ..).trans (?_ : _ ≤ 2*p))).trans (by linarith)
    · rw [norm_sub_rev]; apply hl; rw [add_sub_add_comm]; exact (norm_add_le ..).trans (add_le_add hk hv)
    · rw [P.gamma_norm,one_mul]; apply hl; rw [sub_sub_sub_comm]; exact (norm_sub_le ..).trans (add_le_add hk hv)
  change ‖P.chir*(_+∑ i,P.inc i)-P.chir*(_+∑ i,Q.inc i)‖≤_; rw [←mul_sub,add_sub_add_left_eq_sub,←sum_sub_distrib]; apply (norm_mul_le ..).trans; rw [P.chir_norm,one_mul]; exact (norm_sum_le ..).trans ((sum_le_sum (fun i _=>he i)).trans (by simp [nsmul_eq_mul] <;> ring_nf <;> norm_num [Axis])) -- tune
lemma pro_near (c) (b : Room B e) (h:Guard U e) (k:Guard V e) (g : CloseP p U V) (hp : 0≤p) : ‖lens m B c U-lens m B c V‖≤16400*(16*p) := ((wiel_ok c b h).proj_near (wiel_ok c b k)).trans (mul_le_mul_of_nonneg_left (frame_t c hp g) (by norm_num))
lemma cart_near {x : Index m} {z} (g : x∈active m B z) (s : Ballot) (k : 0≤p) (h : CloseP p U V) : ‖freight m B U z x s-freight m B V z x s‖≤ (4*(B.val:ℝ))*p := by
  unfold freight; rw [←smul_sub,norm_smul,←sum_sub_distrib]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (norm_nonneg _)); apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=>(4*(B.val:ℝ))*p) (fun i _=>?_)) (norm_nonneg _)) -- tune
  · simp only [sum_const,card_univ,nsmul_eq_mul]; let n := (Fintype.card Lattice.Order:ℝ); have he:0<n:= Nat.cast_pos.mpr Fintype.card_pos
    rw [Real.norm_of_nonneg (show 0≤n⁻¹ by positivity),←mul_assoc, inv_mul_cancel₀ he.ne',one_mul]
  apply (turn_price (tax m B U z x i) (tax m B V z x i) s.val).trans; rw [vote_unit,mul_one]
  have he := costsV p firstF U V h.1 z (march z (address m B x) i)
  apply he.trans; apply mul_le_mul_of_nonneg_right _ k; exact_mod_cast march_len z _ i ((separation_comm ..).trans_le (node_dist g).le)
lemma color_near {q : Sq} (s : ArrayF m) {r} (p₁:q∈zone r) (b : Room B e) (h:Guard U e) (u : Verified m B margin U s r) (g:Guard V e) (v : Verified m B margin V s r) (k : 0 ≤ p) (o : CloseP p U V) (i:Site (Domain m B)) : ‖paintV m B U s q i - paintV m B V s q i‖ ≤ 4/low * (4*(B.val:ℝ)*p) := by
  apply (ren_near (prism_nonzero s p₁.1 b.1 h u p₁.2 b.2.2.1 i) (prism_nonzero s p₁.1 b.1 g v p₁.2 b.2.2.1 i)).trans; apply mul_le_mul_of_nonneg_left _ (by have he := low_p; positivity); unfold paint; rw [←sum_sub_distrib]; apply (norm_sum_le ..).trans; let w:=cash m B i q; let K:=4*(B.val:ℝ)*p; apply (sum_le_sum (g:=fun j=>w j*K) _).trans
  · rw [←sum_mul, show ∑ j:Spot m,w j=1 from cash_sum m B i q p₁.1,one_mul]
  intro j _; have he := cash_nonneg m B i q j; rw [←smul_sub,norm_smul,Real.norm_of_nonneg he]
  by_cases e:w j=0
  · rw [show cash m B i q j=0 from e,zero_mul,e,zero_mul]
  have ht : j∈ bandS m B i q := mem_filter.mpr ⟨mem_univ _,lt_of_le_of_ne he (show _ from Ne.symm e)⟩ -- tune
  exact mul_le_mul_of_nonneg_left (cart_near (spot_hit ht) (s j) k o) he
-- additional degree guard will come later
lemma tune (B : Side) : ∃ p:ℝ, 0<p ∧ ∀ m:Side,∀ q:Sq,∀ U V:Skin m B, CloseP p U V→∀ r:Zone,∀ s:ArrayF m,q∈zone r→ Verified m B margin U s r→ Verified m B margin V s r → ∀ e:ℝ, Room B e → Guard U e → Guard V e →∀ c:Phase.Part m B, ‖lens m B c U-lens m B c V‖ ≤ 1/16 ∧ ‖bow m B U s q-bow m B V s q‖≤1/16 := by
  obtain ⟨v,H,u⟩:= evenly (1/16) (by norm_num)
  let K := 4/low * (4*(B.val:ℝ)); have he := low_p; have h : 0<K := by
    unfold K; have ht : 0 < (B.val:ℝ):=by exact_mod_cast B.property
    positivity
  let p := min (1/(16400*16*16)) (v/K); have hk : 0<p := by unfold p; positivity
  refine ⟨p,hk,?_⟩; intro m q U V o r s f g w e b t hx c
  refine ⟨(pro_near c b t hx o hk.le).trans ?_,?_⟩
  · have hp : p≤1/(16400*16*16) := min_le_left ..; linarith
  unfold bow Cfield; rw [←jump_sub]; apply jump_bound _ _ (by norm_num); intro i
  apply u _ _ (grain_unit b t g f i) (grain_unit b hx w f i)
  apply (color_near s f b t g hx w hk.le o _).trans
  rw [←mul_assoc,mul_comm]; exact (le_div_iff₀ h).mp (show p≤v/K from min_le_right ..)
end YM.CF.Delta
