import YM.CF.Delta.Agreement

/-! Compare different gauges. Choose log phase itself, not its square. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Delta
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock SU Lat Cube Phase NormedSpace Branch Function Finset MeasureTheory Filter Tenant Lattice
attribute [local instance] opCStarAlgebra
lemma dovecote {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n] (U V:UNI n) {P Q : Op n} (p : IsStarProjection P) (q : IsStarProjection Q) (h : ‖stage P U.val-U.val‖ ≤ 1/3) (v : ‖P-Q‖≤1/16) (g : ‖U.val-V.val‖≤ 1/16) : ‖relay P U.val (body Q V.val)-1‖≤1/2 := by
  let A := U.val; let B := V.val; let Z := (stage P U.val)⁻¹
  obtain ⟨l,k⟩:= inv_close_le U h
  have hu : ‖A‖=1 := CStarRing.norm_coe_unitary _
  have hb : ‖B‖=1 := CStarRing.norm_coe_unitary _
  have he : body P (body P A)=body P A := (congrArg (fun x=>x*cc P) (body_left p A)).trans (body_right p A)
  have hr : relay P A (body Q B)-1=body P (body Q B-body P A)*Z := by
    nth_rw 1 [←relay_base p l]; unfold relay; rw [add_sub_add_right_eq_sub,←sub_mul, show body P (body Q B-body P A)=body P (body Q B)-body P (body P A) by unfold body; rw [mul_sub,sub_mul], he]
  have hs {K : Op n} : ‖body P K‖≤ ‖K‖ := by
    unfold body; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (IsStarProjection.norm_le _ (ccProj p))).trans; exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (p.norm_le _))
  rw [hr]; apply (norm_mul_le ..).trans ((mul_le_mul hs k (norm_nonneg _) (norm_nonneg _)).trans ?_)
  have ht : ‖body Q B - body P A‖ ≤ 1/4 := by
    unfold body; let a₁ := Q*B; let a₂:=P*A
    have he : ‖a₁‖≤1 := (norm_mul_le ..).trans (by rw [hb,mul_one]; exact q.norm_le _)
    have hv : ‖a₁-a₂‖≤1/16+1/16 := by
      apply (norm_sub_le_norm_sub_add_norm_sub _ (P*B) _).trans; unfold a₁ a₂; rw [←sub_mul, ←mul_sub]; refine add_le_add ((norm_mul_le ..).trans ?_) ((norm_mul_le ..).trans ?_)
      · rw [hb,mul_one,norm_sub_rev]; exact v
      rw [norm_sub_rev]; exact (mul_le_of_le_one_left (norm_nonneg _) (p.norm_le _)).trans g
    change ‖a₁*cc Q-a₂*cc P‖≤_
    apply (norm_sub_le_norm_sub_add_norm_sub _ (a₁*cc P) _).trans
    rw [←mul_sub,←sub_mul]; apply (add_le_add ((norm_mul_le ..).trans (?_ : ‖a₁‖*‖cc Q-cc P‖≤ 1/16)) ((norm_mul_le ..).trans (?_ : ‖a₁-a₂‖*‖cc P‖≤1/16+1/16))).trans (by norm_num)
    · apply (mul_le_of_le_one_left (norm_nonneg _) he).trans; obtain ⟨U,w,k⟩:= spectral_exists _ (q.isSelfAdjoint.sub p.isSelfAdjoint); rw [norm_sub_rev,k] at v; rw [←cc_sub,k,cc_spectral]; simpa only [spectral,twist_norm] using v
    apply (mul_le_of_le_one_right (norm_nonneg _) (IsStarProjection.norm_le _ (ccProj p))).trans; exact hv
  change ‖body Q B-body P A‖*2≤_; linarith
variable {N m B : Side} {p e : ℝ} {U V : Skin m B} {c : Phase.Part m B}
def salaryL (m B : Side) (U V: Skin m B) (c : Phase.Part m B) (x : Cue m) := spark (lens m B c U) (pair m B U x) (body (lens m B c V) (pair m B V x))
def subject (m B : Side) (U V:Skin m B) (c : Phase.Part m B) (x : Cue m) := salaryL m B U V c x+Phase.fund m B c U x - Phase.fund m B c V x
section
variable (c : Phase.Part m B) (L : Wood B p) (P : CloseP p U V) (b : Room B e) (u : Guard U e) (v : Guard V e)
include L P b u v
lemma roof_l {s : ArrayF m} {r : Zone} (h: Verified m B margin U s r) (g: Verified m B margin V s r) {t : Sq} (k:t∈zone r) : ‖relay (lens m B c U) (bow m B U s t) (body (lens m B c V) (bow m B V s t))-1‖≤1/2 := by
  obtain ⟨p,e,H⟩ := bow_val c b u h k; have he := bow_val c b v g k; obtain ⟨w,x⟩:= L.pose _ _ _ P b u v h g k c
  exact dovecote ⟨_,p⟩ ⟨_,he.1⟩ (lensP c b u) (lensP c b v) (show ‖stage _ _-_‖ ≤ 1/3 by rw [stage_gap (lensP c b u)]; exact H) w x -- tune
lemma poly_l {s : ArrayF m} {r : Zone} (h: Verified m B margin U s r) (g: Verified m B margin V s r) {t : Sq} (k:t∈zone r) : acts (lineOp (n:=Mind m B) (lens m B c U)) (filled (lens m B c V) (bow m B V s t))=Complex.exp (spark (lens m B c U) (bow m B U s t) (body (lens m B c V) (bow m B V s t))) • filled (lens m B c U) (bow m B U s t) := by
  exact polar_hitch (n:=Mind m B) (lensP c b u) (lensP c b v) ((L.pose _ _ _ P b u v h g k c).1.trans_lt (by norm_num)) (bow_ok c b u h k).2 ((roof_l c L P b u v h g k).trans_lt (by norm_num)) (bow_val c b u h k).2.1 (bow_val c b v g k).2.1 (bow_full c b u h k)
-- logs equality along connecting arc, maintain full root
lemma move_l {x y : Cue m} (h : EdgeP m B U x y) (g : EdgeP m B V x y) : salaryL m B U V c x+amount m B c V x y= salaryL m B U V c y+amount m B c U x y := by
  let a:= twin m x y; let B₀ := Knot; let t₀ := stick (0:Row); let t₁ := stick (1:Row); let l:= zone B₀
  let P':=lens m B c U; let Q:=lens m B c V; let F:= bow m B U a; let G := bow m B V a
  have ht : t₀∈l := stick_in _ (by simp [B₀,Knot]); have hv : t₁∈l := stick_in _ (by simp [B₀,Knot]);
  let s (t:Sq) := spark P' (F t) (body Q (G t))
  let u':= ray m B c U a t₀; let v':= ray m B c V a t₀
  have he (t) (k:t∈l) : ContinuousAt s t := by
    have hB : ContinuousAt F t := (bow_at b u (show Verified _ _ _ _ _ B₀ from h) k).comp (f:=fun y=>(U,a,y)) (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt
    have hC : ContinuousAt G t := (bow_at b v (show Verified _ _ _ _ _ B₀ from g) k).comp (f:=fun y=>(V,a,y)) (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt
    exact (spark_contAt (bow_ok c b u (show Verified _ _ _ _ _ B₀ from h) k).2 ((roof_l c L P b u v h g k).trans_lt (by norm_num))).comp (f:=fun x=>(P',F x,body Q (G x))) (continuousAt_const.prodMk (hB.prodMk ((continuousAt_const.mul hC).mul continuousAt_const)))
  have hU : ContinuousOn u' l:= ray_contzone c b u (show Verified _ _ _ _ _ B₀ from h) ht
  have hV : ContinuousOn v' l:= ray_contzone c b v (show Verified _ _ _ _ _ B₀ from g) ht
  have hs : s t₀+v' t₁=s t₁+u' t₁ := by
    have hy := carry_log (cube_path B₀).isPreconnected ((continuousOn_const (c:=s t₀)).add hV) ((show ContinuousOn s l from fun t k=>(he t k).continuousWithinAt).add hU) t₀ ht
    refine hy ?_ ?_ t₁ hv
    · intro t k; let w:= filled P' (F t₀)
      have ha i (p:i∈l) : acts (lineOp (n:=Mind m B) P') (filled Q (G i))=Complex.exp (s i) • filled P' (F i):= poly_l c L P b u v h g p
      apply smul_left_injective ℂ (show w≠0 from bow_full c b u h ht)
      change Complex.exp (s t₀+v' t) • w= Complex.exp (s t+u' t) • w; rw [add_comm (s t₀), Complex.exp_add,Complex.exp_add, ←smul_smul, ←smul_smul];
      rw [show Complex.exp (s t₀) • w=_ from (ha t₀ ht).symm,←map_smul, show Complex.exp (u' t) • w=_ from ray_filled c b u h ht k, show Complex.exp (v' t) • filled _ _=_ from ray_filled c b v g ht k, ha t k] -- tune
    change s t₀+v' t₀=s t₀+u' t₀; have hx : u' t₀=0 := add_eq_left.mp (ray_add c b u h ht ht ht |>.symm); have hz : v' t₀=0 := add_eq_left.mp (ray_add c b v g ht ht ht|>.symm); rw [hx,hz]
  unfold s F G at hs
  have h₁ i : bow m B i a t₀=pair m B i x:= spot_pair _ _ (fun j=>by simp [a,Phase.twin,capRow,slot]) i
  have h₂ i : bow m B i a t₁=pair m B i y := spot_pair _ _ (fun j=>by simp [a,Phase.twin,capRow,slot]) i
  rw [h₁,h₁,h₂,h₂] at hs; exact hs
omit L P v
lemma fund_log {x y : Cue m} (h : ZeroF m B U x) (k : ZeroF m B U y) : Phase.fund m B c U x+logs m B c U x y=Phase.fund m B c U y := by
  let s:= logs m B c U x y; let f:= Phase.fund m B c U
  have he : Complex.exp (f x+s)=Complex.exp (f y) := by
    apply smul_left_injective ℂ (show sound m B c U ≠0 from fun h=>by have ht := (unity c b u).2; rw [h,norm_zero] at ht; exact zero_ne_one ht)
    dsimp only; rw [add_comm (f x),Complex.exp_add,←smul_smul,show Complex.exp (f x) • _=_ from (afield c b u h).symm, show Complex.exp (f y) • _=_ from (afield c b u k).symm]; exact log_fill c b u x y h k
  have ht := transpose_mean c b U u x y h k
  apply Complex.ext
  · exact Real.exp_injective (by rw [←Complex.norm_exp,←Complex.norm_exp,he])
  simp [Phase.fund,←ht]
include L P v
lemma kink {x y:Cue m} (h:law m B U x≠0) (k:law m B U y≠0) : subject m B U V c x=subject m B U V c y := by
  obtain ⟨s,q,w⟩:=passArch L.licit P x y h k
  have he:=fund_log c b u (law_rich m B _ x h) (law_rich m B _ y k); have hf:=fund_log c b v (passed L.licit P x h) (passed L.licit P y k)
  have hp : logs m B c V x y-logs m B c U x y=salaryL m B U V c y-salaryL m B U V c x := by
    have hx:= move_l c L P b u v q.1 w.1; have ht:= move_l c L P b u v q.2 w.2
    rw [echoes c b u x y s q,echoes c b v x y s w,bill,bill]; linear_combination hx-ht -- sign?
  unfold subject; rw [←he,←hf]; linear_combination hp -- tune
lemma reason {x : Cue m} (h : law m B U x≠0) : Complex.exp (subject m B U V c x)= inner ℂ (sound m B c U) (sound m B c V) := by
  let A:=lens m B c U; let t := slot m x
  have hx:=law_rich _ _ _ x h; have hy:=passed L.licit P x h
  let p:=stick (0:Row); have hk : p∈zone {0}:= stick_in _ (mem_singleton_self _)
  have he := poly_l c L P b u v hx hy hk
  let Y:= sound m B c U; let Y':= sound m B c V; let z:= Complex.exp (salaryL m B U V c x); let a:=Complex.exp (Phase.fund m B c U x); let i:=Phase.fund m B c V x
  have ht : Complex.exp i*inner ℂ Y Y'=z*a := by
    apply smul_left_injective ℂ (show Y≠0 from fun h=>by have ht : ‖Y‖=1 := (unity c b u).2; rw [h,norm_zero] at ht; exact zero_ne_one ht)
    dsimp only; unfold Y; rw [←smul_smul,←smul_smul,← (unity c b u).scalar (lensP c b u) Y',←map_smul, show Complex.exp i • Y'=_ from (afield c b v hy).symm,show a • sound m B c U=_ from (afield c b u hx).symm]; exact he -- tune
  change Complex.exp (_-i)= _; rw [Complex.exp_sub,Complex.exp_add]; change z*a/_= _; rw [←ht,mul_comm (Complex.exp i),mul_div_cancel_right₀ _ (Complex.exp_ne_zero _)]
end
end YM.CF.Delta
