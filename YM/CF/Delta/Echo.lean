import YM.CF.Delta.Sway

/-! Extensive log transport for nearby link sets. Pair of gauges acts simultaneously. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Delta
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock SU Lat Cube Phase Phase.Sample NormedSpace Branch Tenant Function Finset MeasureTheory Filter Lattice Petal Ave Manifest
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {W : Scroll m B c} {e p K a u : ℝ}
def basef {c : Phase.Part m B} (W : Scroll m B c) (S : Stamp m B) (x : Mkt m B e p) := W.value S none (release (eastK x))-W.value S none (release (westK x))
lemma rated (L : ScaleK a u W) (b : Room B e) (l : Wood B p) (S : Stamp m B) : Delta.Coin S (basef (e:=e) (p:=p) W S) (2*W.mint S) := by
  have he := currency L b S none; have ht : ContinuousOn (basef W S) (trainP m B e p) :=
    (he.cont.comp ((releaseCt.comp east_cont).continuousOn) (fun _=> furn)).sub (he.cont.comp ((releaseCt.comp west_cont).continuousOn) (fun _=> yarn l))
  apply mintCoin S _ (mul_nonneg (by norm_num) he.pos) ht
  · intro x h; rw [two_mul]; exact (norm_sub_le ..).trans (add_le_add (he.norm _ (furn h)) (he.norm _ (yarn l h)))
  · intro x t y v g h p; exact congrArg₂ (·-·) (he.matched _ _ trivial (furn t) (furn v) p g) (he.matched _ _ trivial (yarn l t) (yarn l v) p h)
  · intro x p g; exact congrArg₂ (·-·) (he.gaugeEq (release (eastK x)) g (furn p)) (he.gaugeEq (release (westK x)) g (yarn l p))
  intro x p h; exact sub_eq_zero.mpr (he.matched _ _ trivial (furn p) (yarn l p) (fun _ _=>rfl) h)
lemma plusCoin {f g : Mkt m B e p→ℂ} {S T} (h : Delta.Coin S f a) (k : Delta.Coin S g T) : Delta.Coin S (fun x=> f x+g x) (a+T) := by
  refine ⟨⟨add_nonneg h.1.price k.1.price,h.1.pad,fun x g=>(norm_add_le ..).trans (add_le_add (h.1.avail x g) (k.1.avail x g)),fun _ _=> Algebra.mem_top,h.1.ct.add k.1.ct, h.1.records, fun y w l e=> congrArg₂ _ (h.1.same y w l e) (k.1.same y w l e),fun p=>h.1.weights p,fun g x p=> by rw [map_add, h.1.attire g x p,k.1.attire g x p]⟩,fun i l p=> by dsimp only; rw [h.2 i l p,k.2 i l p,zero_add]⟩
structure Flow (m B : Side) (e p v K : ℝ) (c : Phase.Part m B) (F : Acres m→Letters m B e p→ℂ) (w : Acres m→ℝ) : Prop where
  paid : Charge (Mail m B e p) (terr _) v K F w
  vanishes S x : Agrees (mount m B S) x.val.1.val x.val.2.val → F S x=0
  size x : Complex.exp (∑ i,F i x)=inner ℂ (sound m B c x.val.1.val) (sound m B c x.val.2.val)
lemma blossoms (U : Wood B p) (b : Room B e) (c : Phase.Part m B) (F : Mkt m B e p→ℂ) (v : ∀ t∈ trainP m B e p, F t=subject m B t.1.val.1.val t.1.val.2.val c t.2) (x : Letters m B e p) : Complex.exp (motor (wagon m B e p) F x) = inner ℂ (sound m B c x.val.1.val) (sound m B c x.val.2.val) := by
  let A:= x.val.1.val; let B':= x.val.2.val
  obtain ⟨z,H⟩ : ∃ z:Cue m, law m B A z ≠0 := by by_contra! k; have he:= rain_law m B A; simp_rw [k, integral_zero] at he; exact zero_ne_one he
  let V:=subject m B A B' c z; let K:= wagon m B e p
  have he y : law m B A y • F (x,y)=law m B A y • V := by
    by_cases h:law m B A y=0
    · rw [h,zero_smul,zero_smul]
    rw [v _ (show (x,y)∈trainP m B e p from h),show subject m B A B' c y=V from kink c U x.property b x.val.1.property x.val.2.property h H] -- tune
  have hp : motor K F x=V := by change ∫ i,law m B A i • F _ ∂ rains m=V; simp_rw [he,integral_smul_const,rain_law,one_smul]
  change Complex.exp (motor K F x)=_; rw [hp]; exact reason c U x.property b x.val.1.property x.val.2.property H
lemma cascade (U : Wood B p) (b : Room B e) (c : Phase.Part m B) (F : Stamp m B→ Mkt m B e p→ℂ) (C : Stamp m B→ℝ) (q : ∀ S, Delta.Coin S (F S) (C S)) (a : ℝ) (g : ∀ x, cellHit m B a C x ≤ K) (h : ∀ S,C S≠0→ Grove (terr _) S) (P : ∀ t∈trainP m B e p, ∑ S,F S t=subject m B t.1.val.1.val t.1.val.2.val c t.2) : ∃ v w, Flow m B e p a K c v w := by -- Binder shadow
  let B' := wagon m B e p; let H (S) := motor B' (F S); let E (X:Acres m):= dest (pavilion m B) X
  have W S : Token (Mail m B e p) (pavilion m B S) (H S) (C S) (Grove (terr _)) := ⟨(q S).1.price,fun q=>pad_grove (m:=m) (B:=B) (h S q),(q S).1.flush.gram,fun v=>(q S).1.flush.locality v,(q S).1.flush.owns,(q S).1.flush.ct, (q S).1.flush.dress⟩ -- tune
  let f (i:Acres m) (x) := ∑ j∈E i,H j x; let w i:=∑ j∈E i,C j
  refine ⟨f,w,⟨fun S=> Token.mass _ _ _ (fun i p=> by rw [←show pavilion m B i=S from (mem_filter.mp (show i∈E S from p)).2]; exact W i),fun x=> ?_⟩,fun S x hp=>?_,fun x=>?_⟩ -- tune
  · rw [show hitE a w x= _ from codify_hit m B C x a]; exact g x
  · apply sum_eq_zero; intro i h; rw [←show pavilion m B i=S from (mem_filter.mp h).2, mount_p] at hp
    unfold H motor; apply integral_eq_zero_of_ae _; apply Eventually.of_forall; intro v -- tune
    change fall (B'.seat x) v • F i (x,v) = 0; by_cases g : (x,v)∈trainP m B e p; rw [show F i (x,v)=0 from (q i).2 (x,v) g hp, smul_zero]; change ¬ fall (B'.seat x) v ≠ 0 at g; rw [not_not] at g; rw [g,zero_smul] -- tune
  apply Eq.trans _ (blossoms U b c (fun x=>∑ S,F S x) P x)
  unfold f E; rw [← lump (pavilion m B) (fun i=>H i x)]; apply congrArg Complex.exp; unfold H motor bet; simp_rw [smul_sum]; rw [integral_finsetSum]
  exact fun i _=> net_compact ((q i).1.cashG x)
-- combine with thresholds
lemma flowerV (v : ℝ) (g : 0<v) : ∃ N:ℕ,∀ B:Side,N≤B.val→ ∃ p K:ℝ,0<p∧ ∀ e:ℝ, Room B e→∀ m c, ∃ F w, Flow m B e p v K c F w := by
  obtain ⟨a,d,pa,pD,A⟩:= tours _ ampleR rising; obtain ⟨u,M,h,hM,P⟩:=composeK
  let c := min a u; have h':0<c:=lt_min pa h; obtain ⟨N,G⟩:=exists_nat_gt (v*21^4/c)
  refine ⟨N,?_⟩; intro B e; obtain ⟨p,hp⟩:=slip B
  let m' := d+ 2*(M+(way B:ℝ)*M); have hf : 0≤m':= by unfold m'; positivity
  refine ⟨p,Real.exp (v*21^4)*(16*(7*(B.val:ℝ)+1)^4*m'),hp.pos,?_⟩; intro t b m k
  obtain ⟨W,F⟩:=P m B k; let z := codify (m:=m) (B:=B) k; obtain ⟨Y,C,X,Z⟩:= A z
  let D (S:Stamp m B) (x:Mkt m B t p) := speedL hp b k (Y S) x+basef W S x
  let K (S : Stamp m B):= C S+2*W.mint S
  have he S : Delta.Coin S (D S) (K S) := plusCoin (speed_cost hp b (z:=S) (c:=k) (h:=X.stamped S)) (rated F b hp S)
  have hy S (g:K S≠0) : Grove (terr _) S := by
    have hx : Element (binS z) S (C S) (Y S) := X.stamped S
    by_cases u:C S=0
    · apply (currency F b S none).connect; intro v; apply g; unfold K; rw [u,v, mul_zero,zero_add]
    exact hx.conduct u
  have H i : hitE c K i≤ m' := by
    -- use add costs without defeq
    let y : Stamp m B→ℝ := fun S=>C S
    have hk : hitE a y i≤ d:= X.payline i; have ht:=Scroll.covers F i
    have hv (v : Stamp m B→ℝ) (p : ℝ) (e:c≤p) (g : ∀ S,0≤v S) : hitE c v i ≤ hitE p v i := sum_le_sum fun S _=>mul_le_mul_of_nonneg_right (rent_up e _) (g S)
    apply le_trans (le_of_eq (show hitE c K i=hitE c y i+2*hitE c W.mint i from ?_)) -- tune
    · exact add_le_add ((hv y _ (min_le_left ..) (fun S=> (X.stamped S).posT)).trans hk) (mul_le_mul_of_nonneg_left ((hv _ _ (min_le_right ..) (fun S=>(currency F b S none).pos)).trans ht) (by norm_num))
    unfold hitE; rw [mul_sum,←sum_add_distrib]; apply sum_congr rfl; intro S _; unfold K y; ring
  apply cascade hp b k D K he v _ hy
  · intro y l; let s:=silver hp b k ⟨y,l⟩
    have hx : ∑ S:Stamp m B,(Y S s - Y S (againK z s))/2=salaryL m B y.1.val.1.val y.1.val.2.val k y.2 := by
      let f (S:Stamp m B):TwinK z→ℂ:=Y S
      change ∑ i:Stamp m B,(f i s - f i (againK z s))/2=_; rw [←sum_div,sum_sub_distrib]
      rw [show (∑ S:Stamp m B,f S (againK z s))=0 from (Z (againK z s)).symm.trans (cashR z s),sub_zero]; apply congrArg (· / 2); exact (Z s).symm.trans (tally_log (A:=riseW z s-1) ((riseR z s).trans_lt (by norm_num))).symm -- tune
    change ∑ S:Stamp m B, (speedL hp b k (Y S) y+basef W S y)=_
    rw [sum_add_distrib]; simp_rw [speed_at hp b l,basef]; rw [sum_sub_distrib, taxed F b (furn l),taxed F b (yarn hp l),show (∑ S:Stamp m B,(Y S s - Y S (againK z s))/2)=_ from hx]; exact (add_sub_assoc ..).symm
  intro x; have hv : v*21^4 ≤ c*(B.val:ℝ) := (le_of_lt ((div_lt_iff₀ h').mp G)).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast e) h'.le)
  exact hit_transfer g.le hv hy (fun S=>(he S).1.price) H hf x
end YM.CF.Delta
