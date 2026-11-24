import YM.CF.BProof.Grid.Blend

/-! # dyadic price recursion. Duplicate the labels of corners when on smaller faces; those
give the very same equal-weight mean. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid.Blend
open Function MeasureTheory Lattice Finset Entity
open scoped Matrix.Norms.Frobenius BigOperators Classical
variable (G : Gauge) (n:ℕ)

private def exchange (i : Fin n) : Dice n ≃ Dice n where
 toFun b:=update b i (!b i)
 invFun b:=update b i (!b i)
 left_inv b:=by simp
 right_inv b:=by simp

lemma half {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X] (A B:Dice n→X)(i:Fin n)(b:Bool)(c:ℝ)
    (h:∀ a, if a i=b then A a=B a else ‖A a-B a‖≤c) : ‖average A-average B‖ ≤ c/2:=by
 let C (a):= A a-B a; let s:=exchange n i; let y:= average C
 have he : average (C ∘ s)=y := by unfold y average; simp only [Function.comp_apply]; rw [Equiv.sum_comp s C] -- tune
 have hm := @average_le (Dice n) _ _ X _ _ (fun x=>C x+C (s x)) c (by
    intro a; have hu:=h a; have hv:=h (s a); rw [show s a i= !(a i) from update_self ..] at hv; unfold C; cases hp:a i <;> cases b <;> simp_all)
 rw [← average_sub]; change ‖y‖ ≤ _; have hx : average (fun x=>C x+C (s x))=(2:ℝ) • y := by rw [two_smul]; exact (average_add C (C ∘ s)).trans (show _ from by rw [he]) -- ℕ
 rw [hx,norm_smul] at hm; norm_num at hm; linarith -- `norm_nsmul`

variable {n} {c s : Side} (g: Ratio c s) (U : Wire G n s) (Q : Floor G.El n c)
local notation "M" => G.mat
local notation "V" => G.colorScale

private abbrev Form (n : ℕ)(m a:ℝ) := 16*n^2*m + (a+4*n*m)*(2*n)

lemma recur {m a : ℝ} (hc:4 ≤ c.val)(ht:g.count.val=2)(hm:0≤m)(ha:0≤a)
    (H:Wire.Flat G U Set.univ m)(h:SeatBound G Q (Wire.long G U g) a)
    (C:ℝ)(hv:∀ (F:Dice n→G.El) (e v : G.El), (∀ i,cd G e (F i) ≤ Form n m a) → G.Nearest v (average (G.mat ∘ F)) → ‖average (G.mat ∘ F)-G.mat v‖ ≤ C*(Form n m a)^2):
    SeatBound G (blend G g U Q) U ((a+4*n*m)/2+2*(16*n^2*m)+ (2*C*(Form n m a)^2)/V+(2*n*m)) := by
 intro x i; obtain ⟨q,u,w⟩:= entire g hc x i
 let p:=Entity.mk q Finset.univ; let T:=p.paths G g U; let f:=blend G g U Q; let y:=slide x i
 let b(z:Cubic n s):= f z*(T z)⁻¹; let A:=shelf G g U Q p
 let B(x):=shifted G g U Q p x
 let L(x:Cubic n s):=average (M ∘ A ∘ eighth g x); let D:=Form n m a
 have hp(z:Cubic n s)(h':p.Mem g z) : ‖M (b z) - L z‖ ≤ C*D^2+(16*n^2*m)*V:=by
    have hl:=hv (B z) (A p.home) (b z) (fares G g U Q p hc ht hm H h ha z h') (by
       change G.Nearest (b z) (average (fun i=>G.mat (book G g U Q z i * _))); rw [right_shift]; exact (G.nearest_right _ _ _).2 (closest_p G _)
    )
    apply (norm_sub_le_norm_sub_add_norm_sub (M (b z)) (average (M ∘ B z)) _).trans; apply add_le_add; rw [norm_sub_rev]; exact hl
    exact average_dist _ _ _ fun i => (norm_le_scale ..).mp (translated G g U Q p hc ht hm H z h' i)
 obtain ⟨j,hj⟩:=clicked g p hc ht x i u w
 have he: ‖L x - L y‖≤(a+4*n*m)*V/2:=by
    refine half _ _ _ i j _ ?_; intro z; have ht':=hj z; change ite _ (_=_) _ at ht'; split_ifs with k; exact congrArg (M ∘ A) (by simpa [k,y] using ht' : eighth g x z=eighth g y z)
    have he : eighth g y z=slide (eighth g x z) i:=by rw [if_neg k] at ht'; exact ht';
    have hv := (dimension g p (eighth g y z)).mp (placed g p hc y z w)
    change ‖M (A _)-M (A _)‖ ≤ _; rw [he] at hv ⊢; exact (norm_le_scale ..).mp (tide G g U Q p hc ht hm H ((dimension ..).mp (placed g p hc x z u)) i hv h)
 have e : cd G (b x) (b y) ≤ (a+4*n*m)/2+2*(16*n^2*m)+ (2*C*D^2)/V:=by
    have hv:= norm_sub_le_norm_sub_add_norm_sub (M (b x)) (L x) (M (b y)); have hq:=norm_sub_le_norm_sub_add_norm_sub (L x) (L y) (M (b y));
    rw [norm_sub_rev (L y)] at hq; apply (norm_le_scale ..).2; have := G.colorScale_pos; field_simp; -- tune
    linarith [hp x u,hp y w] -- nonlinear maybe
 let Z:=U (x,i)
 change cd G (f x * Z) (f y) ≤ _; have H₀:= cd_perturb G (b x) (T x * Z) (b y) (T y)
 apply le_trans (by simpa [b] using H₀ : cd G (f x*Z) (f y) ≤ cd G (b x) (b y)+cd G (T x*Z) (T y))
 apply add_le_add e; apply (p.smooth G g U u w hc hm (fun x i j _ _ _ _=>H x i j trivial trivial trivial trivial)).trans_eq; rw [ht]; push_cast; ring

omit g U Q
lemma stepper (n : ℕ) : ∃ C ε:ℝ,0<C∧ 0<ε∧ ∀ {c s:Side}(g:Ratio c s)(U:Wire G n s)(Q:Floor G.El n c){m a : ℝ},
    4≤c.val→g.count.val=2→0≤m→0≤a→ Wire.Flat G U Set.univ m → SeatBound G Q (Wire.long G U g) a → m+a≤ ε → SeatBound G (blend G g U Q) U (a/2+C*(m+a^2)):=by
 obtain ⟨K,-⟩:= chart_bought G 1 one_pos
 obtain ⟨C,v,hc,hv,H⟩:= average_projection (I:=Dice n) G K
 let κ:ℝ:=16*n^2+(4*n)*(2*n)+2*n+1; have hk:0<κ:=by unfold κ; positivity
 have hh:=G.colorScale_pos
 let c':ℝ:= (2*n+2*(16*n^2)+2*n)+4*C*κ^2/V
 have hh':0≤(2*n+2*(16*n^2)+2*n:ℝ):=by positivity
 refine ⟨c',min 1 (v/κ),add_pos_of_nonneg_of_pos hh' (by positivity),lt_min one_pos (by positivity),fun g U Q m a u t hm ha Φ hz h x i=>?_⟩
 have hl:m≤1:=by linarith only [le_min_iff.mp h|>.1,ha]
 have hp:Form n m a ≤ κ*(m+a):=by unfold Form κ; nlinarith [mul_nonneg (show 0≤(n:ℝ)*n by positivity) hm,mul_nonneg (show 0≤(n:ℝ)*n by positivity) ha,mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) hm,mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) ha]
 apply (recur G g U Q u t hm ha Φ hz C (fun F e q h p=> H F e q _ h (hp.trans (mul_comm κ _ ▸ (le_div_iff₀ hk).mp (le_min_iff.mp ‹_≤min _ _› |>.2))) p) x i).trans
 apply le_trans (b:=(a+4*n*m)/2+2*(16*n^2*m)+(2*C*(κ*(m+a))^2)/V+2*n*m)
 · have ht:0≤Form n m a:=by unfold Form; positivity; 
   gcongr
 have hp':(m+a)^2≤2*(m+a^2):=by nlinarith [sq_nonneg (m-a)]
 have hx:=mul_le_mul_of_nonneg_left hp' (show 0≤2*C*κ^2/V by positivity); unfold c'; simp only [div_eq_mul_inv] at hx ⊢; norm_num at hx ⊢; linarith only [hx, mul_nonneg hh' (sq_nonneg a)]
end YM.CF.BProof.Grid.Blend
