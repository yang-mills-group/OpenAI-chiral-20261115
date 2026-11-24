import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic
/-! Gaussian price as polynomial in NONSELF covariance. Prove a tilted version to facilitate derivatives.
  Used on the actual homogeneous path models; vectors may NOT have bounded norm (self contractions
  can diverge in the usage of this lemma).
-/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.RoseGaussian
open Function MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal InnerProductSpace
variable {I X : Type*}
-- remove one potential partner from the rest.
def slit (C : I → ℂ) (K : List I → ℂ) (l : List I) : ℂ := match l with
 | [] => 0
 | a::l => C a * K l + slit C (fun t => K (a::t)) l

lemma slit_map (f:I → X)(l : List I)(K : List X → ℂ) (C : X → ℂ) : slit C K (l.map f)=slit (C∘ f) (fun t=> K (t.map f)) l:=by
  induction l generalizing K with|nil=>rfl|cons i l p=> rw [List.map_cons,slit,p,slit]; rfl

lemma slit_scale (C:I→ℂ)(K:List I→ℂ)(l:List I)(z:ℂ) : slit C (fun t=> z*K t) l=z*slit C K l:=by
  induction l generalizing K with
  | nil=>simp [slit]
  | cons a l p=> rw [slit, slit,p (fun t=> K (a::t))]; ring
lemma slit_dep {C D:I→ℂ}{K K': List I→ℂ} (l:List I) (p:∀ i∈l,C i=D i) (t:∀ l':List I,l'.Sublist l → l'.length+1=l.length → K l'=K' l') : slit C K l=slit D K' l := by
  induction l generalizing K K' with
  | nil=> rfl
  | cons a l h=> rw [slit,slit,p a List.mem_cons_self,t l (.cons a (.refl ..)) rfl]; exact congrArg₂ (·+·) rfl (h (fun i v=>p i (List.mem_cons_of_mem _ v)) (fun l v e=> t _ (v.cons_cons _) (by simp [e])))

-- use depth-index versions to simplify the equations. payments with n >= list.length.
def exchange (C : I → I → ℂ) (n:ℕ) (l:List I) : ℂ := match n,l with
 | _,[]=>1
 | 0,_::_=>0
 | n+1,a::t => slit (C a) (exchange C n) t
lemma exchange_map (f:I→X)(l:List I)(K:X→X→ℂ)(n:ℕ) : exchange K n (l.map f)=exchange (fun i j=> K (f i) (f j)) n l:=by
  induction n generalizing l with
  | zero=> cases l <;> rfl
  | succ n h =>
    cases l with
    | nil=> rfl
    | cons a l => rw [List.map_cons,exchange,slit_map,exchange]; exact slit_dep _ (fun _ _=> rfl) (fun l _ _=> h l)

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
local notation "μZ" => stdGaussian X
abbrev cost (x y:X) : ℂ := inner ℝ x y
noncomputable abbrev phase (t x : X) : ℂ := Complex.exp (cost x t * Complex.I)
noncomputable def path (l:List X)(z:X) : ℂ:= (l.map fun i=> cost i z).prod
lemma path_step (l:List X)(x y:X) : path (x::l) y=cost x y * path l y:= rfl
private lemma path_ink (l:List X) : Continuous (path l) := by
  induction l with
  | nil=> exact continuous_const
  | cons a l t=> exact (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id) |>.mul t : Continuous (fun x:X=> cost a x*path l x))
private lemma path_price (l:List X)(x:X) : ‖path l x‖ ≤ (l.map norm).prod * ‖x‖^l.length:=by
  induction l with
  | nil=> simp [path]
  | cons a l p=>
    rw [path_step,norm_mul,List.map_cons,List.prod_cons,List.length_cons,pow_succ]; refine (mul_le_mul (le_trans (b:=‖inner ℝ a x‖) (Complex.norm_real _|>.le) (norm_inner_le_norm ..)) p (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
lemma path_read (l:List X) : Integrable (path l) μZ:=by
  refine (((IsGaussian.memLp_id μZ (l.length:ℕ) (by simp)).integrable_norm_pow').const_mul (l.map norm).prod).mono' (path_ink _|>.aestronglyMeasurable) (Eventually.of_forall (path_price l))
private lemma phase_norm (y z:X) : ‖phase y z‖=1:=Complex.norm_exp_ofReal_mul_I _
private lemma hill (a:X)(l:List X) : Integrable (fun x=>phase a x * path l x) μZ:=
  (path_read l).norm.mono' (by have h:= path_ink l; unfold phase cost; fun_prop) (by filter_upwards with z; rw [norm_mul, phase_norm,one_mul])
noncomputable def reading (a:X) (l:List X):= ∫ x,phase a x*path l x∂μZ

private lemma climb (a b:X) : HasDerivAt (fun t:ℝ => a + t • b) b 0 := by
  convert ((hasDerivAt_id' (0:ℝ)).smul_const b).const_add a using 1; simp

private lemma ripples (a b:X)(l:List X) : HasDerivAt (fun t:ℝ=>reading (a+t • b) l) (Complex.I * reading a (b::l)) 0 := by
  let τ(t:ℝ) := a+t • b; let f (u:List X)(t:ℝ)(x:X):=phase (τ t) x * path u x
  let g(t:ℝ)(x:X) := Complex.I * f (b::l) t x; let V:=path (b::l)
  have he:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μZ) (F:=f l) (F':=g) (x₀:=0)
    (s:=Set.univ) (bound:= fun x=> ‖V x‖) (by simp) (Eventually.of_forall fun i=> hill _ _|>.aestronglyMeasurable) (hill ..)
    (((hill (τ 0) (b::l)).const_mul Complex.I).aestronglyMeasurable) (ae_of_all _ fun i t _=> le_of_eq (by simp only [g,f,norm_mul, phase_norm, norm_I,one_mul,V])) ((path_read (b::l)).norm) ?_
  · have ht: reading a (b::l)=∫ x:X,f (b::l) 0 x ∂μZ:= by simp_rw [reading,f,τ,zero_smul,add_zero]
    rw [ht, ←integral_const_mul]; exact he.2
  · filter_upwards with x t _; let c(t:ℝ) := inner ℝ x (τ t)
    have h: HasDerivAt c (inner ℝ b x) t:=by
      simp_rw [c,τ,inner_add_right,real_inner_smul_right]
      rw [real_inner_comm b x]; simpa [real_inner_comm] using (((hasDerivAt_id' t).mul_const (inner ℝ x b)).const_add (inner ℝ x a))
    convert (((h.ofReal_comp).mul_const Complex.I).cexp.mul_const (path l x)) using 1
    all_goals first|rfl|(simp only [c,g,f,phase,path_step,cost]; ring)

private lemma trade_term (B:I→ℂ)(G:List I→ ℂ)(H: List I→ℝ→ℂ)(h:∀ v, HasDerivAt (H v) (G v) 0) (l:List I) :
    HasDerivAt (fun x:ℝ=> slit B (fun v=> H v x) l) (slit B G l) 0 := by
  induction l generalizing H G with
  | nil=> exact hasDerivAt_const ..
  | cons a l p=> exact ((h l).const_mul _).add (p _ _ (fun v=> h (a::v)))
-- add no base mismatch charfun orientation mathlib exp.. cp order E4.
lemma trade (b a:X)(l:List X) : reading a (b::l)=Complex.I * cost a b * reading a l + slit (cost b) (reading a) l := by
  induction l generalizing a with
  | nil=>
    have h(x:X):reading x []=Complex.exp (-((inner ℝ x x:ℝ):ℂ)/2) := by
      rw [reading]; simp_rw [path,List.map_nil,List.prod_nil,mul_one]; rw [←MeasureTheory.charFun_apply, charFun_stdGaussian,real_inner_self_eq_norm_sq]; norm_cast
    let g(t:ℝ) := a+t • b; let V(t:ℝ) := -inner ℝ (g t) (g t)/2
    have hf : HasDerivAt (fun t:ℝ=> -(↑(inner ℝ (g t) (g t)):ℂ)/2) (-cost a b) 0 := by
      have ht:= climb a b; convert (((ht.inner ℝ ht).ofReal_comp).neg.div_const (2:ℂ)) using 1 <;> first | rfl | (simp [real_inner_comm b a,cost]) -- tune
    have he:=ripples a b []; change HasDerivAt (fun t:ℝ=> reading (g t) []) _ _ at he; simp_rw [h] at he; have hu:= he.unique hf.cexp
    apply mul_left_cancel₀ Complex.I_ne_zero; rw [hu]; simp [h,cost, slit,g, ←mul_assoc Complex.I]; ring
  | cons y l p =>
    let g(t:ℝ) := a+t • y
    have ht : (fun t:ℝ=> reading (g t) (b::l))= (fun t:ℝ=>Complex.I * cost (g t) b * reading (g t) l + slit (cost b) (reading (g t)) l):=funext fun t=>p _
    have hy := ripples a y (b::l); change HasDerivAt (fun t:ℝ=> reading (g t) (b::l)) _ _ at hy
    rw [ht] at hy
    have h1 : HasDerivAt (fun t:ℝ => cost (g t) b) (cost b y) 0:=by
      have hv:= ((climb a y).inner ℝ (hasDerivAt_const (x:= (0:ℝ)) b)).ofReal_comp; simpa [cost,real_inner_comm b y] using hv
    let X':=trade_term (G:=fun v=>Complex.I * reading a (y::v)) (cost b) (fun v t=>reading (g t) v) (fun v=> ripples a y v) l -- tune
    have he:=hy.unique ((((h1.const_mul _).mul (ripples a y l))).add X')
    have hh : reading a (y::b::l)=reading a (b::y::l) := integral_congr_ae (Eventually.of_forall fun x=> by simp only [path_step]; ring)
    simp only [g,zero_smul,add_zero,hh, slit_scale] at he
    rw [slit]; apply mul_left_cancel₀ Complex.I_ne_zero; rw [he]; ring_nf

lemma reading_equal (l:List X) : reading 0 l=∫ x, path l x∂μZ:=by simp [phase,cost,reading]
lemma exchange_read (n:ℕ)(l:List X)(h:l.length≤n) : reading 0 l=exchange cost n l:=by
  have hh:reading (0:X) []=1:=by simp [reading_equal,path]
  induction n generalizing l with
  | zero=> rw [show l=[] from List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h),hh]; rfl
  | succ n p=>
    cases l with
    | nil=>exact hh
    | cons a l =>rw [trade a,exchange,show cost (0:X) a=0 by simp [cost],mul_zero,zero_mul,zero_add]; apply slit_dep _ (fun _ _=>rfl); exact fun i _ e=> p _ (by rw [List.length_cons] at h; omega)
lemma primitive (n:ℕ)(F:I→X)(l:List I)(p:l.length≤n) :
    (∫ x,path (l.map F) x∂μZ)=exchange (fun i j=>cost (F i) (F j)) n l:=by rw [←exchange_map F l cost n,←reading_equal]; apply exchange_read; simpa using p

section follow
variable (C D:I→I→ℂ) {R : I→I→ Prop}
lemma slit_follows {X Y:I→ℂ}(p :I→ Prop)(h:∀ i,p i → X i=Y i) {K K':List I→ℂ} (l:List I)(v:∀ i∈l,p i)(t:∀ i:List I,i.Sublist l→ K i=K' i) : slit X K l=slit Y K' l:= slit_dep _ (fun i p=> h i (v i p)) (fun i p _=> t i p)
lemma exchange_follows (p:∀ i j,R i j→ C i j=D i j)(l:List I)(h:l.Pairwise R)(n:ℕ): exchange C n l=exchange D n l:=by
  induction n generalizing l with
  | zero=> cases l<;>rfl
  | succ n ih=>
    cases l with
    |nil=>rfl
    |cons i l=> obtain ⟨a,b⟩:= List.pairwise_cons.mp h; exact slit_follows (R i) (p i) l a (fun l e=> ih l (b.sublist e))
-- independence of separate price blocks, needed to get onto the elected character
private lemma exchanges (n m:ℕ)(l:List I)(v:l.length≤ n)(w:l.length≤ m): exchange C n l=exchange C m l:=by
  induction n generalizing l m with
  | zero=> have he:l=[]:=List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero v); rw [he]; cases m<;>rfl
  | succ n ih=>
    cases l with
    | nil=>cases m<;>rfl
    | cons i l=> cases m with
      | zero=> rw [List.length_cons] at w; omega
      | succ m=> exact slit_dep _ (fun i _=>rfl) (fun l _ h=>ih _ _ (by simp only [List.length_cons] at v; omega) (by simp only [List.length_cons] at w; omega))
private lemma slit_empty {f:I→ℂ}(l:List I)(K : List I→ℂ)(u:∀ i∈l,f i=0) : slit f K l=0:=by induction l generalizing K with| nil=>rfl|cons i l ih=> rw [slit,u i List.mem_cons_self,ih (fun t=> K (i::t)) (fun i h=>u i (List.mem_cons_of_mem _ h)),zero_mul,zero_add]
lemma slit_zone (K:List I→ℂ)(f:I→ℂ)(l m:List I)(u:∀ i∈m,f i=0): slit f K (l++m)=slit f (fun x=> K (x++m)) l:=by
  induction l generalizing K with| nil=> exact slit_empty m K u|cons i l ih=>rw [List.cons_append,slit,ih,slit]; rfl
lemma exchange_split (n:ℕ)(l m:List I)(h:l.length+m.length≤n)(t:∀ i∈l,∀ j∈m,C i j=0): exchange C n (l++m)=exchange C n l*exchange C n m:=by
  induction n generalizing l with
  | zero=>
    rw [show l=[] from List.length_eq_zero_iff.mp (by omega)]; simp [exchange]
  | succ n ih=>
    cases l with
    | nil=> simp [exchange]
    | cons a l =>
      rw [List.length_cons] at h
      rw [exchanges C _ n m (by omega) (by omega), List.cons_append, exchange,exchange, slit_zone _ _ _ _ (t a List.mem_cons_self),mul_comm,←slit_scale]
      refine slit_dep _ (fun i _ => rfl) (fun i e k=> (ih i (by omega) fun a v=> t a (List.mem_cons_of_mem _ (e.subset v))).trans (mul_comm ..))
lemma slit_limit {X : Type*} (q:Filter X) {F:X→List I→ℂ} {g:List I→ℂ} {Z:X→I→ℂ}{C:I→ℂ}(l:List I)(h:∀ i∈l,Tendsto (fun t=> Z t i) q (𝓝 (C i)))(e:∀ l', List.Sublist l' l→ Tendsto (fun i=> F i l') q (𝓝 (g l'))) : Tendsto (fun i=>slit (Z i) (F i) l) q (𝓝 (slit C g l)):=by
  induction l generalizing F g with
  | nil=> exact tendsto_const_nhds
  | cons i l ih=> exact ((h i List.mem_cons_self).mul (e _ (List.sublist_cons_self ..))).add (ih (g:=fun t=>g (i::t)) (F:=fun v t=> F v (i::t)) (fun i p=>h i (List.mem_cons_of_mem _ p)) (fun k p=> e _ (p.cons_cons i)))
lemma exchange_limit {X:Type*}(q:Filter X)(D:X→I→I→ℂ)(l:List I)(n:ℕ)(h:l.Pairwise (fun i j=> Tendsto (fun t=> D t i j) q (𝓝 (C i j)))) : Tendsto (fun i=>exchange (D i) n l) q (𝓝 (exchange C n l)):=by
  induction n generalizing l with
  | zero=> cases l<;> exact tendsto_const_nhds
  | succ n ih=>
    cases l with
    | nil=> exact tendsto_const_nhds
    | cons a l => obtain ⟨h,p⟩:= List.pairwise_cons.mp h; exact slit_limit q (F:=fun i=>exchange (D i) n) l (Z:=fun i=> D i a) h (fun v t=> ih v (p.sublist t))
end follow
#print axioms primitive
end YM.RoseGaussian
