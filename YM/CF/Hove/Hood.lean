import YM.CF.Hove.Over
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable(j m:ℕ)(e:Even j)(p:4 ≤ j)(v:2 ≤ m)
variable {c f:Side}(G:Ratio c f)(w: Odd G.count.val)(T:Script Male)(u:Use j G.count T)(M:Male)(b:Bool)(o:Site f)
variable {i s:Kt}{x y:Cover}
lemma stitch_v (B:Side): lace 1 B=lace 0 B/B.val ∧ lace 2 B=lace 0 B/(B.val:ℝ)^2:=by
 unfold lace; have ht:= side_pos B; constructor <;>field_simp <;>ring
include e p v
lemma portY : ∃ C:ℝ,0<C∧∀ {c f:Side}(G:Ratio c f)(w: Odd G.count.val)(T:Script Male),Use j G.count @T →∀ (b:Bool)(M:Male)(o:Site f)(i:Kt)(x:Cover), recL m (lace 0 G.count) G.count.val C (Laurent.size x) (feeT G m o) (indexF G w T j b M o i) (plyT G w T j b M o i x) (flute G w T j b M o i x):=by
 choose R r H using fun b:Bool=> font_u j m e b p v; choose A s Y using fun b:Bool=> flute_p j e b p; let P(b):= max (R b) (A b)
 let C:= max (P false) (P true); have h0:∀ b,0< P b:=fun b=> lt_of_lt_of_le (r b) (le_max_left ..); refine ⟨C,lt_of_lt_of_le (h0 _) (le_max_left ..),fun {c f} G w T ht b M o i x=>?_⟩
 obtain ⟨a,g,s₀,h⟩:= H b G w T ht M o i x; let L:=G.count; let k₀:=lace 0 L; have hp:0 ≤ k₀:=by unfold k₀ lace; positivity
 let z:ℝ:=Laurent.size x; have hz:0 ≤ z:=Nat.cast_nonneg _; let N:ℝ:= L.val; have hx:1 ≤ N:= by unfold N; exact_mod_cast L.property
 have he:P b≤ C:=by cases b; exact le_max_left ..; exact le_max_right ..
 have hr₀:R b≤ C:= (le_max_left ..).trans he; have hA:A b≤ C:= (le_max_right ..).trans he
 obtain ⟨u1,u2⟩:= stitch_v L
 refine ⟨(Y b G w T ht M o i x).trans (mul_le_mul_of_nonneg_right hA hp),g.trans (mul_le_mul_of_nonneg_right hr₀ hp),s₀.trans ?_,a.trans ?_,h.trans ?_⟩
 · rw [show lace 1 G.count=_ from u1]; refine le_trans (mul_le_mul_of_nonneg_right hr₀ (mul_nonneg (by positivity) (div_nonneg hp (side_pos _).le))) ?_; exact le_of_eq (by ring)
 · change R b * (k₀* (1+ z/N)^m)≤ _; change 0 ≤ lace 0 L at hp; rw [mul_comm k₀]; exact mul_le_mul_of_nonneg_right hr₀ (mul_nonneg (by positivity) hp)
 rw [show lace 2 G.count=_ from u2]; refine le_trans (mul_le_mul_of_nonneg_right hr₀ (mul_nonneg (tw_pos ..) (div_nonneg hp (sq_nonneg _)))) ?_; exact le_of_eq (by unfold tweight; ring)
omit e p v
abbrev portB (s: Single f):Kt:= (s.1.2,s.2)
abbrev ox (s:Single f):Cover:=Lattice.lift (s.1.1-o)
abbrev Qy (a:Bool)(s:Single f):Single c→ℂ:= flute G w T j a M o (portB s) (ox o s)
abbrev Qa (a:Bool)(s: Single f):Single c→ℂ:= indexF G w T j a M o (portB s)
abbrev Qk (a:Bool)(s: Single f):Single c→ℂ:= plyT G w T j a M o (portB s) (ox o s)
def ζw (x:Single f):ℂ:= Rush.wind o (ox o x)
local notation "A'" b:max=> Qy j G w T M o b
local notation "Ψb" b:max=> Qa j G w T M o b
local notation "β'" b:max=> Qk j G w T M o b
local notation "ζτ"=> ζw o
local notation "F_" b:max=> lensF G w T j b M
abbrev bushX(O Q:Single f):= billY ((Ψb false) O) ((Ψb true) Q) ((β' false) O) ((β' true) Q)
variable (L:Op (Single f))
def ζl (x y:Single f):= ζw o x*ζw o y*L x y
def totF : Op (Single c):= (lensF G w T j false M)ᴴ * L * lensF G w T j true M
def pinF (Y:Op (Single c)): Single c ×Single c→ℂ:= Function.uncurry Y
local notation "R_"=> Single f × Single f
local notation "Cc"=> Single c ×Single c
local notation "Δ" k:max=> (Qy j G w T M o k)
local notation "Ξ"=> bushX j G w T M o
local notation "W"=> feeT G m o
local notation "Q_" a:max=> (fun x:Single f=> Qy j G w T M o a x)
abbrev born_H (x:R_):= dishV ((Δ false) x.1) ((Δ true) x.2)
abbrev ΨH (s:R_→Cc→ℂ):=∑ x:R_, ζl o L x.1 x.2 • s x
lemma taxiP: pinF (totF j G w T M L) = ΨH o L (born_H j G w T M o):=by
 ext1 q
 let a(x:R_)(p:Bool):Single f:= if p then x.2 else x.1 -- dummy
 have h(x:Single f)(P:Bool)(k):Qy j G w T M o P x k=ζw o x * ((F_ P) x k):=by unfold Qy flute; rw [show plot (stickW o _) _=x from ?_]; rfl; simp only [plot,ox,wrap_lift,add_sub_cancel]
 unfold totF pinF ΨH born_H; simp only [Function.uncurry_apply_pair,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] -- tune unc
 change (((F_ false)ᴴ * L) * F_ true) q.1 q.2=_; conv_rhs=> rw [Fintype.sum_prod_type,sum_comm]
 rw [Matrix.mul_apply]; apply sum_congr rfl; intro s _; rw [Matrix.mul_apply,sum_mul]; apply sum_congr rfl; intro x _
 change _=ζl o L x s * (star ((A' false) x q.1) * ((A' true) s q.2)); rw [h,h,star_mul,show star (ζw o x)=ζw o x from fee_real _]; rw [ζl, Matrix.conjTranspose_apply]; generalize hx: ζw o x=X; generalize hv:ζw o s=Y; have hp:X^2=1:=by rw [←hx,pow_two]; exact fee_one _
 have he:Y^2=1:=by rw [←hv,pow_two]; exact fee_one _
 change ((star _ * _) * _)=_; ring_nf; rw [hp,he]; ring
local notation "w₀" s:max=> (Laurent.size (ox o s):ℝ)
def opus (x:R_):= (1+ max (Laurent.size (ox o x.1):ℝ) (Laurent.size (ox o x.2):ℝ))^m
def moneyP:= paidX (opus m o) (pinF L)
local notation "η_"=> ΨH o L
include e p v
-- Genuine marked transfer, no transl summing. scale-independent post（） all exact lattice periods, max tariff (PH anchored sector)
lemma thrice : ∃ C:ℝ,0<C∧∀ {c f:Side}(G:Ratio c f)(w:Odd G.count.val)(T:Script Male),Use j G.count @T →∀ (M:Male)(o:Site f)(L:Op (Single f)), paidX (coyF (feeT G m o)) (pinF (totF j G w T M L)- ΨH o L (fun x=>bushX j G w T M o x.1 x.2)) ≤ (C/(G.count.val:ℝ)^5)*moneyP m o L:=by
 obtain ⟨X,y,T_⟩:= portY j m e p v; let C:=2*((2:ℝ)^m+4)*X^2
 refine ⟨C,by unfold C; positivity,fun {c f} G w T h M o L=>?_⟩
 let Q(x:Single f):Cover:= ox o x; let K:=feeT G m o; let Y:=coyF K; let A:=G.count; let k:=lace 0 A; let J(w' :Bool)(i:Single f):= Qy j G w T M o w' i; let H:= ΨH (c:=c) o L -- notation shadow safe?
 have hp:1 ≤ K := feeK G m o; have ht:0≤k:=by unfold k lace; positivity
 have he:0 ≤ Y:=fun i=> add_nonneg (zero_le_one.trans (hp i.1)) (zero_le_one.trans (hp i.2))
 let W'(x:Single f×Single f):= bushX j G w T M o x.1 x.2
 have hx(x:Single f×Single f): let U:=born_H j G w T M o x; paidX Y (U-W' x) ≤ (C/(A.val:ℝ)^5*opus m o x):=by
    intro U; let F(z):=T_ G w T h z M o; let Xv:=Q x.1; let Pv:=Q x.2
    have hA:1 ≤ (A.val:ℝ):=by exact_mod_cast A.property
    refine (hoop m v K _ _ _ _ _ _ k A.val X X _ _ hp hA (Nat.cast_nonneg (Laurent.size Xv)) (Nat.cast_nonneg (Laurent.size Pv)) ht y.le y.le (F false _ Xv) (F true _ Pv)).trans_eq ?_
    change _ * _ * (X*k*(X*k))=_; unfold C k opus lace Xv Pv Q; have h:=side_pos A; field_simp; ring_nf; rw [show Real.sqrt A.val ^2=(A.val:ℝ) from Real.sq_sqrt h.le]; ring
 unfold moneyP; rw [taxiP _ _ _ _ _ o, ΨH, ΨH,←sum_sub_distrib]; simp_rw [← smul_sub]; apply (p_posts _ he _ _).trans; unfold paidX; rw [Finset.mul_sum]; refine sum_le_sum fun i _=>?_ ;  change paidX Y _ ≤ _; rw [p_smul, ζl,norm_mul,norm_mul, show ∀ x,‖ζw o x‖=1 from fun x=>fee_norm _,show ‖ζw o i.2‖=1 from fee_norm _,one_mul,one_mul] -- tune all
 exact (mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _)).trans_eq (by unfold A; rw [mul_comm, mul_assoc]; rfl)
end YM.CF.Hove
