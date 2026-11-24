import YM.CF.BProof.Cabinet.Mint
import YM.CF.BProof.Pods.Inverse
/- Canonical core certificates on active variables, complex logs and costs.
Apply once after Lens etc. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 26000
noncomputable section
namespace YM.CF.BProof.Cabinet
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Pods Posts Brick Account
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)
local notation "mH"=> Y.yard
local notation "g₀"=> Y.g
local notation "B"=> Y.Block
local notation "wB"=>House.Season mH Y.c'
variable (r:ℕ) (x:Pod Y)
structure Shift where
    F : Cores Y r→ Pod Y→ℂ
    m(i) : Measurable (F i)
    T(q:Cores Y r) (x y':Pod Y) : q∈ recital Y r x→q∈ recital Y r y'→ Cabinet.Ready P Y T θ x → Cabinet.Ready P Y T θ y' →Spiced Y (plate Y r q) x y'→ F q x= F q y'
namespace Shift
variable {Y P T θ r} (F W: Shift Y P T θ r)
def add : Shift Y P T θ r := ⟨fun i x=> F.F i x+W.F i x,fun i=>(F.m i).add (W.m i),fun i _ _ v t l u p=> congrArg₂ _ (F.T i _ _ v t l u p) (W.T i _ _ v t l u p)⟩
def mul : Shift Y P T θ r := ⟨fun i x=> F.F i x*W.F i x,fun i=>(F.m i).mul (W.m i),fun i _ _ v t l u p=> congrArg₂ _ (F.T i _ _ v t l u p) (W.T i _ _ v t l u p)⟩
def exponential : Shift Y P T θ r:= ⟨fun i=>Complex.exp ∘ F.F i,fun i=> Complex.continuous_exp.measurable.comp (F.m i),fun i _ _ v t l u p=> congrArg Complex.exp (F.T i _ _ v t l u p)⟩
def amt :=∑ i∈recital Y r x,F.F i x
def resp :=∏ i∈recital Y r x,F.F i x
lemma resp_exp : F.exponential.resp x= Complex.exp (F.amt x):= (Complex.exp_sum _ _).symm -- `Complex.exp_sum T` tune
lemma amt_add : (F.add W).amt x=F.amt x+W.amt x:= sum_add_distrib
lemma resp_mul : (F.mul W).resp x= F.resp x * W.resp x:= prod_mul_distrib
variable {V U: Cores Y r→ Pod Y→ℝ} {x}
abbrev Cap (A:Shift Y P T θ r) (V:Cores Y r→ Pod Y→ℝ):=∀ (x:Pod Y) (p:Cores Y r), Cabinet.Ready P Y T θ x → p∈ recital Y r x →‖A.F p x‖ ≤ Real.exp (V p x)
abbrev Income (A:Shift Y P T θ r) (V:Cores Y r→ Pod Y→ ℝ):=∀ (x:Pod Y) (p:Cores Y r),Cabinet.Ready P Y T θ x→p∈ recital Y r x→ (A.F p x).re≤V p x
lemma adds (v:F.Income V)(w:W.Income U) : (F.add W).Income (V+U):=fun x y t p=> add_le_add (v _ _ t p) (w _ _ t p)
lemma muls (v:F.Cap V)(w:W.Cap U): (F.mul W).Cap (V+U):=by intro x y t p; change ‖_*_‖≤ Real.exp (V y x+U y x); rw [norm_mul,Real.exp_add]; exact mul_le_mul (v _ _ t p) (w _ _ t p) (norm_nonneg _) (Real.exp_pos _).le
lemma includeA(v:F.Income V): F.exponential.Cap V:=fun x y t p=> (Complex.norm_exp _).trans_le (Real.exp_monotone (v _ _ t p))
lemma rise(v:F.Cap V)(t:∀ (x:Pod Y)(p:Cores Y r), V p x ≤ U p x): F.Cap U:=fun i x p h=> (v _ _ p h).trans (Real.exp_monotone (t i x))
-- meas assembly. Can depend upon complete Visible on domain. Outside context irrelevant. 
private lemma visit_m(i:Cores Y r): MeasurableSet {x|i∈recital Y r x}:= Contour.Season.vis (bitL Y) (Brick.wake_vis mH g₀ y) (fun a=> i∈ Contact wB r a) -- F not used
@[fun_prop] lemma resp_m : Measurable F.resp:=by
 have hh(x:Pod Y):(recital Y r x)= univ.filter (fun i=> i∈ recital Y r x):=by ext; simp
 change Measurable (fun x=> F.resp x); unfold resp; conv=>enter [1,x]; rw [hh, Finset.prod_filter]
 apply Finset.measurable_prod; intro i _; exact (F.m i).ite (visit_m ..) measurable_const
-- Packaging of tested H and estimate. tasteB.LogWeak.- lift overall.
variable {u:Pod Y→ℂ}{J:Type}[Fintype J](H: Teller (Prox.gridBase (House.Season Y.yard Y.c')) (Cabinet.Ready P Y T θ) (Esp Y r) J u 4 (1/8))
def pickM {u:Pod Y→ℂ}(A:Shift Y P T θ r)(Q: Teller (Prox.gridBase wB) (Cabinet.Ready P Y T θ) (Esp Y r) J u 4 (1/8)) (x:Pod Y) : ℂ:= if Cabinet.Ready P Y T θ x then A.resp x * Complex.exp (∑ i,Q.bill i x) else 0
variable (q:Mint.Mode)(k:F.Cap (Mint.settle Y r q))
include k
lemma freight: Mint.Freight Y r q P T θ F.F:= ⟨F.m,k,fun x y i p t u l g=> F.T i x y u l p t g⟩
omit k
lemma choose_hit (x:Pod Y)(p:Cabinet.Ready P Y T θ x): pickM F H x=F.resp x* Complex.exp (u x):=by unfold pickM; rw [if_pos p,(H.values x p).symm]
@[fun_prop] lemma pick_m : Measurable (pickM F H):= by
 apply Measurable.ite (readyV ..); swap; exact measurable_const
 exact F.resp_m.mul (Complex.continuous_exp.measurable.comp (Finset.measurable_sum _ (fun i _=> H.meas i)))
include k
-- only F.exp settlement evaluated adm
lemma pick_env : Envelope (pickM F H):=by
 let S':= (Fintype.card (Cores Y r):ℝ); let L:= (Fintype.card B:ℝ); let A:= |q.cost| *L+|q.burn| *L+L*|q.bias|; let W:= Real.exp A; have hA:0≤A:=by unfold A L; positivity
 refine ⟨F.pick_m H, Real.exp (A*S'+∑ i,H.size i),fun x=>?_⟩; unfold pickM; rw [Real.exp_add]; split; swap; · rw [norm_zero]; positivity
 rename_i v; rw [norm_mul, Complex.norm_exp]; apply mul_le_mul _ _ (Real.exp_pos _).le (Real.exp_pos _).le; swap; · apply Real.exp_monotone; exact (Complex.re_le_norm _).trans ((norm_sum_le ..).trans (sum_le_sum fun i _=> H.amount i x v))
 unfold resp; rw [norm_prod]; set Q:=recital Y r x; have ht(K:Finset B): (K.card:ℝ)≤L:=Nat.cast_le.mpr (Finset.card_le_card (subset_univ _)) -- tune mismatch
 have hu(i: Cores Y r): Mint.settle Y r q i x≤ A:=by
    rw [Mint.settle_eq]; unfold A; apply le_trans (b:= ((Mint.grey Y r i x).card:ℝ)*|q.cost| + ((Mint.stripe Y r i x).card:ℝ)*|q.burn| + ((Mint.paid Y r i x).card:ℝ)*|q.bias|)
    · rw [sub_eq_add_neg,sub_eq_add_neg]; rw [←mul_neg,←mul_neg]; apply add_le_add (add_le_add ?_ ?_) ?_; all_goals refine mul_le_mul_of_nonneg_left ?_ (by positivity); first | exact le_abs_self _|exact neg_le_abs _
    rw [mul_comm |q.cost|, mul_comm |q.burn|]; gcongr <;> apply ht
 apply (prod_le_prod (fun i _=> norm_nonneg _) (fun i h=> (k x i v h).trans (Real.exp_monotone (hu i)))).trans; rw [←Real.exp_sum,sum_const,nsmul_eq_mul]; rw [mul_comm _ S']; apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card (subset_univ _))) hA
-- B-contour thermal to Ξ. sorts. result denominator volume |Λ| price.
variable (T₀:T.Bounds c w R v)(t:θ∈ Set.Icc (1/2) 2){p:Brick.Solid y Y.yard.short Y.g.count.val}{j χ:ℝ}(hg:hNear≤r)(h₂:q.Buy χ j Y.g.count.val Y.yard.short y)(v':200≤r)(hf:feeχ 4 r≤χ)
-- pack theorem
include T₀ t h₂ v' hf
lemma equity (p:Brick.Solid y Y.yard.short Y.g.count.val): Real.exp (-(Fintype.card B:ℝ)) ≤ ‖Battery.stock (P:=Brick.prep mH g₀ y p) (pickM F H)‖:= by
 let V:=bitL Y; let L:=Mint.brave Y r q p χ j h₂ P T θ T₀ t v'; have ht:Silver (adm:=Cabinet.Ready P Y T θ) (E:=V) (fresh:=lid Y) r (pickM F H) F.F u:=⟨fun x _ p=> choose_hit F H x p,fun _ _ p=> if_neg p⟩
 apply Battery.billing r (readyV ..) L (Mint.grant Y r q p χ j h₂ P T θ T₀ t v' F.F (F.freight q k)) (Brick.story mH g₀ y p) ht H hf rfl -- needs DecEq J not instance? classical
end Shift
end YM.CF.BProof.Cabinet
