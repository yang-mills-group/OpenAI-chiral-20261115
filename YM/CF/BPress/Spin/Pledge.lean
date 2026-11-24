import YM.CF.Support.Hit
/-! Matrix strong price currency, with Spin structure combinators keeping the precondition explicit.

Section B-op variant (fixed grant PLC). Instead of specifying by uniform domain collection,
operators accept any domain together with their support `Stage` prices; combinators return
prices still independent thereof. UNIT gauge in the `Costs` currency: eq:B-sLip doesn't
require each piece equivariant; gauge averaging is on the needed scalar reads.

Can use a local l1 sum metric on support readings. It converts with exponential spare,
and `Costs` here is always for the eval specified (a local stage). The combination results like
`Pledge.over` include also the max convention, apply these lemmas just as well with that currency.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Finset Fock Branch Filter NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
attribute [local instance] opCStarAlgebra

structure Pledge where
 rate : ℝ
 price : ℝ
 pos : 0<rate
 bought : 0<price
namespace Pledge
instance : Inhabited Pledge:= ⟨⟨1,1,one_pos,one_pos⟩⟩
instance : LE Pledge:= ⟨fun x y=> y.rate≤x.rate∧ x.price≤y.price⟩
instance : Preorder Pledge where
 le_refl a:= ⟨le_rfl,le_rfl⟩
 le_trans _ _ _ h t:= ⟨t.1.trans h.1,h.2.trans t.2⟩
def bond (P Q:Pledge):Pledge:=⟨min P.rate Q.rate,max P.price Q.price,lt_min P.pos Q.pos,lt_max_of_lt_left P.bought⟩
lemma bond_lel (P Q:Pledge):P≤bond P Q:= ⟨min_le_left ..,le_max_left ..⟩
lemma bond_ler (P Q:Pledge):Q≤bond P Q:= ⟨min_le_right ..,le_max_right ..⟩
def plus(P Q:Pledge):Pledge:=⟨min P.rate Q.rate,P.price+Q.price,lt_min P.pos Q.pos,add_pos P.bought Q.bought⟩
def times(P Q:Pledge):Pledge:=⟨min P.rate Q.rate,2*(P.price*Q.price),lt_min P.pos Q.pos,mul_pos (by norm_num) (mul_pos P.bought Q.bought)⟩
def scales(P:Pledge)(a:ℝ):Pledge:= ⟨P.rate,(max 1 a)*P.price,P.pos,mul_pos (lt_max_of_lt_left zero_lt_one) P.bought⟩
lemma scales_le (P:Pledge)(a:ℝ):P≤ scales P a:= ⟨le_rfl,le_mul_of_one_le_left P.bought.le (le_max_left ..)⟩
def unary:Pledge:=⟨1,Real.exp 1,one_pos,Real.exp_pos _⟩

variable {Y I D : Type*}[Fintype Y][DecidableEq Y][Fintype I][DecidableEq I][TopologicalSpace D]
-- empty maps cheapest
def solo (b : Stage Y I D Empty) : Tag b:= ⟨fun x=>Empty.elim x,fun x _ _ _=> Empty.elim x⟩
abbrev Costs (P:Pledge)(b : Stage Y I D Empty)(f : Raw D I):= RootedK (solo b) (solo b) P.rate P.price f
variable {b : Stage Y I D Empty}{P Q:Pledge}{f g: Raw D I}{a C:ℝ}
namespace Costs
lemma up (h:Costs P b f)(v:P≤Q): Costs Q b f:= (h.drop v.1).books v.2
lemma plus (p:Costs P b f)(q:Costs Q b g): Costs (P.plus Q) b (fun i=> f i+g i):=(p.drop (min_le_left ..)).plus (q.drop (min_le_right ..)) -- recursion? abbrev dot
lemma neg (p:Costs P b f): Costs P b (fun i=> - f i):= p.minus
lemma sub (p:Costs P b f)(q:Costs Q b g): Costs (P.plus Q) b (fun i=> f i-g i):=(p.drop (min_le_left ..)).sub (q.drop (min_le_right ..))
lemma mul (p:Costs P b f)(q:Costs Q b g): Costs (P.times Q) b (fun i=> f i*g i):=(p.drop (min_le_left ..)).product (q.drop (min_le_right ..)) (le_min P.pos.le Q.pos.le)
lemma stalk (p:Costs P b f):Costs P b (fun i=> star (f i)):= p.starUp
lemma stars (p:Costs P b f):Costs P b (fun i=> cc (f i)):=by
 have hx:(solo b).reverseV=solo b:=by apply Tag.mk.injEq .. |>.mpr; funext x; exact x.elim
 have hy:= p.ccUp; rwa [hx] at hy
lemma transpose (p:Costs P b f):Costs P b (fun i=> (f i)ᵀ):=by
 have he : ∀ A: Op I, cc (star A)= Aᵀ := by intro A; ext i j; simp
 have ht:= stars (stalk p); simpa only [he] using ht
lemma one : Costs unary b (fun _=>1):= RootedK.oneK ..
lemma free : Costs P b (fun _=>0):= RootedK.free.books P.bought.le
lemma amplify (p:Costs P b f){c:ℂ}(he:‖c‖≤a): Costs (P.scales a) b (fun i=> c • f i):= (p.raise c).books ((mul_le_mul_of_nonneg_right (he.trans (le_max_right ..)) P.bought.le))
lemma smul (p:Costs P b f)(c:ℂ): Costs (P.scales ‖c‖) b (fun i=> c • f i):= p.amplify le_rfl
lemma scale (p:Costs P b f)(c:ℝ): Costs (P.scales ‖c‖) b (fun i=> c • f i):=by
 have he (x:D):(c:ℂ) • f x=c • f x:= by ext i j; simp [Complex.real_smul]
 simpa only [he,Complex.norm_real] using p.smul (c:ℂ)
lemma sums {α:Type*}[Fintype α](f:α→ Raw D I)(p:∀ a, Costs P b (f a)): Costs (P.scales (Fintype.card α)) b (fun i=> ∑ x,f x i):=by
 refine (RootedK.sumK univ _ _ (fun i _=> p i)).books ?_; simpa only [sum_const,nsmul_eq_mul,card_univ,scales] using (mul_le_mul_of_nonneg_right (le_max_right 1 (Fintype.card α:ℝ)) P.bought.le)
lemma bound (h:Costs P b f) (x:D):‖f x‖≤ P.price:= h.boundOp P.pos.le x
lemma morph {D' G:Type*}[TopologicalSpace D']{A : Stage Y I D' G}{s t: Tag A}{f'}(p:RootedK s t P.rate P.price f') (F:D→D')(e:Continuous F)(h:A.F=b.F)(u:A.home=b.home)(v:0≤C)(l:∀ S x y,A.eval S (F x) (F y)≤ C*b.eval S x y):
 Costs (P.scales C) b (f' ∘ F):=by
 obtain ⟨R,K,L,H,g⟩:=p; let w:= max 1 C; have ht:1≤w:= le_max_left ..
 refine ⟨(fun S=> R S ∘ F),_,fun S=>⟨fun i _=>Empty.elim i, fun i j=>?_⟩, H.funds (show 0≤w from zero_le_one.trans ht),fun x=> g (F x)⟩
 let E:= (L S).expo i j; refine ⟨mul_nonneg (zero_le_one.trans ht) E.positive,fun a=>?_,fun x=> (E.bounded (F x)).trans (le_mul_of_one_le_left E.positive ht),fun x y=> (E.variation (F x) (F y)).trans ((mul_le_mul_of_nonneg_left ((l S x y).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (b.pos ..))) E.positive).trans_eq (by ring)), E.connected.comp e⟩
 rw [←h,←u]; exact E.triggered (right_ne_zero_of_mul a)
lemma pulls {D':Type*}[TopologicalSpace D']{A:Stage Y I D' Empty}{f':Raw D' I}(p:Costs P A f')(F:D→D')(e:Continuous F)(h:A.F=b.F)(u:A.home=b.home)(l:∀ S x y,A.eval S (F x) (F y)≤ b.eval S x y): Costs P b (f' ∘ F):=by
 have ht:= morph p F e h u (show 0≤(1:ℝ) by norm_num) (by simpa only [one_mul] using l); refine ht.up ⟨le_rfl,?_⟩; simp [scales]
end Costs
end Pledge
end YM.CF.BPress.Spin
