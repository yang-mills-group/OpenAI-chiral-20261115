import YM.SU5.FiniteGaugeData.Seld.GaugeK
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)(x y:H)(t:ℝ)(u:ℝ≥0)
local notation "rayA"=> Ioi (0:ℝ)
local notation "R"=> saucer S
open Spectral Boundary Probe
local notation "V"=> S.unit
local notation "U"=> M S
variable (A B: H.Op)(p:E4)(g h: Test4)(c:ℂ)
local notation "W" => Bench S
local notation "□" => W →ₗ[ℂ] W
variable (X Y: Bench S) (g₁ : 0<u) (m n:ℕ)
local notation "P" => Par S
local notation "K"=> Cache S
local notation "F"=> parabola S
variable (v u' v':ℝ≥0)(L M':H.Op)
-- linearity as price within ANY S.O.B fixture
lemma waterQ : (∫ p,g p* inner ℂ x ((L * optx S A p * M') y)) = inner ℂ x ((L*valise S A g*M') y):=by
 have he(Gx:H.Op):inner ℂ x ((L*Gx*M') y)=inner ℂ (L.adjoint x) (Gx (M' y)):= (ContinuousLinearMap.adjoint_inner_left L _ _).symm
 simp_rw [he]; exact sell_in .. -- tune arg names conflict F notation.
lemma waterI : Integrable (fun p=>g p* inner ℂ x ((L * optx S A p * M') y)):=by
 have he(Gx:H.Op):inner ℂ x ((L*Gx*M') y)=inner ℂ (L.adjoint x) (Gx (M' y)):= (ContinuousLinearMap.adjoint_inner_left L _ _).symm
 simp_rw [he]; exact sell ..
local notation "D₀" x:max y:max=> lucent S (hall S m x) (hall S m y) A
local notation "ℓ"=> optx S
-- Eu-spectator forms on a-window. order-margins.Need κu v>0.Real separators.
local notation "L₀"=> Par S m u
local notation "B₀"=> Par S n v
local notation "M₀"=> Par S (m+n) u'
local notation "Ψℓ" => ℓ A p
-- general diagrams with positive widths $u around static poin
abbrev backE (q:E4):= inner ℂ x (((((Par S m u)*optx S A p)*Par S (m+n) u')*optx S B q*Par S n v) y)
abbrev forE (q:E4):= inner ℂ x ((((Par S n v*optx S B q)*(Par S (m+n) u'*optx S A p*Par S m u)) y))
lemma fountainP : Integrable (fun q=>g q* backE S x y u A B p m n v u' q):= waterI .. -- tune order
lemma fountainR : Integrable (fun q=>g q* forE S x y u A B p m n v u' q):= waterI ..
local notation "Φ"=> ℑ S B g n
local notation "Φ'"=> ℑ S (star B) (bar g) n
-- interior association formulas
variable (k0:0<u)(k₁:0<v)(k₂:0<u')
include k0 k₁ k₂
lemma wage : (∫ q,g q* backE S x y u A B p m n v u' q) = lucent S (L₀ x) ((hall S m) (stove S u' (Φ (flame S v k₁ y)))) A p:= by
 rw [show _ from waterQ S x y B g (L₀ * (Ψℓ) * M₀) B₀]; change inner ℂ x ((L₀) ((Ψℓ) ((M₀) (valise S B g ((B₀) y)))))=_
 rw [← ContinuousLinearMap.adjoint_inner_left (L₀), show (L₀).adjoint=(L₀) from parRev S u m k0]
 -- k0 not in statement include
 let w:= Φ (flame S v k₁ y); have he: (K n) (w.val) = valise S B g ((B₀) y):= by unfold w; rw [native,rung]
 rw [←he, show (M₀) (K n w.val)= P m u' w.val from DFunLike.congr_fun (resolve S u' m n k₂) _]; unfold lucent; rw [priceT _ u' w m k₂]
omit k0
lemma wageR : (∫ q,g q* forE S x y u A B p m n v u' q) = lucent S ((hall S m) (stove S u' (Φ' (flame S v k₁ x)))) (L₀ y) A p:= by
 rw [show _ from waterQ S x y B g B₀ (M₀ * Ψℓ * L₀)]; change inner ℂ x ((B₀) (valise S B g ((M₀) ((Ψℓ) ((L₀) y))))) = _
 rw [← ContinuousLinearMap.adjoint_inner_left (B₀),← ContinuousLinearMap.adjoint_inner_left (valise S B g), show (B₀).adjoint=B₀ from parRev S v n k₁, show (valise S B g).adjoint=valise S (star B) (bar g) from (scenery S B g).symm]
 let w:= Φ' (flame S v k₁ x); have he: (K n) (w.val)= valise S (star B) (bar g) ((B₀) x):=by unfold w; rw [native,rung]
 rw [←he, ← ContinuousLinearMap.adjoint_inner_left (M₀), show (M₀).adjoint=M₀ from parRev S u' (m+n) k₂, show (M₀) (K n w.val)= P m u' w.val from DFunLike.congr_fun (resolve S u' m n k₂) _]; unfold lucent; rw [priceT _ u' w m k₂]
#print axioms wage
#print axioms wageR
-- denominator-only.Criterion. explicit limit epsilon invoice. choose u fixed=1, v=1- ε; n.Norm smears.K. zero.
omit k₁ k₂
local notation "ϵ"=> ℝ≥0
-- naming alias partition.E
abbrev squirt(i:ℕ):ϵ:=1/(i+2)
abbrev dearth(i:ℕ):ϵ:=2-squirt i
variable (i:ℕ)
lemma squirtP : 0<squirt i:=by unfold squirt; positivity
lemma dearthP : 0<dearth i:=tsub_pos_of_lt (by unfold squirt; exact lt_trans (div_lt_self zero_lt_one (by exact (show (1:ϵ)<2 from by norm_num).trans_le (le_add_of_nonneg_left (by positivity)))) (by norm_num))
lemma squirtL : Tendsto squirt atTop (𝓝 0):=by apply NNReal.tendsto_coe.mp; simpa [squirt] using (tendsto_const_nhds (x:=(1:ℝ))).div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop) -- annotation
lemma dearthL : Tendsto dearth atTop (𝓝 2):=by simpa only [tsub_zero] using tendsto_const_nhds (x:=(2:ϵ)) |>.sub squirtL -- tsub?
lemma stoveT (k:∀ i:ℕ,0<dearth i): pays_to S atTop (fun i:ℕ=> stove S (squirt i) (ℑ S B g n (flame S (dearth i) (k i) x))) (ℑ S B g n (flame S 2 zero_lt_two x)):=by
 refine Eq.mp ?_ (stoveLim S 0 (Φ (flame S 2 zero_lt_two x)) _ _ _ squirtL (ℑLim₁ S B g _ n _ _ _ tendsto_const_nhds (warps S x 2 _ _ dearthL zero_lt_two k _ tendsto_const_nhds))); rw [stove_zero]
def DotComm (X Y:Bench S):Prop:= (D₀ X (Φ Y)) p = (D₀ (Φ' X) Y) p
lemma flanks (e:Tendsto (fun i:ℕ=>∫ q, g q*(backE S x y 2 A B p m n (dearth i) (squirt i) q - forE S x y 2 A B p m n (dearth i) (squirt i) q)) atTop (𝓝 0)): DotComm S A B p g m n (flame S 2 zero_lt_two x) (flame S 2 zero_lt_two y):=by
 let X:= flame S 2 zero_lt_two x; let Y:=flame S 2 zero_lt_two y; let Uc(s:Bench S):=hall S m s
 let r(i:ℕ):= dearth i; let t(i:ℕ):=squirt i
 let D(i:ℕ):H:= Uc (stove S (t i) (Φ (flame S (r i) (dearthP i) y))); let G(i:ℕ):H:= Uc (stove S (t i) (Φ' (flame S (r i) (dearthP i) x)))
 let R':= Uc (Φ Y); let L':=Uc (Φ' X)
 have hX(i:ℕ): (∫ q, g q*(backE S x y 2 A B p m n (dearth i) (squirt i) q - forE S x y 2 A B p m n (dearth i) (squirt i) q))=inner ℂ (Uc X) ((Ψℓ) (D i))-inner ℂ (G i) ((Ψℓ) (Uc Y)):=by
    simp_rw [mul_sub,integral_sub (fountainP ..) (fountainR ..),wage S x y _ A B p g m n _ _ zero_lt_two (dearthP i) (squirtP i),wageR S x y _ A B p g m n _ _ (dearthP i) (squirtP i)]; unfold Uc X Y; rw [rung,rung]; rfl
 simp_rw [hX] at e; apply sub_eq_zero.mp; change inner ℂ (Uc X) ((Ψℓ) R')-inner ℂ L' ((Ψℓ) (Uc Y))=0; refine tendsto_nhds_unique ((tendsto_const_nhds.inner ((Ψℓ).continuous.continuousAt.tendsto.comp (stoveT S y B g n dearthP m))).sub ((stoveT S x (star B) (bar g) n dearthP m).inner tendsto_const_nhds)) e
#print axioms flanks
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
