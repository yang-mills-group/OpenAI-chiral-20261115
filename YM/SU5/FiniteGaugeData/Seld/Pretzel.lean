import YM.SU5.FiniteGaugeData.Seld.Raft
import YM.SU5.FiniteGaugeData.Celeritas.Lacem
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
open Lattice Celeritas
local notation "d"=> OS.Semigroup.duration
local notation "K"=> Cache S
local notation "F"=> parabola S
local notation "P"=> Par S
local notation "εd"=> OS.Semigroup.sideways
-- L left vector includes AC; b price. v1 and v2 GAP full; spend u so require residuals v1-u≥ margin etc.
variable (C:Cinema S)(b:Cross a)(hB: ‖b‖ ≤ 1)(m n:ℕ)(v w:ℝ≥0) (δ:ℝ≥0)
abbrev sprawl (z:ℂ) := inner ℂ x ((Par S m (v-u)) (cup S u C b hB z (A ((cup S u C b hB (-z)) ((Par S n (w-u)) y)))))
local notation "Ω"=> sprawl S x y u A C b hB m n v w
variable (z:ℂ)
lemma sprawlA (p:z∈ lanes (u:ℝ)): AnalyticAt ℂ Ω z:=by
 let β:= cup S u C b hB; let B:= (innerSL ℂ x).comp (P m (v-u)); let y':=(P n (w-u)) y; have L:= cup_A S b u C hB z p; let Q:= (ContinuousLinearMap.apply ℂ H.space y'); let f(z:ℂ):= β z *A * β (-z); have J:AnalyticAt ℂ f z:= (L.mul analyticAt_const).mul ((cup_A S b u C hB (-z) (by rw [lanes,mem_setOf,neg_im,abs_neg]; exact p)).comp (analyticAt_id.neg)); exact B.analyticAt _ |>.comp (Q.analyticAt _ |>.comp J)
-- bound grade
abbrev slu (δ:ℝ≥0)(A:H.Op) :ℝ:= ‖x‖*(‖P m δ‖*(4*(‖A‖*(4*(‖P n δ‖*‖y‖)))))
lemma roul (h:0<δ)(i:δ≤v): ‖P m v‖≤‖P m δ‖:=by rw [landDiv S v m δ h i]; exact (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (S.shrinks _))
lemma abound (p:z∈ lanes (u:ℝ))(h:0<δ)(v':δ≤v-u)(w':δ≤w-u): ‖Ω z‖ ≤ slu S x y m n δ A:=by
 apply (norm_inner_le_norm ..).trans; have he: -z∈ lanes (u:ℝ):=by rw [lanes,mem_setOf,neg_im,abs_neg]; exact p
 have hx(u:H)(M:H.Op){c v:ℝ}(p:‖M‖≤c)(t:‖u‖≤v):‖M u‖≤ c*v:= (M.le_opNorm u).trans (mul_le_mul p t (norm_nonneg _) ((norm_nonneg _).trans p))
 exact mul_le_mul_of_nonneg_left (hx _ _ (roul S m (v-u) δ h v') (hx _ _ (cupH S b u z C hB p) (hx _ _ le_rfl (hx _ _ (cupH S b u (-z) C hB he) (hx _ _ (roul S n (w-u) δ h w') le_rfl))))) (norm_nonneg _) -- unresolved
lemma divrest (v':u<v): P m v=P m (v-u)*S.E u := Eq.trans (landDiv S v m _ (tsub_pos_of_lt v') (tsub_le_self)) (by rw [tsub_tsub_cancel_of_le v'.le]) -- tsub_le
lemma sprawlR (h:0<u)(p:u<v)(q:u<w) : sprawl S x y u A C b hB m n v w (t:ℂ)= inner ℂ x ((P m v) (S.U (t • b) (A (S.U (-t • b) ((P n w) y))))):=by
 have Hk(v:ℝ≥0)(i:u<v)(t:ℝ)(m:ℕ)(x:H): P m v (S.U (t • b) x)= (P m (v-u)) (cup S u C b hB t x):=by
    rw [credit_h S b u t C hB h, divrest S u m v i]; exact congrArg (P m (v-u)) (DFunLike.congr_fun (S.independent ..) x)
 have G: (cup S u C b hB (-(t:ℂ))) ((P n (w-u)) y)= S.U (-t • b) ((P n w) y):=by
    rw [← ofReal_neg,credit_h S b u (-t) C hB h]; let Z:H.Op:=P n (w-u); have HE : S.E u* Z = P n w:=by
       let Q':=t; have he:= congrArg (star:H.Op→H.Op) (divrest S u n w q); rw [star_mul, (parRev S w n (h.trans q)).star_eq,(parRev S (w-u) n (tsub_pos_of_lt q)).star_eq, show star (S.E u)=_ from S.sym u] at he; exact he.symm
    exact congrArg (S.U (-t • b)) (DFunLike.congr_fun HE y)
 unfold sprawl; rw [G,Hk v p]
#print axioms sprawlR
-- Interior along BOTH.W. B right.E.Action.HSlot. Comparison to real.Sh.Positive `backL` with Opts already.
lemma snort {q:ℝ≥0}(P0: 0< q)(k:q<2)(L:t∈{t:ℝ| |t|<(u:ℝ)}): (OS.Semigroup.duration q)+sideways t∈chamber 2 (u:ℝ):=by
 unfold chamber OS.Semigroup.duration sideways; change |t| < (u:ℝ) at L; have hp:(0:ℝ)<(q:ℝ):=P0; have hz: (q:ℝ)<2:=by exact_mod_cast k
 simp [hp,hz,L]
lemma rills(F₁:ℂ→ℂ)(h: AnalyticOnNhd ℂ F₁ (lanes (u:ℝ)))(lr:0<u)
    (e:∀ t:ℝ, 0<t→t<2→ backwards S x y A B m n (t:ℂ)=F₁ t)
    (e':∀ t:ℝ, 0<t→t<2→ forwards S x y A B m n (t:ℂ)=F₁ (-(t:ℂ)))
    (q:ℝ≥0)(v:0<q)(z:q<2)(L:|t|<(u:ℝ)): backwards S x y A B m n ((d q)+sideways t)=F₁ ((d q)+sideways t) ∧ forwards S x y A B m n ((d q)+sideways (-t))=F₁ (-(d q)+sideways t):=by
 let f(z:ℂ):= F₁ (-z); have hh(Z:ℂ)(p:Z∈lanes (u:ℝ)): AnalyticAt ℂ f Z := (h (-Z) (by rw [lanes, Set.mem_setOf, neg_im,abs_neg]; exact p)).comp analyticAt_id.neg
 refine ⟨veil_set 2 (u:ℝ) zero_lt_two lr (fun z p=>(rafts S x y A B m n z (show z.re > 0 ∧ z.re <2 from ⟨p.1,p.2.1⟩)).1) (fun i p=> h i p.2.2) e (snort t u v z L),?_⟩
 let V0:=veil_set 2 (u:ℝ) zero_lt_two lr (fun z p=> (rafts S x y A B m n z (show z.re>0∧z.re<2 from ⟨p.1,p.2.1⟩)).2) (fun i p=> hh i p.2.2) e' (snort (-t) u v z (by show |(-t)| < (u:ℝ); rwa [abs_neg]))
 exact V0.trans (congrArg F₁ (show -(d q+ sideways (-t))=(-(d q)+sideways t) from (by unfold sideways; push_cast; ring))) -- snort order anticipated t u
#print axioms rills
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
