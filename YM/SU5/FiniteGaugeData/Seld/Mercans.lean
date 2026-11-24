import YM.SU5.FiniteGaugeData.Seld.Fountain
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
-- Density Extension independent of geometry. annihilator dense uses <...>>. DotComm price_after external.$D_G.U with arbitrary linear operator. Gram. convert cost.P
local notation "P" => Par S
local notation "K"=> Cache S
variable (m n:ℕ) (X Y: Bench S)
local notation "Φ" => ℑ S B g n
local notation "Φ'"=> ℑ S (star B) (bar g) n
local notation "AB"=> optx S A p
abbrev tunes (v:H.Op)(g:Test4):H.Op:= brochure S v (n+m) g * P (n+(n+m)) 1
def leftF:H.Op:= P m 1 * AB * tunes S m n B g
-- tunes arg order? B,p before m n implicit? lean infers.B expected.A.F
local notation "Tp"=>tunes S m n B g
local notation "Tq"=>tunes S m n (star B) (bar g)
local notation "L"=> leftF S A B p g m n
local notation "G"=> (star (Tq)) * AB * P m 1
local notation "ϒ"=> flame S 1 zero_lt_one
lemma Afo : DotComm S A B p g m n ((ϒ) x) ((ϒ) y) ↔ inner ℂ x ((L-G) y)=0:=by
 rw [_root_.sub_apply,inner_sub_right,sub_eq_zero]; unfold DotComm lucent; rw [graphN, graphN, rung,rung,rung,rung]; -- ℋ star issue rewrite.
 change inner ℂ ((P m 1) x) (AB (Tp y))=inner ℂ (Tq x) (AB (P m 1 y))↔_
 rw [← ContinuousLinearMap.adjoint_inner_right (P m 1),← ContinuousLinearMap.adjoint_inner_right (Tq) x, show (P m 1).adjoint=P m 1 from parRev S 1 m zero_lt_one]; rfl -- `Tp` defeq.M
abbrev Annihilated (T:Set H):= ∀ v:H,(∀ x:H,x∈T→inner ℂ v (S.E 1 x)=0)→v=0
-- requirement: SO support v. Use $ρ.A.S `.Warget
variable (U₀ T₀:Set H)
lemma flame_fold : flame S 1 zero_lt_one (S.E 1 x)= flame S 2 zero_lt_two x:= Subtype.ext (by change (S.E 1) (S.E 1 x)=_; exact DFunLike.congr_fun (show S.E 1 * S.E 1 = S.E 2 from Eq.trans (S.time 1 1 |>.symm) (by norm_num)) x)
lemma Dot_limit {C:Type*}(ℱ:Filter C)[ℱ.NeBot](F G':C→ Bench S)(h:pays_to S ℱ F X)(k:pays_to S ℱ G' Y) (p':∀ᶠ i in ℱ,DotComm S A B p g m n (F i) (G' i)): DotComm S A B p g m n X Y:= by
 apply tendsto_nhds_unique_of_eventuallyEq _ _ p'; rotate_left
 · exact (((ℑLim₁ S (star B) (bar g) X n ℱ F _ tendsto_const_nhds h) m).inner ((AB).continuous.continuousAt.tendsto.comp (k m))) -- unfolding function inferred p' no λ?
 exact (h m).inner ((AB).continuous.continuousAt.tendsto.comp ((ℑLim₁ S B g Y n ℱ G' _ tendsto_const_nhds k) m))
variable (e₁: Annihilated S U₀) (e₂:Annihilated S T₀)
lemma arriere (e₁: Annihilated S U₀) (e₂:Annihilated S T₀)
    (h:∀ x∈U₀,∀ y∈T₀, DotComm S A B p g m n (flame S 2 zero_lt_two x) (flame S 2 zero_lt_two y)): DotComm S A B p g m n X Y:=by
 let F:H.Op:=L-G
 have he (x)(z:x∈U₀)(y)(w:y∈T₀): inner ℂ (S.E 1 x) (F (S.E 1 y))=0:= by
    apply (Afo S _ _ A B p g m n).1; rw [flame_fold,flame_fold]; exact h _ z _ w
 have hp(y:H)(w:y∈T₀):F (S.E 1 y)=0:= by apply e₁; intro x z; rw [←inner_conj_symm, he x z y w,map_zero]
 have hv(x:H): F.adjoint x=0:= e₂ _ fun y w=>by rw [ContinuousLinearMap.adjoint_inner_left,hp y w]; exact inner_zero_right _
 obtain ⟨x,hx⟩:= browse S X 1 zero_lt_one; obtain ⟨y,hy⟩:=browse S Y 1 zero_lt_one; apply Dot_limit S A B p g m n X Y atTop _ _ hx hy; apply Eventually.of_forall; intro i; apply (Afo S (x i) (y i) A B p g m n).2; change inner ℂ (x i) (F _)=_; rw [←ContinuousLinearMap.adjoint_inner_left,hv]; exact inner_zero_left _
#print axioms arriere
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
