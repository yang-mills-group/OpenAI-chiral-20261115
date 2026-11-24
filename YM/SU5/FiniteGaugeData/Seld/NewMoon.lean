import YM.SU5.FiniteGaugeData.Seld.Mercans
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
-- translated coordinates via `shift η`
variable (q:E4)
lemma ush_pre : hall S n (usher S p X) = (U p) (hall S n X) := park_κ S n _ _ _ _ ((tread S p).symm.pow_right _)
lemma lucid : lucent S (hall S m (usher S q X)) (hall S m (usher S q Y)) A (q+p)=lucent S (hall S m X) (hall S m Y) A p:= by
 rw [ush_pre,ush_pre,lucent,lucent,← opt_act]; let x:= hall S m X; let y:= hall S m Y; change inner ℂ (U q x) (U q (optx S A p (U (-q) (U q y))))= _; rw [tsees, show U (-q) (U q y)=y from DFunLike.congr_fun ((tgo S (-q) q).trans (by rw [neg_add_cancel, tini] : U (-q+q)=1)) y]
lemma dot_slide (e: DotComm S A B p g m n X Y): DotComm S A B (q+p) (ahead q g) m n (usher S q X) (usher S q Y):=by unfold DotComm; rw [← attends, bar_ahead,← attends, lucid,lucid]; exact e
lemma route : MapsTo (fun x:E4=>x-p) (tsupport (ahead p g)) (tsupport g):= MapsTo.closure (t:=support g) (s:=support (ahead p g)) (fun _ p=>p) (continuous_id.sub continuous_const)
lemma shuttle(p q:E4)(g:Test4): ahead p (ahead q g)=ahead (p+q) g:= by ext1 x; change g (x-p-q)= _; rw [ahead_at]; rw [sub_sub]
lemma ahead₀ : ahead 0 g=g:= by ext1 x; simp
lemma yank (e:∀ X Y:Bench S, DotComm S A B (p-q) (ahead (-q) g) m n X Y): DotComm S A B p g m n X Y:=by
 have w:=dot_slide S A B (p-q) (ahead (-q) g) m n (usher S (-q) X) (usher S (-q) Y) q (e _ _); rw [shuttle, add_neg_cancel, ahead₀, ushe,ushe,add_neg_cancel,uh_zero, uh_zero, show q+(p-q)=p from by abel] at w; exact w
lemma nighttime (e:∀ p∈ tsupport h,DotComm S A B p g m n X Y): inner ℂ X.val (ℑ S A h m (ℑ S B g n Y)).val=inner ℂ X.val (ℑ S B g n (ℑ S A h m Y)).val:=by
 let Z:= ℑ S A h m Y; have he(x:Bench S): inner ℂ X.val (ℑ S B g n x).val = inner ℂ (ℑ S (star B) (bar g) n X).val x.val:=by rw [sees_κ, star_star, bar_twice]
 rw [he,assizes,assizes]; apply integral_congr_ae; filter_upwards with x'; by_cases p:h x'=0; · simp [p]
 exact congrArg (h x'* ·) (e x' (subset_closure p))
lemma Eff (e: ∀ p∈tsupport h,∀ X Y: Bench S, DotComm S A B p g m n X Y): (ℑ S A h m).comp (ℑ S B g n)=(ℑ S B g n).comp (ℑ S A h m):= by
 ext1 x; apply Subtype.ext; apply (show DenseRange (Subtype.val:Bench S→H) from (by rw [DenseRange,Subtype.range_val]; exact bench_warm S)).eq_of_inner_right ℂ; intro y; exact nighttime S A B g h m n y x (fun p t=> e p t y x)
#print axioms yank
#print axioms Eff
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
