import YM.Heat.Lift
import YM.SU5.FiniteGaugeData.Seld.Wadding
import YM.Distribution.Product
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
abbrev M (p:E4):= S.unit.translation p
local notation "U"=> M S
variable (p q:E4)(A:H.Op)
lemma step_c : Continuous (fun p:H×E4=> M S p.2 p.1):= continuous_prod_of_continuous_lipschitzWith _ 1 (V).moves fun t=>(show Isometry (S.unit.translation t) from AddMonoidHomClass.isometry_of_norm _ (S.unit.unitary t)).lipschitz
lemma tcost : ‖U p x‖=‖x‖:= (V).unitary p _
lemma tcostO : ‖U p‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>by rw [tcost,one_mul])
lemma tgo : U p*U q=U (p+q):=(V).sends ..
lemma tini : U 0=1:= (V).origin
lemma tsees : inner ℂ (U p x) (U p y)=inner ℂ x y:= LinearIsometry.inner_map_map (show H →ₗᵢ[ℂ] H from { (U p).toLinearMap with norm_map':= fun x=> tcost S x p }) x y
lemma tboth : inner ℂ x (U p y)=inner ℂ (U (-p) x) y:=by rw [← tsees S _ _ (-p),show U (-p) (U p y)=y from DFunLike.congr_fun (show U (-p)*U p=1 from (by rw [tgo,neg_add_cancel,tini])) y] -- chooses RHS first?
lemma tstar : star (U p)=U (-p):=by ext1 x; apply ext_inner_right ℂ; intro y; change inner ℂ ((U p).adjoint x) y=_; rw [ContinuousLinearMap.adjoint_inner_left,tboth]
lemma tread : Commute R (U p) := (cupL S (p a)).mul_right (cupU S _)
lemma timeslot(t:ℝ) : U (t • basis a)= S.edge t := by dsimp only [M,unit]; rw [show SEP a (t • basis a)=0 from Subtype.ext (by show (t • basis a-(t • basis a:E4) a • basis a)=0; simp),S.uZero]; simp
lemma laneslot(t:Cross a): U t.val= S.U t:= by
 dsimp only [M,unit]; have he:t.val a=0:= t.property; rw [he,S.birth,show SEP a t.val=t from Subtype.ext (by change t.val-t.val a • basis a=t.val; simp [he]),ContinuousLinearMap.id_comp]
lemma hslot (z:ℂ)(h:z∈inside): Commute (S.F z) (U p):= (show Commute (S.F z) (S.edge (p a)) from (S.either h _).trans (S.along h _).symm).mul_right ((show Commute (S.F z) (S.U (SEP a p)) from S.stays h (SEP a p)))
lemma isochron (A:H.Op)(B:H.Op)(p: R*A=R*B): A=B:=by ext1 x; exact paranoid S (DFunLike.congr_fun p x)
lemma mslot (z:ℂ)(h:z∈inside)(n:ℕ):Commute (parabola S n z) (U p):=by
 let K:=Cache S n; let T:=U p; let B:=parabola S n z; have he:K*B= S.F z:=recover S n z h; have hp: K*T=T*K:= (tread S p).pow_left n; have hv: K*(B*T)=K*(T*B):=by rw [← mul_assoc,← mul_assoc,he,hp,mul_assoc,he,(hslot S p z h).eq]
 change B*T=T*B; ext1 x; exact cache_I S n (DFunLike.congr_fun hv x)
-- conjugation
abbrev optx (A:H.Op)(p:E4):H.Op:= U p*A*U (-p)
lemma opt_act : optx S (optx S A q) p=optx S A (p+q):=by unfold optx; rw [mul_assoc (U q) A,← mul_assoc (U p), tgo,mul_assoc,mul_assoc A,tgo]; abel_nf; rw [mul_assoc]
lemma village : Continuous (fun p => optx S A p x):=by
 have h := A.continuous.comp ((S.unit.moves x).comp (continuous_neg (G:=E4))); let f:= fun p:E4=> A (U (-p) x); let T:= fun p:E4=> S.U (SEP a p) (f p); exact S.cont_edge T (fun p:E4=> p a) (S.cont_cross f (SEP a) h (SEP a).continuous) (by fun_prop)
lemma vcost: ‖optx S A p x‖ ≤ ‖A‖*‖x‖:=by
 change ‖U p (A (U (-p) x))‖ ≤ _; rw [tcost]; exact (A.le_opNorm _).trans (by rw [tcost])
lemma versL(c:ℂ): optx S (c • A) p = c • optx S A p:=by unfold optx; rw [mul_smul_comm,smul_mul_assoc]
lemma versA(c:H.Op): optx S (A+c) p = optx S A p+optx S c p:=by unfold optx; rw [mul_add,add_mul]
lemma versP(B:H.Op)(t:Commute (U p) B): optx S (B*A) p=B*optx S A p:=by unfold optx; rw [←mul_assoc, t.eq]; simp only [mul_assoc]
lemma versQ(B:H.Op)(t:Commute (U (-p)) B): optx S (A*B) p=optx S A p * B:=by unfold optx; rw [← mul_assoc,mul_assoc,mul_assoc]; simp only [mul_assoc,t.eq]
lemma versX : star (optx S A p)= optx S (star A) p:=by unfold optx; rw [star_mul,star_mul,tstar,tstar,neg_neg,mul_assoc]
lemma vroot : optx S A 0=A:=by unfold optx; rw [neg_zero,tini,one_mul,mul_one]
#print axioms mslot
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
