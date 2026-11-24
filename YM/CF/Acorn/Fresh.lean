import YM.CF.Acorn.Foil
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Matrix NormedSpace Finset Fock Jet Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {n Y D E:Type}[LinearOrder n][Fintype n][Fintype Y][DecidableEq Y][TopologicalSpace D][TopologicalSpace E]
variable {X:Master D Y} {Z:Master E Y}{f g:E→ D}{O:n→Y}{S R:Seal Y}{a K c r h V:ℝ}{A:D→ℂ}{L:D→Op (I n)}
structure Wallet (X: Master D Y)(a K:ℝ)(A:D→ℂ) : Prop where
 screen :∃ M:Seal Y→ D→ℂ, ∃ C:Seal Y→ℝ,(∀ i,Pro X i (M i) (C i))∧ (∀ i:Y,hitE a C i≤ K) ∧ ∀ i,A i=∑ j,M j i
lemma Wallet.tech (v:Grove Z.frame S)(w:S.Nonempty)(p:Cop X Z f)(q:Cop X Z g)(t:∀ R,Disjoint S R→∀ x,X.moves R (f x) (g x))(a':0≤a)(c:Wallet X a K A): Cash Z S a (fun x=> A (g x)-A (f x)) (S.card*(2*K)):=by
 obtain ⟨P,R,h,p',Q⟩:= c.screen
 -- t not sym; use minus
 have he:=Cash.sc (Cash.off S w v p q t P R h a' p' Q) (-1)
 rw [norm_neg,norm_one,one_mul] at he; convert he using 1; funext x; simp
structure Funds (X:Master D Y) (O:n→Y)(P C:D→Op n)(A:D→Wave n)(θ:D→ℂ)(a K L M:ℝ):Prop where
 scope: Plum X O (fun i=> quantX (P i) (C i)) a K
 extra: Plum X O (fun i=> stackX 0 0 (C i)) a L
 bonus: Wallet X a M θ
 parcel x : IsStarProjection (P x) ∧ (C x)ᵀ= -C x ∧ IsUnit (stage (P x) (C x))
 score x : filled (P x) (C x)=Complex.exp (θ x) • A x

def treasure (a h K L M:ℝ)(d k:ℕ):ℝ:=
 let v:=K+K
 worth k * Real.exp (worth k*(d*(2*M))) *
 (worth k*Real.exp (worth k*(6*DriftX a h v (d*(2*L)) k))*Real.exp (3*(worth k*(2*DriftX a h v (d*(2*K)) k))))
lemma budget_delta (v:Grove Z.frame S)(w:S.Nonempty)(p:Cop X Z f)(q:Cop X Z g)(t:∀ R,Disjoint S R→∀ x,X.moves R (f x) (g x))(a':0≤a)(hp:0≤h)
    {P C:D→Op n}{F:D→Wave n}{θ:D→ℂ}(H: Funds X O P C F θ a K c r) :∃ A:E→ FC n,Carries Z O S a h A (treasure a h K c r S.card Z.k) ∧ ∀ x, acts (A x) (F (f x))=F (g x):=by
 let V(x:D):= excite (P x) (C x); have hV(x): UnitR (V x):= unitR (H.parcel x).1 (H.parcel x).2.1 (H.parcel x).2.2
 let U(x:E):= -V (g x); let W(x:E):=exp (U x); let R(x:E):=exp (V (f x)); let B(x:E):=coupl (C (g x))-coupl (C (f x))
 let H':=K+K; have hx:0≤ H':=by obtain ⟨u,v,h,p,k,G⟩:= H.scope.hit; have hy:=p.posP; linarith
 have he(i:I n): Drop Z O a i (fun x=>unitL (U x) (pen i)) H':=by
    have hg:=Drop.seam i H.scope.nop q; convert hg using 1; funext i; simp only [Pi.neg_apply,mix_neg,exciteS]; rfl
 have hm(x): UnitR (U x):=unit_negR _ (hV _)
 set k:=Z.k; let m:= S.card
 let Y'(x:E):= quantX (P (f x)) (C (f x))-quantX (P (g x)) (C (g x))
 have hu: Carries Z O S a h (W*R) (Real.exp (3*(worth k*(2*DriftX a h H' (m*(2*K)) k)))):=by
    apply earned_t (A:=U) (B:=V ∘ f) (F:=Y') w v a' hp hx hm ?_ (peal (M:=fun i=>quantX (P i) (C i)) v p q t H.scope a') he (fun i=> (hV _).exhaust); funext x; change -_+V _=mix (_-_); rw [mix_less, exciteS,exciteS,add_comm]; rfl
 have hb:PairX Z O S a B (m*(2*c)):=by
    have T:=peal (S:=S) v p q t H.extra.nop a'; convert T using 1; funext x; simp only [Pi.neg_apply,mix_less,mix_neg,mix_put]; unfold B; abel
 have hB (x:E) : nilX (B x):=by
    rw [show B x=coupl (C (g x)-C (f x)) by unfold B coupl squareP; simp only [Matrix.sub_apply,sub_smul,sum_sub_distrib,smul_sub]]; exact coupl_nil _
 have hf:= paidJ (h:=h) w v a' hp hx hm hb hB he
 let L:=fun x=> W x* exp (B x) * R x; have hy':∀ x,exp (-U x)*exp (U x)=1:=fun x=>mul_eq_one_comm.mp (wind_inv _)
 have hy:L=(fun x=> exp (U x)*exp (B x)*exp (-U x))*(W*R):=by funext x; simp only [Pi.mul_apply]; unfold W L; rw [← mul_assoc, mul_assoc _ (exp (-U x)) (exp (U x)),hy',mul_one]
 let J(x:E):= θ (f x)- θ (g x) -- eq mapping require θf-θg (exp-phase in θdiff)
 have ht:= H.bonus.screen; obtain ⟨M,b,h,Hs,hQ⟩:=ht
 let M':= Cash.off S w v p q t M b h a' Hs hQ
 let C':= M'.embark a' w v
 let T:= hf.product hu w a' hp; rw [←hy] at T
 refine ⟨fun x=>Complex.exp (J x) • L x,?_,fun x=>?_⟩
 · have heq:= (C'.silent (A:=Complex.exp) (O:=O) (f:=J)).product T w a' hp; convert heq using 1; swap; rfl
   ext x s u
   change _=((Complex.exp _ • 1)*L x) s u; rw [Algebra.smul_mul_assoc,one_mul]
 have hw:= eqIn (H.parcel (f x)).1 (H.parcel (f x)).2.1 (H.parcel (f x)).2.2 (H.parcel (g x)).1 (H.parcel (g x)).2.1 (H.parcel (g x)).2.2
 rw [H.score,H.score] at hw; exact phaseEQ (J x) rfl hw rfl
end YM.CF.Acorn
