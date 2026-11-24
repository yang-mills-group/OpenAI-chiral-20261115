import GaugeFieldConstruction.HesperΛL
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Finset Mink MeasureTheory Analysis LineDeriv
open scoped BigOperators Topology ContDiff InnerProductSpace
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{B:∀ i, Blanket i}{F:Waves S}{X:Y.Aurora B}
variable {n:ℕ}(a:Axis)(f:Fin n→Test4)(k:Fin n)
noncomputable abbrev ΦshiftΛ (d:E4): Test4→L[ℂ]Test4:=lineDerivOpCLM ℂ _ d
lemma ΦsΛKnownL (d:E4)(f:Test4)(x:E4): ΦshiftΛ d f x=fderiv ℝ f x d:=by simp [ΦshiftΛ, SchwartzMap.lineDerivOp_apply_eq_fderiv]
lemma spotHasΛL (x:Points n): HasDerivAt (fun s:ℝ=>Joint.materialize n f (x+s • NSF.Points.direction k a)) (Joint.materialize n (Function.update f k (ΦshiftΛ (basis a) (f k))) x) 0:=by
 let C:= univ.erase k; let h:= (∏ i∈C,f i (x i)); let w(t:ℝ):=x+t • NSF.Points.direction k a
 simp only [Joint.material_at]
 have ht(A:Fin n→Test4)(p:Points n): (∏ i:Fin n,A i (p i))= A k (p k)*∏ i∈C,A i (p i):= (mul_prod_erase _ _ (mem_univ _)).symm
 simp_rw[ht]
 have he(s:ℝ): (∏ i∈C,f i ((x + s • NSF.Points.direction k a) i))=h:= prod_congr rfl (fun i hi=>by change _=f i (x i); simp [Points.direction, (mem_erase.mp hi).1])
 simp_rw [he,update_self] -- update self leaks RHS syntactic barrier
 rw [show (∏ i∈C,Function.update f k (ΦshiftΛ (basis a) (f k)) i (x i))=h from prod_congr rfl fun i hi=> by rw [Function.update_of_ne ((mem_erase.mp hi).1)]]
 simp only [Points.direction,PiLp.add_apply,PiLp.smul_apply,PiLp.single_eq_same]
 refine HasDerivAt.mul_const ?_ _
 let q(s:ℝ):= x k+s • basis a
 have hη:q 0=x k:=by simp[q]
 have hy:HasDerivAt q (basis a) 0:=by
    have H:= ((hasDerivAt_const (0:ℝ) (x k)).add ((hasDerivAt_id' (0:ℝ)).smul_const (basis a))); exact H.congr_deriv (by simp)
 have u:= ((f k).smooth 1 |>.differentiable (by simp) (q 0)).hasFDerivAt.comp_hasDerivAt 0 hy
 rw [hη,← ΦsΛKnownL] at u; exact u
lemma spotTestΛL : DriftΛL (NSF.Points.direction k a) (Joint.materialize n f)= Joint.materialize n (Function.update f k (ΦshiftΛ (basis a) (f k))):= by
 ext1 x; rw [DriftΛKnownL]
 have hp: DifferentiableAt ℝ (Joint.materialize n f) x:= ((Joint.materialize n f).smooth 1).differentiable (by simp) x
 exact (hp.hasFDerivAt.hasLineDerivAt _).unique (spotHasΛL a f k x)

variable (D:Axis→Axis→ S.Union)(w:ConsWΛL Y D)
include w
lemma ΩspotΛL (V:Fin n→ Letter S): (∑ i:Axis,Y.expect (List.ofFn (Function.update V k (D i a, ΦshiftΛ (basis i) (V k).2))))=0:=by
 simp_rw [NSF.Work.C29.expectOfFn, Function.comp_update]
 have u:= w.lives n (Prod.fst∘ V) a k (f:=(Joint.materialize n (Prod.snd ∘ V))) -- adjust.
 simp_rw [spotTestΛL] at u; exact u
omit w in
private lemma insertLiveΛL {m n : ℕ} {α : Type*} (v : Fin m → α) (w : Fin n → α) (x y : α) :
    Function.update (Fin.append v (Fin.cons x w)) (Fin.natAdd m 0) y = Fin.append v (Fin.cons y w) := by -- Uses argument C29.
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have h : Fin.castAdd (n+1) i ≠ Fin.natAdd m 0 := by
      apply Fin.ne_of_lt
      exact (show i.val < m + 0 by simp)
    simp [h]
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.natAdd_inj]
lemma VeqΩΛL (z:Letter S)(v l:Sentence S): (∑ i:Axis,Y.expect (v++(D i a,ΦshiftΛ (basis i) z.2)::l))=0:=by
 have h:= ΩspotΛL a (Fin.natAdd v.length 0) D w (Fin.append v.get (Fin.cons z l.get)); simpa only [Fin.append_right, Fin.cons_zero, insertLiveΛL,List.ofFn_fin_append,List.ofFn_cons,List.ofFn_get] using h
omit w
variable (R:Fields S)(e:R.Total)
local notation "XΩ"=> R.domain
include e
lemma ΓEyesΛL (p q:XΩ)(h:∀ b:Sentence S, inner ℂ (R.evaluates b) p= inner ℂ (R.evaluates b) q): p=q:=by
 apply ext_inner_left ℂ; intro i
 have he: ∀ (i:R.H), i ∈ Submodule.span ℂ (Set.range R.vector)→ inner ℂ i p.val = inner ℂ i q.val := by
    intro x v
    apply Submodule.span_induction (p:=fun i _=> inner ℂ i p.val = inner ℂ i q.val) ?_ ?_ ?_ ?_ v
    · rintro y ⟨d,rfl⟩; exact h d
    · simp
    · intro a b x y h l; simp [inner_add_left,h,l]
    intro c b y l; simp [inner_smul_left,l]
 exact he i.val (e.cyclic ▸ i.property)
lemma DrivesΛL {M V:XΩ→ₗ[ℂ]XΩ}(g:∀ b:Sentence S,M (R.evaluates b)=V (R.evaluates b)): M=V:=by
 have H(x:R.H)(h:x∈Submodule.span ℂ (Set.range R.vector)): ∀ (p : XΩ), p.val=x→ M p=V p:=by
    apply Submodule.span_induction (p:=fun i _=> ∀ p:XΩ,p.val=i→M p=V p) ?_ ?_ ?_ ?_ h
    · rintro y ⟨c,rfl⟩ p k; rw [show p=R.evaluates c from Subtype.ext k,g]
    · intro p k; rw [show p=0 from Subtype.ext k,map_zero,map_zero];
    · intro x y u z s f p k; let a:XΩ:=⟨x,e.cyclic.symm ▸ u⟩; let b:XΩ:=⟨y,e.cyclic.symm ▸ z⟩; rw [show p=a+b from Subtype.ext k,map_add,map_add,s a rfl,f b rfl];
    intro c x u s p k; let a:XΩ:=⟨x,e.cyclic.symm ▸ u⟩; rw [show p=c • a from Subtype.ext k,map_smul,map_smul,s a rfl];
 exact LinearMap.ext fun x=> H x.val (e.cyclic ▸ x.property) x rfl
include w
lemma ΓWardHereΛL (a:Axis)(J:StarOp S)(q:R.sharpPair J)(m:R.realizes Y)(b:Test4): (∑ i:Axis,R.field (D i a) (ΦshiftΛ (basis i) b))=0:=by
 apply DrivesΛL R e; intro c; apply ΓEyesΛL R e; intro k
 rw [LinearMap.sum_apply,inner_sum,LinearMap.zero_apply,inner_zero_right]
 change (∑ i:Axis,inner ℂ (R.evaluates k) (R.evaluates ((D i a, ΦshiftΛ (basis i) b)::c)))=_
 have he (v):inner ℂ (R.evaluates k) (R.evaluates v)=Y.expect (Sentence.rev J k ++ v):= R.general Y m J q k v
 simp_rw [he]; exact VeqΩΛL a D w (0,b) (Sentence.rev J k) c
#print axioms ΓWardHereΛL
end YM.NSF.Boundary
