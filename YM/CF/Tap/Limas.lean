import YM.CF.Tap.Cerf
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
abbrev KinX(x:E) : Pal:= (1:Op SpinIdx)⊗ₖ (matter x).val
def AxSym(W: Momentum → Pal):Prop:= ∀ s:Signed,∀ b:Bool,∀ U:UNI SpinIdx,JetS s b (detX s) U→∀ p∈baseCube,sings b (twoU U b) (W (cadence s b p))= Thera.jazz (detX s) (W p)
structure AxisP(W:Momentum→Pal):Prop where
 rise: AxSym W
 hold: ∀ g:SU.E,∀ p∈baseCube,Commute (W p) (KinX g)
 age: ∀ i:Axis,DifferentiableAt ℝ (fun z=>W (bout i z)) 0
variable {W:Momentum→Pal}
variable (j:ℕ)(k:1≤j)(M:Male)
def potion(W:Momentum→ Pal)(p:Momentum):Pal:= (1-boot j M p)* W p * boot j M p
private lemma P_c (s:Signed)(b:Bool)(U:UNI SpinIdx)(v:JetS s b (detX s) U)(p:Momentum)(h:p∈baseCube):sings b (twoU U b) (boot j M (cadence s b p))=swapX (detX s) (boot j M p):=by
 rw [boot,Scroll.wingK,show sings b U (bar _ _ (cadence s b p))= bent ((detX s).xor true) j M.val p from bent_s v _ M.property p h true j,show sings b _ 1=1 by rw [singT,win_i,map_one]]
 cases hx:detX s; rfl
 change (1-bar j M.val p)⊗ₖ _=1-(bar _ _ p⊗ₖ _); rw [sub_eq_add_neg,Matrix.add_kronecker,Matrix.one_kronecker_one, op_kron_neg, sub_eq_add_neg]
include k
lemma Psy (h:AxisP W):AxisP (potion j M W):=by
 refine ⟨fun s b U v p hp=>?_,fun g p hp=>?_,fun i=>?_⟩
 · let X:=W p; unfold potion; rw [singm,singm,h.rise s b U v p hp, show sings _ _ (1- _)=1-sings b (twoU U b) (boot j M (cadence s b p)) by rw [singT,win_l,win_i,map_sub,map_one,singT],P_c j M s b U v p hp]
   let V:=boot j M p; have hv : star V=V:=by unfold V boot; rw [op_star_kron,(firm_bar j M.val M.property (base_subset_realCube zone_pos hp)).2,star_one]
   cases hx:detX s; rfl
   change (1-(1-V)) * (-star X) * (1-V)= -star ((1-V)*X*V); rw [star_mul,star_mul,star_sub,hv,star_one]; simp [mul_assoc]
 · have hp': Commute (boot j M p) (KinX g):=by unfold Commute SemiconjBy boot KinX; rw [op_kron_mul,op_kron_mul,one_mul,one_mul,mul_one,mul_one]
   exact Commute.mul_left ((Commute.one_left _ |>.sub_left hp').mul_left (h.hold _ _ hp)) hp'
 exact (((differentiableAt_const 1).sub (barox j k M i).differentiableAt).mul (h.age i)).mul (barox j k M i).differentiableAt
private def lode (b:Bool)(U:UNI (coneA Slot)): Pal→L[ℝ] Pal:= (show Pal →ₗ[ℝ] Pal from ⟨⟨fun x=>sings b U x,fun x y=>by simp only [singT,win_a,map_add]⟩,fun r x=>by change sings _ _ (r • x)=r • sings _ _ x; simp only [singT,win_r,map_smul]⟩).toContinuousLinearMap
private def joust(b:Bool):Pal→L[ℝ] Pal:=(show Pal→ₗ[ℝ] Pal from ⟨⟨fun x=> Thera.jazz b x,fun x y=>by cases b; rfl; change -star _ = -star _ + -star _; rw [star_add,neg_add]⟩,fun r x=>by cases b; rfl; change -star (r • x)=r • (-star _); rw [star_smul,star_trivial, smul_neg]⟩).toContinuousLinearMap
omit k
private lemma steep (s:Signed)(b:Bool)(i:Axis)(t:ℝ): bout (s.perm i) (hush (b.xor (s.flip i)) t)= cadence s b (bout i t):=by
 funext a; obtain ⟨m,rfl⟩:= s.perm.surjective a
 unfold bout; cases b<;>cases h:s.flip i<;>cases f:s.flip m<;> by_cases hx:m=i <;>simp_all [cadence] -- tune
private lemma steep_r (W:Momentum→ Pal)(e:AxisP W)(s:Signed)(b:Bool)(U:UNI SpinIdx)(hp:JetS s b (detX s) U)(i:Axis): sings b (twoU U b) (deriv (fun t=> W (bout (s.perm i) t)) 0) = Thera.jazz (detX s) (hush (b.xor (s.flip i)) (deriv (fun t=> W (bout i t)) 0)):=by
 let l:=lode b (twoU U b); let p:= joust (detX s)
 let r:= b.xor (s.flip i); let f(z):=W (bout i z); let g(z):=W (bout (s.perm i) z); let y(t:ℝ):=hush r t
 have hx: (p ∘ f)=ᶠ[𝓝 (0:ℝ)] l ∘ g ∘ y:=by filter_upwards [bout_v i] with t ht; change Thera.jazz _ _=sings _ _ (W (bout _ _)); unfold y r; rw [steep]; exact (e.rise s b U hp _ ht).symm
 have ht := p.hasFDerivAt.comp_hasDerivAt (0:ℝ) (e.age i).hasDerivAt
 have hm:=e.age (s.perm i)
 cases hv:r
 · rw [show y=id from funext (fun i=>by simp [y,hv])] at hx; have hg := l.hasFDerivAt.comp_hasDerivAt (0:ℝ) (e.age (s.perm i)).hasDerivAt; change (l _)=(p _) -- tune
   change b.xor (s.flip i)=false at hv; rw [hv]; exact (hg.congr_of_eventuallyEq hx).unique ht
 rw [show y=(fun t:ℝ=> -t) from funext (fun i=>by simp [y,hv])] at hx
 have hk: HasDerivAt (fun t:ℝ=> -t) (-1) 0:=(hasDerivAt_id' (0:ℝ)).neg
 have hg:HasDerivAt (g ∘ Neg.neg) (-deriv g 0) 0:=by
    have ht : HasDerivAt g (deriv g 0) (- (0:ℝ)):=by rw [neg_zero]; exact hm.hasDerivAt
    exact (ht.scomp (0:ℝ) hk).congr_deriv (by simp)
 have hd := (l.hasFDerivAt.comp_hasDerivAt (0:ℝ) hg).congr_of_eventuallyEq hx
 have hy : l (-deriv g 0)=p (deriv f 0):=hd.unique ht; rw [map_neg] at hy
 change l (deriv g 0)=p (hush r _); rw [hv,hush_true,map_neg] -- tune
 exact neg_eq_iff_eq_neg.mp hy
private lemma jar (P Q:Pal)(z:E)(f:ℝ→Pal)(e:HasDerivAt f Q 0)(h:∀ᶠ t in 𝓝 (0:ℝ), Commute (f t) (KinX z)):Commute Q (KinX z):= (e.mul_const _).unique ((e.const_mul _).congr_of_eventuallyEq h)
def zest(W:Momentum→ Pal)(i:Axis): Pal:= deriv (fun t=> potion j M W (bout i t)) 0
def zeus(W:Momentum→Pal):Op Slot:= spaX (zest j M W 0) 0
include k
lemma normalization (h:AxisP W): potion j M W 0=0 ∧ Mind (zeus j M W) ∧∀ i,zest j M W i=petal i ⊗ₖ zeus j M W:=by
 let P:=potion j M W; let e:=Psy j k M h
 let A:=bins Slot; have ha:A*A=A:=binsSq _; let B:=1-A; have hb:B*B=B:=by unfold B; rw [sub_mul,one_mul,mul_sub,mul_one, ha]; abel
 have hc :P 0=A * W 0 * B:=by unfold P potion; rw [boot_o,sub_sub_cancel]
 have he:P 0=0:=by
    apply first_n; unfold Binned; change A * _ * B=_; rw [hc,← mul_assoc A, ← mul_assoc,ha,mul_assoc _ B, hb]
    intro s hv; have hx:=(Psy j k M h).rise s false (spinX s) (bud_s _) 0 (by simpa [bout_zero] using bout_h 0 0 (by norm_num)); rw [hv,show cadence s false 0=0 from (Cad s false).map_zero] at hx; exact hx
 refine ⟨he,color_all (zest j M W) (fun i=>?_) (steep_r P e) (fun i z=> jar 0 (zest j M W i) z (fun t=>P (bout i t)) (e.age i).hasDerivAt (by filter_upwards [bout_v i] with t ht using e.hold z _ ht))⟩
 let V(t):= boot j M (bout i t); let X(t):=P (bout i t); let T(t):=1-V t
 have hV : (T*X*V)=ᶠ[𝓝 0] X:=by
    filter_upwards [Ps_b j k M i] with t ht; have hx:V t*V t=V t:=ht.1; have hm:T t * T t=T t :=by unfold T; rw [sub_mul,one_mul,mul_sub,mul_one,hx]; abel
    change T t*(T t*_ *V t) *V t=X t; rw [← mul_assoc (T t),← mul_assoc, hm,mul_assoc (T t*_),(hx)]; rfl
 have hv:=barox j k M i; have hz:HasDerivAt X (zest j M W i) 0:=(e.age _).hasDerivAt; have hp' : X 0=0:=by unfold X; rw [bout_zero,he]
 have hT : HasDerivAt T (-boom i) 0:= hv.const_sub 1 -- tune
 have hd:=(((hT.mul hz).mul hv).congr_of_eventuallyEq hV.symm).unique hz; change ((_ * X 0 + T 0 * _) * V 0 + (T*X) 0 * _) = _ at hd; unfold Binned; rw [Pi.mul_apply,hp',mul_zero,mul_zero,zero_add, zero_mul,add_zero] at hd; simp only [T,V,bout_zero,boot_o] at hd; simpa using hd
end YM.CF.Tap
