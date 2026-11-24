/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Tap.Tub
import YM.Push.LOOP_COEFFICIENT.ReadJets
import YM.CF.Matter.Anomaly
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (j m:ℕ)(p:1≤j)(M:Male)
def Paw (b:Bool)(z:Cover):Pal:= tub (bent b j M.val) z ⊗ₖ 1
def Tern(K:Cover→Pal): Cover → Pal:= foldY (foldY (Paw j M false) K) (Paw j M true)
private lemma glory (b:ℝ)(g:0<b):∃ V:ℝ,0<V∧∀ d:Cover,tweight m d≤ V*Real.exp (b*Laurent.size d):=by
 let y:=b/(m+1); let V:= max 1 y⁻¹; have hy:0<y:=div_pos g (by positivity); have hk:0<V:=zero_lt_one.trans_le (le_max_left ..)
 refine ⟨V^m,pow_pos hk _,fun d=>?_⟩; let x:ℝ:= Laurent.size d; have hp:0≤x:=Nat.cast_nonneg _
 change (1+x)^m≤ _ * Real.exp (b*x); rw [show b*x=m*y*x+y*x from ?_,Real.exp_add,mul_assoc] -- tune
 · calc (1+x)^m≤ (V*Real.exp (y*x))^m:=by
             have hx : x ≤ V*(y*x) := by rw [←mul_assoc]; exact le_mul_of_one_le_left hp ((inv_le_iff_one_le_mul₀ hy).mp (le_max_right ..))
             refine pow_le_pow_left₀ (by positivity) ?_ m
             have hV: 1≤V:=le_max_left ..
             nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y*x)) hk.le]
        _ ≤ _:=by rw [mul_pow, ←Real.exp_nat_mul, ←mul_assoc]; gcongr; exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
 unfold y; field_simp
include p
lemma hel_pawn (b:Bool):Reads (Paw j M b) (fun x=> (if b then boot j M x else 1-boot j M x)):=by
 let F:=tub (bent b j M.val); have he:= cBar j M.val b p M.property
 have ht(x): (if b then boot j M x else 1-boot j M x)=bent b j M.val x⊗ₖ (1:Op Slot):=by
    cases b; swap; rfl
                                                                           -- align
    change 1-boot j M x=(1-bar j M.val x)⊗ₖ _; rw [sub_eq_add_neg 1 (bar _ _ _), Matrix.add_kronecker, Matrix.one_kronecker_one, op_kron_neg, sub_eq_add_neg]
 constructor
 · rintro ⟨x,l⟩ ⟨y,k⟩; change Summable (fun d=> ‖Paw j M b d _ _‖); simp only [Paw,Matrix.kronecker_apply,norm_mul]; exact (he.sumK ..).mul_right _
 rintro x g ⟨i,l⟩ ⟨j',c⟩; rw [ht, Laurent.read]; simp only [Paw,Matrix.kronecker_apply,smul_eq_mul, ←mul_assoc,tsum_mul_right]; rw [←he.readK x g i j']; rfl
lemma pawn_p (q:Bool): ∃ C:ℝ,0<C∧∀ M:Male,RailP m (Paw j M q) C:=by
 obtain ⟨⟨η,C,h,hC,H⟩,hg⟩:= tub_bill (bent_budget q j p (fun i:Male=>i.val) (fun i=>i.property)) (fun i x g v t=> by unfold Fir.bent; rw [bar_overlap _ _ g v t])
 obtain ⟨D,hd,ht⟩:=glory m η h
 refine ⟨D*C,mul_pos hd hC,fun M ⟨b,i⟩ ⟨z,k⟩=>?_⟩; let f(l:Cover):=Paw j M q l (b,i) (z,k); by_cases hz:i=k; swap
 · have hp(l): f l=0:=by simp [f,Paw,hz]
   change Cp _ f _; simp only [Cp,hp,norm_zero,mul_zero]; exact ⟨fun _=>le_rfl,summable_zero,by simp; positivity⟩
 have he: Width η C f:=by unfold f Paw; simp only [hz, Matrix.kronecker_apply,Matrix.one_apply_eq, mul_one]; simpa only [mul_one] using H M b z
 let F(x):=Real.exp (η*Laurent.size x)*‖f x‖
 apply Work.F08.budget_minor (show RG.SumBudget (fun x=> D*F x) _ from ⟨fun x=>mul_nonneg hd.le (he.1 _),he.2.1.mul_left D,by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left he.2.2 hd.le⟩) (fun _=>mul_nonneg (tw_pos ..) (norm_nonneg _)); intro x; change _≤ D*( _*_); rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (ht x) (norm_nonneg _)
lemma snapP{N:Side}(b:Bool):love N (cart N (Paw j M b)) = skewE j M b N 1:=by
 rw [skew_flat j p]; ext ⟨⟨x,i⟩,a⟩ ⟨⟨y,l⟩,c⟩; change (Rush.cart N _) (x,i,a) (y,l,c) = _; simp only [Rush.cart,Paw,wagon_app,Matrix.of_apply,Matrix.kronecker_apply,← mul_assoc, ←tsum_mul_right, ite_mul,zero_mul]
lemma winP {N:Side}(W:Cover→Pal)(a:ℝ)(h:RailP m W a):let V:=funde j M N 1; (1-V)*love N (cart N W)*V=love N (cart N (Tern j M W)):=by
 obtain ⟨C,_,u⟩:= pawn_p j m p false; obtain ⟨A,_,v⟩:=pawn_p j m p true
 let P:=Paw j M false; let Q:=Paw j M true; have hp:=readsP h
 intro V; rw [show V=love N (cart N Q) from (snapP j p M true).symm] -- also 1-V.
 have ht: 1-V= love N (cart N P):=(snapP j p M false).symm
 rw [show 1-(love N (cart N Q))=love N (cart N P) from ?_]; swap; · rw [show love N _=V from snapP j p M true]; exact ht
 rw [← map_mul, ←map_mul]; apply congr_arg; unfold Tern P Q; rw [cart_traded hp,cart_traded (hel_pawn j p M true), cart_traded (hel_pawn j p M false), cart_traded (reads_fold (foldYP (u M) h) (v M) (reads_fold (u M) h (hel_pawn j p M false) hp) (hel_pawn j p M true)),pilesP,pilesP]
omit p
open YM.Push.Loops
private lemma step_i(i:Axis): (step i:Momentum)=unitAxis i:=by ext a; simp [unitAxis,Lattice.step_apply,eq_comm,Pi.single_apply]
variable {m}
lemma moments{f:Cover→ℂ}{a:ℝ}(h:Cp m f a)(p:1≤m)(i:Axis): Summable (fun x:Cover=> (x i:ℂ)* f x)∧HasDerivAt (fun t=> Laurent.read f (bout i t)) (Complex.I* ∑' x:Cover, (x i:ℂ) * f x) 0:=by
 let d (x:Cover)(t:ℝ):= Laurent.mode (bout i t) x*(Complex.I*(x i:ℂ))*f x
 let F(x:Cover)(t:ℝ):= Laurent.mode (bout i t) x*(f x)
 have hs(x:Cover): (Laurent.size x:ℝ) ≤ tweight m x:=by unfold tweight; refine le_trans ?_ (pow_le_pow_right₀ (show 1 ≤ (1:ℝ)+Laurent.size x from by simp) p); simp
 have hx(x t):‖d x t‖≤ tweight m x*‖f x‖:=by
    unfold d; rw [norm_mul, norm_mul, norm_mul,Complex.norm_I,one_mul, Laurent.mode_real,one_mul]; exact mul_le_mul_of_nonneg_right ((axis_le_size ..).trans (hs x)) (norm_nonneg _); ext a; by_cases h:a=i <;> simp [h,bout] --  [bout,mul_ite]
 refine ⟨Summable.of_norm_bounded h.2.1 (fun x=>by rw [norm_mul]; exact mul_le_mul_of_nonneg_right ((axis_le_size ..).trans (hs x)) (norm_nonneg _)),?_⟩
 have he(x t):HasDerivAt (F x) (d x t) t:=by
    unfold F d; simp_rw [bout,step_i]
    have ht:= (mode_ray_deriv i x t).scomp t (show HasDerivAt (fun x:ℝ=>(x:ℂ)) 1 t from Complex.ofRealCLM.hasFDerivAt.hasDerivAt); apply HasDerivAt.mul_const _; exact ht.congr_deriv (by simp)
 have hh:= hasDerivAt_tsum (g:=F) h.2.1 he hx (y₀:= (0:ℝ)) (by unfold F; simp_rw [bout_zero,mode_constant, one_mul]; exact h.falls.2.1.of_norm) 0
 unfold d at hh; simp_rw [bout_zero,mode_constant,one_mul, mul_assoc, tsum_mul_left] at hh; exact hh
structure NullW(W:Momentum→Pal): Prop where
 still: W 0=0
 free:∀ i, HasDerivAt (fun v=>W (bout i v)) 0 0
lemma valueK {T:Momentum→ Pal}{X:Cover→ Pal}{a:ℝ}(h:Reads X T)(p:NullW T)(s:RailP m X a)(q:1≤m)(a b): (∑' x,X x a b)=0∧∀ i:Axis, (∑' x: Cover,(x i:ℂ)* X x a b)=0:=by
 constructor
 · have hp:= h.readK 0 (by simpa [bout_zero] using bout_h 0 0 (by norm_num)) a b; simpa [Laurent.read,p.still] using hp
 intro i; have he: HasDerivAt (fun v:ℝ=> T (bout i v) a b) 0 0:= op_deriv.mp (p.free i) a b
 have hx := ((moments (s a b) q i).2.congr_of_eventuallyEq (by filter_upwards [bout_v i] with v hv using (h.readK (bout i v) hv a b).symm)).unique he
 exact (mul_eq_zero.mp hx).resolve_left Complex.I_ne_zero
end YM.CF.Tap
