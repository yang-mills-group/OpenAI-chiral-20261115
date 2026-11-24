import YM.CF.Emu.Fade
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Pic Nova Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc MeasureTheory
variable {α:Type*}{N:Side}{o:Site N}{L B:Side}{j n:ℕ}{O:Odd L.val}{Y:Pricing j L O (Thread j)}{e b c v K a l r τ w u:ℝ}{P:Grasp Y B e}{H:Pearl P}{M:Jill.Male}{F':E}{m:Side}{f:ℕ→Side}{R T W:ℕ→ℝ}
-- plot cost paid before normalization as well
abbrev aj(V:Side)(f:ℕ→Side)(i:ℕ):= CSide (f i) V
abbrev Sep(U:Side)(f:ℕ→Side)(i:ℕ):=Domain (f i) U
variable (D:Span H K b v c l r n)
local notation "N'"=> CSide m B
local notation "A'"=> Greek N'
include D
theorem orbQ (u':n ≤ (N').val)(U:Bkg (Domain m B))(q:wit m B)(y:Stock U P M q (K*A') w)(g:Cart (Domain m B))(d:Candle)(h:slowT (Domain m B) d)(t:lawnK (gauge g U) (Kea.tax d) τ)(p:τ>0)(l:τ≤1)(s:A'^10*τ≤ min v 1)(x:ℂ)(o:Site N')(j:α→TagT)(L:List α)(F:E)(R:ℝ)(e₀:F'=g (node o)*F)
 (a b':ℝ)(hw:0≤w)(hp:Pays (K*A') (zoneA o U F R j L) a)(hq:Pays (K*A') (zoneA o (gauge g U) F' R j L) a)(hx:Pays (K*A') (zoneA o (gauge g U) F' R j L-zoneA o (Kea.tax d) F' R j L) b'):
 let I:=Kea.angel m P M; ‖wall o U F R j L q x-wall o (Kea.tax d) F' R j L (changeM (m:=m) P (Kea.tax d) M) x‖≤ ((a+‖x‖)*w*(2*c)+(a+‖x‖)*(c*A'^10*τ)+b'*c)*I:=by
 intro I; let Y:=gauge g U; let M'(z:Bkg (Domain m B))(i:E)(T:wit m B):=wall o z i R j L T x; let P' := fun x=> changeM (m:=m) P x M
 let W:=Kea.tax d (N:=Domain m B); have he:=emerge D u' M U g d h t p l s q y; have hg:0<I:=angel_p H D.stmt (D.plan _ u').1 D.p D.eP _ (D.plan _ u').2
 have hu:= D.pale _ u' M d h _ τ p l (s.trans (min_le_left ..)) t; have ht:0<c:= zero_lt_one.trans_le D.cP; have hv:0<A':= nPos _
 change ‖M' U F q-M' W F' (P' W)‖≤ _; refine (norm_sub_le_norm_sub_add_norm_sub _ (M' U F (P' U)) _).trans ?_
 have hy : M' U F (P' U)= M' Y F' (P' Y):=by rw [e₀]; exact (noteR D u' U he.1 g _ _ _ _ _ _ _).symm
 have hj:‖M' W F' (P' W)-M' Y F' (P' W)‖≤ b'*(c*I):=by
    rw [norm_sub_rev]; unfold M' wall matchF; rw [sub_sub_sub_cancel_right, ← inner_sub_right,←act_sub]; apply kem _ hx (by positivity); exact (D.powV _ u' M d (skim N' d)).2.2.2
 refine (add_le_add (bon (show 0≤ w*(2*c*I) by positivity) he.2.2.1 _ _ _ _ _ _ hp x) (d:=(a+‖x‖)*(c*A'^10*τ*I)+b'* (c*I)) ?_).trans (le_of_eq (by ring)); rw [hy]; refine (norm_sub_le_norm_sub_add_norm_sub _ (M' Y F' (P' W)) _).trans (add_le_add (bon (show 0≤ c*A'^10*τ*I by positivity) hu.2 _ _ _ _ _ _ hq x) ((norm_sub_rev ..).trans_le hj)) -- order metavars
-- scaled schedule witness costs eventually. T small all required moments (else statement per test)
structure BeamG (D:Span H K b v c l r n)(f:ℕ→Side)(T W:ℕ→ℝ)(k:ℕ):Prop where
 ok:∀ᶠ i in atTop, n ≤ (aj B f i).val ∧ 0< T i ∧ T i ≤1∧ Greek (aj B f i)^10*T i ≤ min v 1∧0 ≤ W i
 wave:Tendsto (fun i=>Greek (aj B f i)^(10+k)*T i) atTop (𝓝 0)
 fine:Tendsto (fun i=>Greek (aj B f i)^k *W i) atTop (𝓝 0)
lemma reshot(Q: Plot α R)(J:List α)(y:Yard (aj B f) R)(t:BeamG D f T W (3*J.length))(o:∀ i,Site (aj B f i))(M:ℕ→Jill.Male)(U:∀ i,Bkg (Sep B f i))(q:∀ i,wit (f i) B)(Z:ℕ→E)(p:∀ᶠ i in atTop, Stock (U i) P (M i) (q i) (K*Greek (aj B f i)) (W i)∧∃ g:Cart (Sep B f i),∃ d:Candle,speedB d (Sep B f i)∧ lawnK (gauge g (U i)) (Kea.tax d) (T i)): Tendsto (fun i=>wall (o i) (U i) (Z i) (R i) (Q.pal i) J (q i) (runes Q.rho J)/(Kea.angel (f i) P (M i):ℂ)) atTop (𝓝 0):=by
 have hf :∀ i,Nonempty (Cart (Sep B f i) × Candle):=fun i=>⟨1,emptyC⟩ -- tune
 obtain ⟨u,w⟩:=budgetO (I:=fun i=> Cart (Sep B f i) × Candle) (fun i t=>speedB t.2 (Sep B f i)∧ lawnK (gauge t.1 (U i)) (Kea.tax t.2) (T i)) (p.mono fun i he=>by obtain ⟨_,g,d,T,E⟩:=he; exact ⟨(g,d),T,E⟩)
 let d i:=(u i).2; let V i :Bkg (Sep B f i):=Kea.tax (d i); let F(i):= changeM (m:=f i) P (V i) (M i); let X(i):=skim (aj B f i) (d i); let G(i):= (u i).1 (node (o i))*Z i; let I(i):= Kea.angel (f i) P (M i); let A(i):ℂ:=I i
 let a:=runes Q.rho J; let x(i)(p:Bkg (Sep B f i))(v:E)(q:wit (f i) B):ℂ:=wall (o i) p v (R i) (Q.pal i) J q a/A i
 have he:Tendsto (fun i=> x i (V i) (G i) (F i)) atTop (𝓝 0):=by
    let B'(i):ℂ:= iceK j (X i) (M i) r; let L(i):ℂ:=wall (o i) (V i) (G i) (R i) (Q.pal i) J (F i) a
    have hp:∀ᶠ i in atTop,Sea (Dofu (aj B f i) (field (X i) j (M i))) (F i):=by filter_upwards [t.ok] with i hi; obtain ⟨m,h⟩:=D.plan _ hi.1; rw [← h.2 (d i)]; exact sea_g m _ (tax_guard (d i) _ _ D.eP.le) _
    have hz:Tendsto (fun i=>L i/B' i) atTop (𝓝 0):=by unfold L; simp_rw [stax]; exact Q.hoot d X M G o y F hp D.p D.rP J
    apply (payM c hz (g:=fun i=>B' i/A i) ?_).congr
    · intro i; have he:B' i≠0:= by unfold B'; exact_mod_cast (ice_p _ _ _ D.rP).ne'
      change _= L i / A i; change (B' i / A i)*(L i/B' i)=_; rw [div_mul_div_comm]; field_simp
    filter_upwards [t.ok] with i hi; have hx:0<I i:=angel_p H D.stmt (D.plan _ hi.1).1 D.p D.eP _ (D.plan _ hi.1).2; unfold B' A; rw [norm_div,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hx.le,Real.norm_of_nonneg (ice_p _ _ _ D.rP).le]; exact (div_le_iff₀ hx).2 (D.powV _ hi.1 (M i) _ (X i)).2.1
 suffices H:Tendsto (fun i=>x i (U i) (Z i) (q i)-x i (V i) (G i) (F i)) atTop (𝓝 0) by simpa only [sub_add_cancel,zero_add] using H.add he
 obtain ⟨C,h,hv⟩:=Emu.pay_v Q J y D.kP; let n'(i):= Greek (aj B f i); let L:=3*J.length
 let g(i):ℝ:=n' i^(10+L)*T i; let w'(i):= n' i^L * W i
 rw [tendsto_zero_iff_norm_tendsto_zero]; let K(i):=(C+‖a‖)*2*c*w' i+((C+‖a‖)*c+C*c)*g i
 refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) (g:=K) ?_ ?_; rotate_left
 · simpa only [K,mul_zero,add_zero] using (t.fine.const_mul ((C+‖a‖)*2*c)|>.add (t.wave.const_mul ((C+‖a‖)*c+C*c))) -- tune
 filter_upwards [t.ok,hv,p,w] with i hi hZ l m; let k:= n' i; have hK:1 ≤k:=by unfold k n' Greek; exact_mod_cast (aj B f i).property
 obtain ⟨w₀,p₀,v,l',z⟩:=hi; let U':=C*k^L; let B':=C*k^(L+1)*T i; obtain ⟨s,s'⟩:= hZ (o i) (gauge (u i).1 (U i)) (V i) (G i); have ht:=orbQ D w₀ (U i) (q i) l.1 (u i).1 (d i) (spiral _ m.1) m.2 p₀ v l' a (o i) (Q.pal i) J (Z i) (R i) rfl U' B' z (hZ (o i) (U i) (V i) (Z i)).1 s (s' (T i) p₀.le m.2); unfold x A; have he:0<I i:=angel_p H D.stmt (D.plan _ w₀).1 D.p D.eP _ (D.plan _ w₀).2; rw [←sub_div,norm_div,Complex.norm_real,Real.norm_of_nonneg he.le]; rw [div_le_iff₀ he]; apply ht.trans; refine mul_le_mul_of_nonneg_right ?_ he.le
 have hy: U'+‖a‖≤ (C+‖a‖)*k^L:=by unfold U'; rw [add_mul]; apply add_le_add (le_refl _); exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hK)
 have hh:B'≤ C*k^(10+L)*T i:=by unfold B'; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK (show L+1 ≤10+L by omega)) h.le) p₀.le
 unfold K g w'; change _≤ (C+_)*2*c*(k^L*_)+_*(k^(10+L)*_); rw [pow_add k]; let d:=D.cP
 -- calc
 apply le_trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hy z) (by positivity)) (mul_le_mul_of_nonneg_right hy (by change 0 ≤ c*k^10*T i; positivity))) (mul_le_mul_of_nonneg_right hh (zero_le_one.trans D.cP)))
 rw [pow_add]; apply le_of_eq; ring
end YM.CF.Emu
