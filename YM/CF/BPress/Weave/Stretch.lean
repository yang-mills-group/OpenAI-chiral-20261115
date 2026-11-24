import YM.CF.BPress.Weave.Quay
import YM.CF.BPress.Wealth.Higher
/-! polynomial and override. Real CLM conventions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson RG Precision Grid Cube Bands Tunnel Pressure Wealth Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
-- helper generic for ℝ
variable {s:Side}{B:BandWidth}(X:Bands s B) (S:Finset X.Hcols)
-- Abstract calculus
variable (A F: BEnd X)(p r :ℝ)(n:ℕ)
def incomeT := 1-p⁻¹ • A
def rotateT : BEnd X:= peak p • ∑ i∈ range (n+1),SignScalar.c i • (incomeT X A p)^i
def stretch := rotateT X A p n+(1-shortA p n 1) • keeper X S
lemma blink (v:RaySpace X)(z:ℝ)(e:Flare A v z): Flare (rotateT X A p n) v (shortA p n z):=(Flare.rays (range (n+1)) _ (_) (fun i _=> (((Flare.one (v:=v)).sub (e.scale p⁻¹)).pow i).scale (SignScalar.c i))).scale _
-- global support severed
structure Whole (A:BEnd X) (d:ℝ):Prop where
 self : IsSelfAdjoint A
 agrees (v:RaySpace X) : Flare A (keepOnly X S v) d
namespace Whole
variable {X A S F p n}{d c:ℝ}
lemma mask_self : IsSelfAdjoint (keeper X S):= ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y=> ray_mask X S x y
lemma mask : Whole X S (keeper X S) 1:= ⟨mask_self, fun i=>by unfold Flare; rw [one_smul]; exact id_mask ..⟩
lemma reads (h:Whole X S A d)(v:RaySpace X) : keepOnly X S (A v)=d • keepOnly X S v:=by
 refine ext_inner_left ℝ fun y=>?_ ; rw [← ray_mask,real_inner_smul_right,←ray_mask X S y v] -- tune
 · change _ = _; rw [← (show inner ℝ (A (keepOnly X S y)) v= inner ℝ (keepOnly X S y) (A v) from (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp h.self) (keepOnly X S y) v), show A _=_ from h.agrees y]; simp [real_inner_smul_left,real_inner_smul_right]
lemma complement (h:Whole X S A d)(v:RaySpace X): A (keepOnly X Sᶜ v)=keepOnly X Sᶜ (A v):=by
 apply add_left_cancel (a:= d • keepOnly X S v); conv_lhs=> lhs; rw [← show A _=_ from h.agrees v]
 rw [← h.reads]; rw [←map_add, ←mask_add, ←mask_add] -- tune `conv`
lemma rotates (h:Whole X S A c) (p:ℝ)(n:ℕ) : Whole X S (rotateT X A p n) (shortA p n c):= by obtain ⟨I,f,k⟩:= basis_harp A h.self; exact ⟨(show Harp I (rotateT X A p n) (shortA p n ∘ f) from fun i=> blink X A p n _ _ (k i)).self, fun v=>blink X A p n _ _ (h.agrees v)⟩ -- tune `..`
lemma stretched (h:Whole X S A 1)(p:ℝ)(n:ℕ): Whole X S (stretch X S A p n) 1:= by
 unfold stretch; refine ⟨?_,?_⟩
 · rw [ContinuousLinearMap.isSelfAdjoint_iff']; have f:= h.rotates p n |>.self; rw [map_add,map_smulₛₗ, show ContinuousLinearMap.adjoint _=_ from f, show ContinuousLinearMap.adjoint _=_ from mask_self (X:=X) (S:=S)]; rfl -- tune
 intro v; let H:= ((h.rotates p n).agrees v).plus ((mask.agrees v).scale (1-shortA p n 1)); simpa [stretch] using H
end Whole
-- abstract floor/ceiling
lemma disjoint_mask (x:RaySpace X): keepOnly X S (keepOnly X Sᶜ x)=0:= by ext i; by_cases h:i.1.1∈ S<;> simp [keepOnly,h]
lemma mask_disjoint (x y:RaySpace X): inner ℝ (keepOnly X S x) (keepOnly X Sᶜ y)=0:= by rw [ray_mask,disjoint_mask]; simp
lemma remains (x:RaySpace X): stretch X S A p n (keepOnly X Sᶜ x)=rotateT X A p n (keepOnly X Sᶜ x):=by unfold stretch; rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, show keeper X S _=_ from disjoint_mask X S x]; simp
lemma margins_soft {a b c:ℝ}(H : Whole X S F c)(t:c∈Set.Icc a b)(h : ∀ x:RaySpace X, let P:= keepOnly X Sᶜ x; inner ℝ P (F P) ∈ Set.Icc (a*‖P‖^2) (b*‖P‖^2)): Margins F a b:=by
 intro v; let u:=keepOnly X S v; let w:=keepOnly X Sᶜ v; have he:= h v; dsimp only at he; rw [show inner ℝ v (F v)=c*‖u‖^2+inner ℝ w (F w) from ?_, splitSoft X S v]; swap
 · conv_lhs=> rw [mask_add X S v, map_add, inner_add_left, inner_add_right, inner_add_right, show F _=_ from H.agrees v, real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,real_inner_comm (y:=keepOnly X Sᶜ v) (x:=keepOnly X S v)] -- tune both occurrences
   unfold u w; rw [H.complement v]; rw [mask_disjoint,mask_disjoint]; ring
 rw [mul_add,mul_add]; exact ⟨add_le_add (mul_le_mul_of_nonneg_right t.1 (sq_nonneg _)) he.1,add_le_add (mul_le_mul_of_nonneg_right t.2 (sq_nonneg _)) he.2⟩
def errorT :=1-F*A*F
lemma error_sym (h:IsSelfAdjoint F)(g:IsSelfAdjoint A): IsSelfAdjoint (errorT X A F):= by
 unfold errorT; rw [ContinuousLinearMap.isSelfAdjoint_iff', map_sub]; change _ - ContinuousLinearMap.adjoint ((F.comp A).comp F)=1-F*A*F
 rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,show ContinuousLinearMap.adjoint A=A from g,show ContinuousLinearMap.adjoint F=F from h]; change ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ _) - F*(A*F)=_; rw [ContinuousLinearMap.adjoint_id, ←mul_assoc]; rfl -- tune
lemma whole_error (h: Whole X S F 1)(g:Whole X S A 1): Whole X S (errorT X A F) 0:=⟨error_sym X A F h.self g.self,fun i=>by have h:=h.agrees i; simpa only [errorT,mul_one,sub_self] using ((Flare.one (v:=keepOnly X S i)).sub ((h.mul (g.agrees i)).mul h))⟩
structure Poly (A F:BEnd X)(L U e:ℝ):Prop where
 lid : Whole X S F 1
 floorP : 0<L
 bound : Margins F L U
 geo : 0≤e
 tile : ‖errorT X A F‖ ≤ e

lemma stretch_bound (h:Whole X S A 1)(t:Margins A r p)(u:1≤ p)(v:0< r)(d:r≤1) {e:ℝ} (g:p * (2*peak r)*brink p r n ≤ e) : Poly X S A (stretch X S A p n) (peak p) (peak r) e:=by
 let F:=rotateT X A p n; let G:=stretch X S A p n; obtain ⟨I,f,k⟩:=basis_harp A h.self; have H:Harp I F (shortA p n ∘ f):=fun i=>blink X A p n _ _ (k i); let T:=errorT X A F; have ht:=h.rotates p n; have hg:=h.stretched p n; have he(i):=peak_price p r (f i) n v ((k.margin.mp t) i)
 have hp:0<p:=zero_lt_one.trans_le u; have hP:0<peak p:=inv_pos.mpr (Real.sqrt_pos.mpr hp); have hn:0<peak r:=inv_pos.mpr (Real.sqrt_pos.mpr v); have hc:0≤e:= (show 0≤p * (2*peak r)*brink p r n by unfold brink; positivity).trans g; refine ⟨hg,hP, margins_soft X S G hg ?_ (fun i=> ?_),hc,Margins.cap ?_ hc (whole_error X S A G hg h).self⟩ -- tune order
 · unfold peak; exact ⟨inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt u),one_le_inv₀ (Real.sqrt_pos.mpr v) |>.mpr (by simpa using Real.sqrt_le_sqrt d)⟩ -- tune
 · dsimp only; unfold G; rw [remains]; exact (H.margin.mpr (fun i=>(he i).1)) _
 have hy(i): Flare T (I i) (1-(shortA p n (f i))^2*f i):=by rw [show 1-(shortA p n (f i))^2*f i=1-(shortA p n (f i)*f i)*shortA p n (f i) by ring]; exact Flare.one.sub (((H i).mul (k i)).mul (H i))
 have ho: Margins T (-e) e:= (show Harp I T _ from hy).margin.mpr (fun i=> ⟨(neg_nonpos.mpr hc).trans (he i).2.1,(he i).2.2.trans g⟩) -- tune simp args
 refine margins_soft X S (errorT X A G) (whole_error X S A G hg h) ⟨neg_nonpos.mpr hc,hc⟩ (fun x=>?_ ); dsimp only; rw [show errorT X A G (keepOnly X Sᶜ x)=T (keepOnly X Sᶜ x) from ?_]; exact ho _
 unfold errorT T; simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,ContinuousLinearMap.mul_apply]; rw [show G _=_ from remains X S A p n x]; change keepOnly X Sᶜ x-G (A (F _))=keepOnly X Sᶜ x-F (A (F _)); rw [show F (keepOnly X Sᶜ x)=_ from ht.complement x,h.complement]; rw [show G _=_ from remains X S A p n _] -- tune reduce
end YM.CF.BPress.Weave
