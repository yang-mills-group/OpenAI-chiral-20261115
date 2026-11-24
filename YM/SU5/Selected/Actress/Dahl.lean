import YM.SU5.Selected.Actress.Moves
/-!
# Actor component extremality on ALL invariant states of the stated real-time operator algebra (Satin
 application separately). Includes Riesz construction and CS. Don't conflate with von Neumann purity,
 support-ergodicity of register measures, or Mink invariance for Lorentz beyond our qualifying Candor.
-/
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.Spectral.Alps
open Function Filter Real Set Complex Analysis Boundary Probe OS.Semigroup
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators ComplexOrder
variable {H:Hilbert}(A:StarSubalgebra ℂ H.Op) (Ω:H)
-- Circumstances. Every permitted direction yields a list of travels A∈A already proven. Not require action defined at any OTHER motion, nor ordering over all distributions. $∀∂` representation implemented.
variable {d:Type*}(T:d→unitary H.Op)(X: ↑A →ₗ[ℂ] ℂ) (v: ∀ i:d, (T i).val Ω=Ω) (q : ∀ i, Set.MapsTo (Unitary.conjStarAlgAut ℂ H.Op (T i)) (↑A) (↑A))
def afloat (B:StarSubalgebra ℂ H.Op)(F: B→ₗ[ℂ] ℂ) := F 1=1 ∧ (∀ x,F (star x)=star (F x)) ∧ ∀ x:B, 0 ≤ F (star x*x)
noncomputable def sail (i:d) (b: ↑A) : ↑A := ⟨Unitary.conjStarAlgAut ℂ H.Op (T i) b.val,q i b.property⟩
def sameShore:= afloat A X ∧ ∀ x i, X (sail A T q i x)=X x  -- q notation type? 
variable (p:‖Ω‖=1)
local notation "B" => ↑A
-- Canonical linear expectation. Continuous ops later. Gram `Q.Quasi`.
noncomputable def ray: ↑A→ₗ[ℂ] H where
  toFun x := x.val Ω
  map_add' x y:=rfl
  map_smul' c x:=rfl
noncomputable def opState: ↑A→ₗ[ℂ] ℂ := (innerSL ℂ Ω).toLinearMap.comp (ray A Ω)
local notation "μ"=> opState A Ω
local notation "κ"=> ray A Ω
include q v
lemma prep_in (i:d)(a:B): κ (sail A T q i a)=(T i).val (κ a) := by -- mul type wrong change
 let t:= T i; let W:= t.val; have he : t.val Ω=Ω:=v i; change (Unitary.conjStarAlgAut ℂ _ t a.val) Ω= W (κ a); rw [Unitary.conjStarAlgAut_apply];
 have hx: (star t.val) Ω=Ω:= (congrArg (star t.val : H.Op)  he.symm).trans (DFunLike.congr_fun t.property.1 Ω)
 change t.val (a.val ((star t.val) Ω))=_; rw [hx]; rfl -- maybe
omit v q
lemma structures(B':B): μ (star B'*B')=((‖κ B'‖^2:ℝ):ℂ):=by
 let u:=B'.val; change inner ℂ Ω (u.adjoint (u Ω))=_; rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]; change (↑‖u Ω‖:ℂ) ^2=_; norm_cast
lemma fromRay (b:B): μ (star b)=star (μ b):= by change inner ℂ Ω (b.val.adjoint Ω)= _; rw [ContinuousLinearMap.adjoint_inner_right]; exact (inner_conj_symm ..).symm
lemma op_pos (a:B) : 0 ≤ μ (star a*a):= by rw [structures]; exact_mod_cast sq_nonneg (‖κ a‖)
include v q p
-- state invariant (even if SOT). qualify both real t & spatial t.
lemma opMotion : sameShore A T μ q :=by
 have he : μ 1=1:= by change inner ℂ Ω Ω=1; rw [inner_self_eq_norm_sq_to_K,p]; simp
 refine ⟨⟨he,fromRay A Ω,op_pos A Ω⟩,fun x i=>?_⟩; let t:= T i; let W := t.val; have ht: ∀ u:H, ‖W u‖=‖u‖:= (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr t.property.1; change inner ℂ Ω (κ (sail ..))= _; rw [prep_in A Ω T v q]; have hf:= (LinearMap.norm_map_iff_inner_map_map W.toLinearMap).mp ht Ω (κ x); change inner ℂ (W Ω) _ = inner ℂ Ω _ at hf; rw [show W Ω=Ω from v i] at hf; exact hf
omit p v q
lemma cs (p:afloat A X)(b:B) : ((‖X b‖^2:ℝ):ℂ) ≤ X (star b*b) :=by
 let u:= (X b) • (1:B); have h:=p.2.2 (b-u); let z:=X b; have he: z*star z=(( ‖X b‖^2:ℝ):ℂ):=by
    unfold z; rw [Complex.sq_norm]; exact Complex.mul_conj _
 have hx : X u=X b:=by unfold u; rw [map_smul, p.1]; simp
 rw [star_sub,sub_mul,mul_sub,mul_sub,map_sub,map_sub,map_sub] at h
 have hp(y:B) : X (star u * y)=star (X b)*X y:=by unfold u; rw [star_smul,star_one,Algebra.smul_mul_assoc,one_mul,map_smul]; rfl
 have ht: X (star b * u)= z*star z:=by unfold u z; rw [Algebra.mul_smul_comm, mul_one,map_smul,p.2.1]; rfl
 rw [hp,hp,hx,ht,sub_self,sub_zero,he] at h; exact sub_nonneg.mp h
include v q
local notation "sF" X:max=> sameShore A T X q
variable (L:DenseRange (ray A Ω))
variable (t':∀ x:H,(∀ i:d,(T i).val x=x)→∃ c:ℂ,c • Ω=x)
omit v q in
private lemma mass {x u z:ℝ}{U W:ℂ}(p:0≤ x)(v:0<u)(g:0≤z)(f:0≤W) {k:ℝ}(t: 0≤k)(y: ((k^2:ℝ):ℂ)≤ U)(h: ((x^2:ℝ):ℂ)= (u:ℂ)*U + (z:ℂ)*W) : k ≤ (Real.sqrt u)⁻¹*x:=by
 have hx:x^2 = u*U.re+z*W.re:= (by have h':= congrArg Complex.re h; simpa only [Complex.add_re,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero] using h');
 have he:k^2≤U.re:= (Complex.le_def.mp y).1; have hp:Real.sqrt u > 0:= by positivity
 rw [←div_eq_inv_mul, le_div_iff₀ hp]; apply (sq_le_sq₀ (by positivity) p).1; rw [mul_pow,Real.sq_sqrt v.le]; linarith only [hx,mul_le_mul_of_nonneg_left he v.le, mul_nonneg g (Complex.le_def.mp f).1 ]
include L t' p
lemma appoint {Y:B→ₗ[ℂ] ℂ}(h:sF X)(u:sF Y)(a b:ℝ)(hp:0<a)(g:0≤b)(t: μ=(a:ℂ) • X+(b:ℂ) • Y) : X=μ:=by
 let c:= (Real.sqrt a)⁻¹; have he(z:B): ‖X z‖≤ c*‖κ z‖:= mass (norm_nonneg _) hp g (u.1.2.2 z) (norm_nonneg _) (cs A X h.1 z) ((structures A Ω z).symm.trans (LinearMap.congr_fun t (star z*z))) -- price no false CS bypass.
 let P:= X.extendOfNorm (κ); let Q:= P.adjoint (1:ℂ); have hL(z:B):P (κ z)=X z:= LinearMap.extendOfNorm_eq L ⟨c,he⟩ _; have ht(x:H): inner ℂ Q x=P x:= (P.adjoint_inner_left x 1).trans (by simp); have he'(i):P ((T i).val Q)=P Q:= by
    let V:=(T i).val; suffices h:P∘ V=P from congrFun h Q; exact L.equalizer (P.continuous.comp V.continuous) P.continuous (funext fun f=> (show _ from ((congrArg P (prep_in A Ω T v q i f).symm).trans ((hL _).trans ((h.2 _ i).trans (hL f).symm))))) -- ext hL etc
 have hY(i):‖(T i).val Q‖ = ‖Q‖:= ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr (T i).property.1 Q)
 obtain ⟨d,e⟩:= t' Q (fun i=> eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ) (hY i).le (by rw [inner_re_symm,ht,he', ←ht,inner_self_eq_norm_sq]))
 have hx : inner ℂ Q Ω = 1:=(ht Ω).trans ((hL (1:B)).trans h.1.1); rw [←e,inner_smul_left, inner_self_eq_norm_sq_to_K,p] at hx; have hw:d=1:= star_injective (show star d=star (1:ℂ) by simpa using hx); rw [hw,one_smul] at e; ext1 z; exact (hL z).symm.trans ((ht _).symm.trans (congrArg (fun x : H=> inner ℂ x (κ z)) e.symm))
lemma principal : sameShore A T μ q ∧ ∀ (X Y:B→ₗ[ℂ] ℂ)(k:ℝ),0 < k→ k < 1 → sF X → sF Y → μ= (k:ℂ) • X+((1-k:ℝ):ℂ) • Y→ X=μ∧Y=μ := by refine ⟨opMotion A Ω T v q p, fun X Y k u t h l e=> ⟨appoint A Ω T X v q p L t' h l k (1-k) u (sub_nonneg.mpr t.le) e, ?_⟩⟩; exact appoint A Ω T Y v q p L t' l h (1-k) k (sub_pos.mpr t) u.le (e.trans (add_comm ..))
end YM.Spectral.Alps
open YM.Spectral.Alps
#print axioms principal
#print axioms sameShore
