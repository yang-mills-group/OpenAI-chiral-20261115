import SatinFixedContrastNovember4

/-!
# Height-uniform estimates for reaching an operator-valued thin limit

A constant-growth budget only (in *micro* Foot widths held fixed!),
used separately from the nonzero estimate. Adapted from the strategy
in `the construction notes`, not assuming any NL results.
Keep very same course/enrollment. Use the charged Geometry and inflation
on it.

Modify the narrow & banner bounds of the Epoch at every observing height
when spending there. Here preserve a POINTWISE MARK sup inside the
budget. Proof follows `YM/SU5/FiniteGaugeData/{Marked/Journey/Smokestack,Tower/Gallery}`;
do not change any readiness or actual purchases.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat Analysis

section fares
variable {K:Calibration}{m:Side}{L:Scree.Loom (K.c m)}{Y:Mark (K.c m) →ℂ}{D D' l:ℝ}(p:Metered K m L Y D')
local notation "N"=> K.c m

private lemma reflectsOp (i:Axis)(z:ℤ) (f:Mark N) (c:ℝ) (h:∀ x, ‖f x‖≤c) :
  ∀ x, ‖reflMark i z f x‖≤c := by
  intro x; rw [reflMark,Fock.theta,twist_norm,Scroll.norm_cc]; exact h _

structure SupThinFlare (t:ℕ)(x y:Mark (K.c m))(X:Mark (K.c m)→ℂ) :Prop where
  value : ‖X x‖^t ≤ ‖X y‖
  cost : ∀ C:ℝ, 0≤C→ (∀ v,‖x v‖≤C)→ ∀ v, ‖y v‖ ≤ C^t

private lemma thinChain {l n:ℕ} {f g y:Mark N}(h:SupThinFlare (K:=K) (m:=m) l f g Y)(s:SupThinFlare (K:=K) (m:=m) n g y Y): SupThinFlare (K:=K) (m:=m) (l*n) f y Y := by
  constructor
  · rw [pow_mul]; exact (pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) h.value n).trans s.value
  intro C u v x; rw [pow_mul]; exact s.cost (C^l) (pow_nonneg u _) (h.cost C u v) x

include p
lemma thinFunnel (i:Axis)(k:ℕ){d:ℕ}(h:2^k*(d+addgap K)≤ (N).val) {S:Support (More N)}(w:rest K m S i d)
    {x:Mark N} (c:AtSupport false S x):
    ∃ (y:Mark N) (T:Support (More N)), AtSupport false T y ∧ SupThinFlare (K:=K) (m:=m) (2^k) x y Y ∧
           ∀ j:Axis,j≠i → ∀ d', rest K m S j d' → rest K m T j d' := by
  induction k generalizing d S x with
  | zero=> exact ⟨x,S,c,⟨by simp,fun _ _ g _ => by simp; exact g _⟩,fun _ _ _ v=>v⟩
  | succ k ih=>
    have ht:d+addgap K ≤ (N).val:=h.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _))
    obtain ⟨z,u,v,e⟩:= twice i w ht; let s:=Heat.gaugeShift K.B z
    let M:=S.image ((plane i s).anon N) ∪ S
    have hp:AtSupport false (band N i s K.ℓ) x := by
      exact c.mono u
    let g:=reflMark i s x
    let y:=g*x
    have hz: AtSupport false M y:= ((c.refl i s).mono subset_union_left).mulM (c.mono subset_union_right)
    obtain ⟨Y₁,T,a,b,q⟩:= ih (d:=2*d+addgap K) (by rw [pow_succ] at h; exact h.trans' (le_of_eq (by ring))) v hz
    · exact ⟨Y₁,T,a,pow_succ' 2 k ▸ thinChain (show SupThinFlare (K:=K) (m:=m) 2 x y Y from ⟨p.twiceX i z hp,fun c u h v=> by
                   change ‖g v * x v‖≤_; rw [sq]; exact (norm_mul_le ..).trans (mul_le_mul (reflectsOp (K:=K) (m:=m) i s x c h v) (h v) (norm_nonneg _) u)⟩) b,fun j a d f=> q j a d (e j a d f)⟩


lemma thinBrush (k:ℕ){d:ℕ}(h:2^k*(d+addgap K)≤ (N).val) {S:Support (More N)}(R:Finset Axis)(w:∀ i∈R,rest K m S i d)
    {x:Mark N} (c:AtSupport false S x):
    ∃ (y:Mark N) (T:Support (More N)), AtSupport false T y ∧ SupThinFlare (K:=K) (m:=m) ((2^k)^R.card) x y Y := by
  induction R using Finset.induction_on generalizing S x with
  | empty=> exact ⟨x,S,c,⟨by simp,fun _ _ g _ => by simp; exact g _⟩⟩
  | @insert i R v ih=>
    obtain ⟨y,T,a,b,e⟩:=thinFunnel p i k h (w _ (mem_insert_self _ _)) c
    obtain ⟨Y,M,q,g⟩:= ih (S:=T) (fun j u=> e j (fun V=> v (V ▸ u)) d (w j (mem_insert_of_mem u))) a
    rw [card_insert_of_notMem v,pow_succ']; exact ⟨_,_,q,thinChain b g⟩

omit p in
private lemma thinScales(x b:ℕ)(pb:0< b)(h: b≤x): ∃ k:ℕ,2^k*b ≤ x ∧ x ≤2*2^k*b:=by
 have e:x ≤ 2^x*b := (Nat.lt_two_pow_self.le).trans (Nat.le_mul_of_pos_right _ pb)
 let P(k:ℕ):=x ≤2*2^k*b
 have t:∃ k,P k:= ⟨x,by unfold P; linarith⟩
 refine ⟨Nat.find t,?_,Nat.find_spec t⟩
 generalize hx:Nat.find t=y
 cases y with
 | zero=> exact (one_mul b).symm ▸ h
 | succ j=>
    have u:= Nat.find_min t (m:=j) (by omega)
    rw [pow_succ']; unfold P at u; exact (not_le.mp u).le

lemma vistaSup {d:ℕ}(a:Axis)(u:d+addgap K≤(K.c m).val){s:Support (More N)}{f:Mark (K.c m)}(hf:AtSupport false s f)(hs:∀i:Axis,i≠a→ rest K m s i d)
    (E:∀ g:Mark (K.c m), Envelope g→∀ c:ℝ,0≤c→(∀ v,‖g v‖≤c)→ ‖Y g‖≤ Real.exp (D*(m.val:ℝ)^4)*c)
    (s0:ℝ)(v:∀ z,‖f z‖≤ s0)(h0:0≤ s0)(g0:0≤D):
 ‖Y f‖ ≤ Real.exp (D * ((2*(d+addgap K):ℕ):ℝ)^3 * (m.val:ℝ))*s0:=by
 let b:=d+addgap K
 obtain ⟨k,h,t⟩:=thinScales (K.c m).val b (lt_of_lt_of_le addgap_pos (Nat.le_add_left (addgap K) d)) u
 let R:= univ.erase a
 obtain ⟨x,T,e,w⟩:=thinBrush p k h R (fun j v=>hs j (mem_erase.mp v).1) hf
 let J:=(2^k)^3; have hp:0<J:=by unfold J; positivity
 have h₁:R.card=3:=by rw [card_erase_of_mem (mem_univ _),card_univ,show Fintype.card Axis=4 from card_fin 4]
 have hw: SupThinFlare (K:=K) (m:=m) J f x Y :=by rw [h₁] at w; exact w
 have hg:(m.val:ℝ)^4 ≤ J*((2*b:ℕ):ℝ)^3*m.val:=by
    exact_mod_cast (show (m.val:ℕ)^4 ≤ J*(2*b)^3*m.val from by
       unfold J; rw [←mul_pow, show m.val^4=m.val^3*m.val from rflX m.val]
       have hx:m.val≤2^k*(2*b):= (side_lower K).trans (t.trans_eq (by ring))
       gcongr)
 let c:= ((2*b:ℕ):ℝ)
 apply (pow_le_pow_iff_left₀ (norm_nonneg (Y f)) (mul_nonneg (Real.exp_pos _).le h0) (n:=J) (by omega)).mp
 have hh:D * (m.val:ℝ)^4 ≤ J*(D*c^3*m.val):=by
    calc _≤ D*(J*c^3*m.val):=mul_le_mul_of_nonneg_left hg g0
         _= _:=by ring
 calc ‖Y f‖^J ≤ Real.exp (D * (m.val:ℝ)^4)*(s0^J) := hw.value.trans (E x e.env (s0^J) (pow_nonneg h0 _) (hw.cost _ h0 v))
      _ ≤ _:=by
         rw [mul_pow,←Real.exp_nat_mul]; exact mul_le_mul (Real.exp_le_exp.mpr hh) le_rfl (pow_nonneg h0 _) (Real.exp_pos _).le
where rflX (a:ℕ):a^4=a^3*a:= pow_succ ..

lemma narrowHeight (j:Axis) {d:ℕ}(u:d+addgap K≤ (K.c m).val){S:Finset Cover}{x:Axis→ℤ}{f:Family K}
 (hf:InTest K true S false f)(t:Transom j S x d)(c:ℝ)(w:pay f c)
 (H:∀ g:Mark (K.c m), Envelope g→∀ c:ℝ,0≤c→(∀ v,‖g v‖≤c)→ ‖Y g‖≤ Real.exp (D*(m.val:ℝ)^4)*c)(h0:0≤D): ‖Y (f m)‖ ≤ Real.exp (D*((2*(d+addgap K):ℕ):ℝ)^3*(m.val:ℝ))*c:=by
 have ht (i:Axis)(v:i≠j): rest K m (Satin.region S (K.c m)) i d:=by
    refine ⟨x i,?_⟩; rintro x w; obtain ⟨x,p,rfl⟩:=mem_image.mp w; exact ⟨x i,(t i v x p).1,(t i v x p).2,rfl⟩
 exact vistaSup p j u (hf.support _) ht H c (w m) (pay_nonneg w) h0

end fares
end YM.CF.Buffered.Afterglow.Tower.SlabMark

#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.narrowHeight
