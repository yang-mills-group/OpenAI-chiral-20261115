import YM.SU5.FiniteGaugeData.Tower.RoomShape
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
/-!
# Uniform three-axis estimate at charged periods, with linear fourth-axis bill

Essential for train application. We will call ONLY with this charge at a fixed
slab's observing scale, no control of that stamp at later entries. Kemble's
factor linear in m (or n_torus in gauge-site units); sufficient for powers.
No extra shape indices: temporal support can be the entire cyclic torus.
-/
section fares
variable {K:Calibration}{m:Side}{L:Scree.Loom (K.c m)}{Y:Mark (K.c m) →ℂ}{D:ℝ}(p:Metered K m L Y D)
local notation "N"=> K.c m
private lemma scales(x b:ℕ)(pb:0< b)(h: b≤x): ∃ k:ℕ,2^k*b ≤ x ∧ x ≤2*2^k*b:=by
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
include p
lemma vista {d:ℕ}(a:Axis)(u:d+addgap K≤(K.c m).val){s:Support (More N)}{f:Mark (K.c m)}(hf:AtSupport false s f)(hs:∀i:Axis,i≠a→ rest K m s i d):
 ‖Y f‖ ≤ Real.exp (D * ((2*(d+addgap K):ℕ):ℝ)^3 * (m.val:ℝ))*cash L f:=by
 let b:=d+addgap K
 obtain ⟨k,h,t⟩:=scales (K.c m).val b (lt_of_lt_of_le addgap_pos (Nat.le_add_left (addgap K) d)) u
 let R:= univ.erase a
 obtain ⟨x,T,e,w⟩:=p.brush k h R (fun j v=>hs j (mem_erase.mp v).1) hf
 let J:=(2^k)^3; have hp:0<J:=by unfold J; positivity
 have h₁:R.card=3:=by rw [card_erase_of_mem (mem_univ _),card_univ,show Fintype.card Axis=4 from card_fin 4]
 have hw: Metered.Flare J f x Y L :=by rw [h₁] at w; exact w
 have hg:(m.val:ℝ)^4 ≤ J*((2*b:ℕ):ℝ)^3*m.val:=by
    exact_mod_cast (show (m.val:ℕ)^4 ≤ J*(2*b)^3*m.val from by
       unfold J; rw [←mul_pow, show m.val^4=m.val^3*m.val from rflX m.val]
       have hx:m.val≤2^k*(2*b):= (side_lower K).trans (t.trans_eq (by ring))
       gcongr)
 let c:= ((2*b:ℕ):ℝ)
 apply (pow_le_pow_iff_left₀ (norm_nonneg (Y f)) (mul_nonneg (Real.exp_pos _).le (cash_nonneg ..)) (n:=J) (by omega)).mp
 have hh:D * (m.val:ℝ)^4 ≤ J*(D*c^3*m.val):=by
    calc _≤ D*(J*c^3*m.val):=mul_le_mul_of_nonneg_left hg p.positive
         _= _:=by ring
 calc ‖Y f‖^J ≤ Real.exp (D * (m.val:ℝ)^4)*cash L x := hw.value.trans (p.tally x e.env)
      _ ≤ _:=by
         rw [mul_pow,←Real.exp_nat_mul]; exact mul_le_mul (Real.exp_le_exp.mpr hh) hw.cost (cash_nonneg ..) (Real.exp_pos _).le
where rflX (a:ℕ):a^4=a^3*a:= pow_succ ..

-- version of core CS on actual covered Family
local notation "H" p:max=> Y ((p:Family K) m)
local notation "R" i:max z:max f:max=>mirror K i z f
variable (j:Axis)(z:ℤ)
lemma bill {f:Family K}(h:TestFamily K true f)(q:ℝ)(w:pay f q): ‖H f‖ ≤ Real.exp (D*(m.val:ℝ)^4)*q:=by
 have he:cash L (f m) ≤ q:= (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=>norm_nonneg _)) (integrable_const q) (Filter.Eventually.of_forall (fun i=>w _ _))).trans_eq (by simp)
 exact (p.tally _ (h.paid.choose_spec.support m).env).trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)
lemma narrow {d:ℕ}(u:d+addgap K≤ (K.c m).val){S:Finset Cover}{x:Axis→ℤ}{f:Family K}
 (hf:InTest K true S false f)(t:Transom j S x d)(c:ℝ)(w:pay f c): ‖H f‖ ≤ Real.exp (D*((2*(d+addgap K):ℕ):ℝ)^3*(m.val:ℝ))*c:=by
 have ht (i:Axis)(v:i≠j): rest K m (Satin.region S (K.c m)) i d:=by
    refine ⟨x i,?_⟩; rintro x w; obtain ⟨x,p,rfl⟩:=mem_image.mp w; exact ⟨x i,(t i v x p).1,(t i v x p).2,rfl⟩
 have he:cash L (f m) ≤ c:= (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=>norm_nonneg _)) (integrable_const c) (Filter.Eventually.of_forall (fun i=>w _ _))).trans_eq (by simp)
 exact (vista p j u (hf.support _) ht).trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)

def Cand(j:Axis)(z:ℤ): Submodule ℂ (Family K) where
 carrier:={f|TestFamily K true f∧ AtSupport false (band (K.c m) j (gaugeShift K.B z) K.ℓ) (f m)}
 zero_mem':=⟨aux_test (S:=∅) InTest.zero,AtSupport.zeroM⟩ -- check
 add_mem':=fun ⟨x,y⟩ ⟨t,h⟩=>⟨x.add t,y.addM h⟩
 smul_mem':=fun c _ ⟨x,y⟩=> ⟨x.scale _,y.smulM c⟩
local notation "S"=> Cand (m:=m) (K:=K) j z
local notation "J"=>gaugeShift K.B z
omit p in
lemma crownU {f:Family K}(v:f∈Cand (m:=m) (K:=K) j z): TestFamily K true f ∧ AtSupport false (band (K.c m) j (gaugeShift K.B z) K.ℓ) (f m):=v
noncomputable def speak: S→ₗ⋆[ℂ] S →ₗ[ℂ] ℂ:=by
 let q(x y:S):= H ((R j J x.val)*y.val)
 have e(x y:S):Envelope (((R j J x.val)*y.val) m):=(((reflect_ok K j J ((crownU j z x.property).1)).mul (crownU j z y.property).1).paid.choose_spec.support _).env
 refine ⟨⟨fun x=> ⟨⟨fun y=>q x y,fun y r=>?_⟩,fun c y=>?_⟩,fun x y=>LinearMap.ext fun r=>?_⟩,fun c x=> LinearMap.ext fun y=>?_⟩
 · unfold q; rw [AddSubmonoid.coe_add,mul_add]; exact p.sum _ _ (e x y) (e x r)
 · change q _ _= _; unfold q; rw [Submodule.coe_smul,Algebra.mul_smul_comm]; exact p.mult ..
 · change q _ _= _; unfold q; rw [AddSubmonoid.coe_add,mirror_plus,add_mul]; exact p.sum _ _ (e x r) (e y r)
 change H ((R j J (c•x.val))* y.val)= _; rw [mirror_scale,Algebra.smul_mul_assoc]; exact p.mult ..
lemma summit (x y:S):‖speak p j z x y‖^2≤ ‖speak p j z x x‖*‖speak p j z y y‖:=by
 let Q(x y:S):=speak p j z x y
 have ht (x:S):0≤Q x x:=p.fund j z (x.val m) (crownU j z x.property).2
 have hv:_root_.YM.Analysis.NNKernel Q:=fun _ v=>halfSpaceKernel (speak p j z) ht v
 obtain ⟨q⟩:=_root_.YM.Kernel.host hv
 have he(x:S):‖Q x x‖= ‖q.plant x‖^2:=by rw [← q.measure,inner_self_eq_norm_sq_to_K,norm_pow]; change ‖((‖q.plant x‖:ℝ):ℂ)‖^2= _; simp
 change ‖Q x y‖^2 ≤ ‖Q x x‖*‖Q y y‖
 rw [he,he,← mul_pow,←q.measure]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm ..) 2
-- concrete cut statement using wrapped qualifications instead of half support syntax
lemma seam_cut {T T':Finset Cover}{f g:Family K}(h:InTest K true T false f)(t:InTest K true T' false g)
 (u:Satin.region (reflectedBox j J T) N⊆band N j J K.ℓ)
 (q:Satin.region T' N ⊆ band N j J K.ℓ): ‖H (f*g)‖^2 ≤ ‖H (f*(R j J f))‖*‖H ((R j J g)*g)‖:=by
 let U:=R j J f
 have he:= axial K j J h
 let a₁:S:=⟨U,(show _ from And.intro (aux_test he) ((he.support m).mono u))⟩
 let a₂:S:=⟨g,(show _ from And.intro (aux_test t) ((t.support m).mono q))⟩
 have hv:=summit p j z a₁ a₂; change ‖H ((R j J U)*g)‖^2 ≤ ‖H ((R j J U)*U)‖*‖H ((R j J g)*g)‖ at hv
 unfold U at hv; rwa [reversal K j J h] at hv
end fares
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.narrow
