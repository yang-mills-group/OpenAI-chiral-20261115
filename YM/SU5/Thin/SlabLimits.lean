/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import SatinFixedContrastNovember4
import YM.SU5.Thin.Uptake

/-! # Uniform thinOP stage paycheck (following `Tower/StationRide`; version with
uniform D, from our HeightBounds). This is OP norm, not a spectral or connected bound. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 390000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Set
section pace
variable {V : Type*} [AddCommMonoid V] [Module ℂ V] {H : Hilbert}
-- identical to the private lemma `driver` in StationRide
private lemma thinDriver (A B : V→ₗ[ℂ] V) (X : V →ₗ[ℂ] H) (D : ℝ) (h : 0<D)
    (hp : ∀ v w, inner ℂ (X (A v)) (X w)=inner ℂ (X v) (X (B w)))
    (v : V) (ht : ∃ C : ℝ, ∀ n:ℕ, ‖X (((B ∘ₗ A)^n) v)‖ ≤ C*D^(2*n)) :
    ‖X (A v)‖ ≤ D*‖X v‖ := by
  let T : V→ₗ[ℂ] V := B ∘ₗ A
  have hh (v w) : inner ℂ (X v) (X (T w))=inner ℂ (X (T v)) (X w) := by
    change inner ℂ (X _) (X (B _))=_
    rw [← hp,← inner_conj_symm (X (A v)),hp,inner_conj_symm];rfl
  have hw n (v w) : inner ℂ (X v) (X ((T^n) w))=inner ℂ (X ((T^n) v)) (X w) := by
    induction n generalizing v w with
    | zero => rfl
    | succ n ih =>
      conv_rhs => rw [pow_succ]
      conv_lhs => rw [pow_succ']
      rw [show (T*T^n) w=T ((T^n) w) from rfl, hh, ih];rfl
  obtain ⟨C,hC⟩ := ht
  let d n := ‖X ((T^n) v)‖/D^(2*n)
  have Ht n : 0 ≤ d n := by unfold d; positivity
  have he : BddAbove (range d) := by
    refine ⟨C, fun c he => ?_⟩; obtain ⟨i,rfl⟩ := he
    exact (div_le_iff₀ (pow_pos h _)).2 (hC _)
  let s := ⨆ i, d i
  have hr n : d n≤ s := le_ciSup he _
  have hz n : d n ^ 2 ≤ ‖X v‖ * s := by
    have hi : ‖inner ℂ (X v) (X ((T^(n+n)) v))‖= ‖X ((T^n) v)‖^2 := by
      rw [pow_add,Module.End.mul_apply, hw,inner_self_eq_norm_sq_to_K]; simp
    calc _ = ‖inner ℂ (X v) (X ((T^(n+n)) v))‖/D^(2*(n+n)) := by unfold d; rw [hi,div_pow, Nat.mul_add, pow_add, pow_two (D^_)]
         _ ≤ ‖X v‖*d (n+n) := by
             apply (div_le_div_of_nonneg_right (norm_inner_le_norm _ _) (pow_nonneg h.le _)).trans (le_of_eq ?_); unfold d; ring
         _ ≤ _ := by gcongr; exact hr _
  have hs := (Ht 0).trans (hr 0)
  have hu : s ≤ ‖X v‖ := by
    have hx : s ≤ √(‖X v‖*s) := ciSup_le fun i => (Real.le_sqrt (Ht i) (by positivity)).mpr (hz i)
    have he := Real.sq_sqrt (show 0 ≤ ‖X v‖*s by positivity)
    nlinarith [norm_nonneg (X v)]
  have hy : ‖X (A v)‖^2=‖inner ℂ (X v) (X ((T^1) v))‖ := by rw [pow_one,show X (T v)=X (B (A v)) from rfl,← hp];simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  rw [hy]
  have hr : ‖X ((T^1) v)‖ ≤ ‖X v‖*D^(2*1) := (div_le_iff₀ (pow_pos h _)).1 ((hr 1).trans hu)
  apply (norm_inner_le_norm _ _).trans
  exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans_eq (by ring)
end pace
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (j:Axis)(strict:Bool)
variable (C:Arena Y H Q.circuit j 0 strict) -- tune
variable (w:ℕ)(f:Entry Y H s j strict w)
variable (Qt : Clipped Y H (i∘a) (k∘b))(hw:0 < w)
local notation "A"=> Ark.Ht Y H Q.circuit j 0 strict C
local notation "Γ" i:max=> Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s Q.circuit j 0 strict C

local notation "T" i:max h:max=>furnished Y H s Q j strict w f i h
local notation "uM" t:max=> (L₀^t*w)
local notation "M" i:max x:max=>slabT Y H i j strict (Λ.R.L.val^(i-s)*w) x
local notation "KTT" i:max t:max=>tick Y H t j 0 strict i
variable (γ:ℝ) (g0:0≤ γ)(bg:PaidHeight (i:=i) (k:=k) (a:=a) (b:=b) Y H s γ)
variable (S:Finset Cover)(t0:InTest (tent Y H) true S false f.val.val)(hB:Between (tent Y H) j 0 (ruler Λ.block*w) S)
variable (M0:ℝ)(hd0:pay f.val.val M0)(d0:ℕ)(X0:Axis→ℤ)(ht0:Transom j S X0 d0)
local notation "Bω"=> thinStand Λ K w d0 M0 γ
include V C Qt hw Q t0 hB hd0 ht0 g0 bg
lemma drivesOnPage: ∀ t:ℕ,∀ p:s ≤ t,∀x:Γ t,
 let y:Γ t := (KTT (2*(L₀^(t-s)*(3*w))) t) x
 ‖(κ t) ((M t (T t p)) y)‖ ≤ (Real.sqrt Bω)*‖(κ t) y‖:=by
 let B:= Bω; have b:0<B:= standPos ..; have hB0:=uptake Y H V s Q j w f.val.val S t0 hB Qt hw γ g0 bg M0 hd0 d0 X0 ht0
 let q:=Real.sqrt B
 have HQ:0<q:=Real.sqrt_pos.mpr b
 intro t p x y
 let r:= t-s; let e:=L₀^r; let d:=e*w
 let z:=T t p; let q':=inverse Y H t j strict d z
 let Y₁:= M t (T t p)
 let Z₁:= M t q'
 let F:=arrows Y H V Q.circuit j 0 strict C t
 refine thinDriver (H:=A) Y₁ Z₁ F q HQ (fun i b=>symmetry Y H V _ Q.circuit j strict C z i b) y ?_
 obtain ⟨A₀,m₀,g⟩:= (show ∃ KTT':Finset Cover,InTest K true KTT' false x.val∧ Tower.region j (meshface (Λ:=Λ) 0 t) (K).ℓ KTT' from ((purpose_ok ..).mp x.property).1)
 let v:= (3*d:ℕ); let W:= plow K j (v:ℕ) A₀
 have hv': y.val=relocate K j (v:ℤ) x.val:=by
    change chime K j (Heat.gaugeShift Λ.block _) _=chime _ _ (gaugeT K _) _
    unfold v d e r gaugeT; push_cast; rw [show (K).B = Λ.block from rfl]; congr 2; ring
 have hv:InTest K true W false y.val:= hv'.symm ▸ (flow_port K j _ m₀)
 let i:= ruler Λ.block*d
 have Hl:∀I∈ W, 2*i+(K).ℓ ≤ I j:=by
    intro u v'; obtain ⟨m',t',rfl⟩:= plow_stays K j (v:ℕ) A₀ v'; specialize g m' t'; rw [moves,if_pos rfl]; rw [area0] at g
    unfold v i; change _ ≤ _+ruler Λ.block*(↑(3*d:ℕ):ℤ)
    have h':0 ≤ ruler Λ.block:=(ruler_gene _).le; push_cast; nlinarith
 obtain ⟨Δ,k⟩:=Tower.sizes W; obtain ⟨i',ht⟩:= k j
 let c:ℤ:= |i'|+Δ+(K).ℓ; have hd:0≤c:=by unfold c; positivity
 have he:Between K j (2*i) c W:=by intro z v; unfold c; have h:=ht z v; exact ⟨Hl z v,by linarith [le_abs_self i']⟩
 obtain ⟨a,qx⟩:=Journey.valuation Y H hv
 let a':=a+1; have hx:0<a':= by unfold a'; exact add_pos_of_nonneg_of_pos (pay_nonneg (F:=y.val) qx) one_pos
 have ht:pay y.val a':=fun i x=> le_trans (qx ..) (by unfold a'; linarith)
 let J:=wages K (duetCharge Y (s+r)) Δ c a'; have hJ:0≤J:=by unfold J wages closefare; positivity
 refine ⟨Real.sqrt J,fun n=>?_⟩
 apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
 rw [mul_pow, Real.sq_sqrt hJ, ← pow_mul q,show 2*n*2=2*(2*n) from by ring, pow_mul q 2, show q^2=B from Real.sq_sqrt b.le]
 -- packaged excursion
 change ‖(κ t) (((slabT Y H t j strict _ _ ∘ₗ slabT Y H t j strict _ _)^n) y)‖^2≤ _
 rw [excursion Y H V t Q j strict C d z y n]
 have hp:=hB0 r Δ W c hd y.val hv (by simpa only [i,d,e,Nat.cast_mul,Nat.cast_pow] using he) k a' hx ht (2*n)
 let F':= chambers j ((e*w:ℕ):ℤ) 0 (stream Y H D s r f.val.val) y.val (2*n)
 change ‖E t F'‖ ≤ _
 unfold F'; rw [show ((e*w:ℕ):ℤ) = (L₀:ℤ)^r*w from by unfold e; push_cast; rfl]; have hh:s+r=t:=Nat.add_sub_of_le p; generalize stream Y H D s r f.val.val=a at hp ⊢; rw [hh] at hp; unfold J; rw [hh]; exact hp

lemma slabBound : ‖boxOp Y H V s Q Qt j strict C w f hw‖≤Real.sqrt Bω := by
  let F:= boxOp Y H V s Q Qt j strict C w f hw; let L:= Real.sqrt Bω
  apply F.opNorm_le_bound (Real.sqrt_nonneg _)
  let S':Set A:={y : A | ‖F y‖ ≤ L*‖y‖}
  intro x
  apply closure_minimal (t:=S') ?_ (show IsClosed S' from isClosed_le F.continuous.norm (continuous_const.mul continuous_norm)) (concurs Y H V s Q j strict C w x)
  intro z vz; obtain ⟨r,i'⟩:= mem_iUnion.mp vz; obtain ⟨v,u'⟩:=mem_iUnion.mp i'; obtain ⟨a,rfl⟩:=u'
  let y:Γ r:=(KTT (2*(L₀^(r-s)*(3*w))) r) a
  change ‖boxOp Y H V s Q Qt j strict C w f hw ((κ r) y)‖≤ L*‖(κ r) y‖
  rw [snatch Y H V s Q Qt j strict C w f hw v]
  exact drivesOnPage Y H V s Q j strict C w f Qt hw γ g0 bg S t0 hB M0 hd0 d0 X0 ht0 r v a
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.slabBound
