import YM.SU5.FiniteGaugeData.Tower.Ford
/-!
# Buffered slabs at true resolution

Alignment and spread, raw algebra. Plane zero. Width h>0 is an integer
number of the **double times** later used on resolution Hilbert (16B gauge).
Pay endpoints of f interior stencil (within [ℓ,h*b-ℓ]). This file no
assertion yet that insertion is a bounded operator, or even on Hilbert. Strict
may be either; all are even physical marks, a nilpotent-matter algebra. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
section direct
variable (K:Calibration)(j:Axis)
noncomputable def ruler(B:Side):ℤ:= 16*B.val
lemma ruler_gene(B: Side):0<ruler B:=by unfold ruler; positivity
local notation "b₀"=>ruler K.B
def Between (K:Calibration)(j:Axis)(x y:ℤ)(f:Finset Cover) := ∀z∈f,x+K.ℓ≤z j∧ z j+K.ℓ ≤ y
/-- controls only indicated transverse directions -/
def Transom(j:Axis)(f:Finset Cover)(X:Axis→ℤ)(d:ℕ):Prop:=∀i≠j,∀z∈f,X i ≤ z i ∧ z i ≤ X i+d
lemma moves(j i:Axis)(v:Cover)(x:ℤ): (v+x • step j:Cover) i= if i=j then v i+x else v i:=by by_cases p:i=j <;> simp_all
noncomputable def gaugeT(v:ℤ):ℤ:= Heat.gaugeShift K.B (2*v) -- half displacement
local notation "r" v:max=> gaugeT K v
lemma gaugeT_add(v x:ℤ):r (v+x)= r v+r x:=by unfold gaugeT Heat.gaugeShift; ring
lemma gaugeT_zero: r 0=0:=by unfold gaugeT Heat.gaugeShift; ring
lemma ruler_offset(v:ℤ): 2*(r v)= b₀*v:=by unfold ruler gaugeT Heat.gaugeShift; ring

def relocate (v:ℤ)(F:Family K):Family K := chime K j (r v) F
local notation "U" i:max=>relocate K j i
local notation "R" y:max=>mirror K j y
variable {F G:Family K}{p:Finset Cover}
lemma relocate_sums(v w:ℤ)(x:TestFamily K true F):(U v) ((U w) F)=(U (v+w)) F:=by unfold relocate; rw [Tower.bumps K j _ _ x.paid.choose_spec, gaugeT_add]
lemma relocate_zero (x:TestFamily K true F): (U 0) F = F:=by unfold relocate; rw [gaugeT_zero,Tower.wake K j x.paid.choose_spec]
lemma relocate_mul (v:ℤ): (U v) (F*G)=(U v) F*(U v) G:=chime_product K j ..
lemma relocate_unit (v:ℤ):(U v) 1=1:= chime_unit ..
lemma mirror_relocate (v y:ℤ)(x:TestFamily K true F): (R y) ((U v) F)=(U (-v)) ((R y) F):=by unfold relocate; rw [chime_diag K j _ y x.paid.choose_spec, show -(r (-v))=(r v) by unfold gaugeT Heat.gaugeShift; ring]
lemma mirror_at {v y z:ℤ}(h:y-z=r v)(x:TestFamily K true F): (R y) ((R z) F)=(U v) F:=moted K j y z (r v) x.paid.choose_spec h
lemma mirror_invert (y:ℤ)(x:TestFamily K true F):(R y) ((R y) F)=F:=reversal K j y x.paid.choose_spec
lemma reflect_ok(y:ℤ)(x:TestFamily K true F):TestFamily K true ((R y) F):=aux_test (axial K j y x.paid.choose_spec)
lemma move_ok(v:ℤ)(x:TestFamily K true F):TestFamily K true ((U v) F):=aux_test (flow_port K j _ x.paid.choose_spec)
lemma mirror_cancel (u v:ℤ)(f:TestFamily K true F): (R (r u)) F=(U (u-v)) ((R (r v)) F):=by
 rw [← mirror_at K j (show (r u)-(r v)=(r (u-v)) by unfold gaugeT Heat.gaugeShift; ring) (reflect_ok K j (r v) f),mirror_invert K j _ f]
lemma odd_cancel(u v x:ℤ)(f:TestFamily K true F):(R (r u)) ((U x) F)=(U (u-v-x)) ((R (r v)) F):=by
 rw [mirror_relocate K j x _ f,mirror_cancel K j u v f,relocate_sums K j _ _ (reflect_ok K j _ f),show -x+(u-v)=u-v-x by abel]

def plow (v:ℤ)(S:Finset Cover):=Tower.address j (r v) S
lemma plow_stays (v:ℤ)(S:Finset Cover){u:Cover}(h:u∈plow K j v S):∃w∈S, u=w+(b₀*v)•step j:=by obtain ⟨w,p,rfl⟩:= mem_image.mp h; exact ⟨w,p,by rw [ruler_offset]⟩
omit K in
lemma reflect_stays (v:ℤ)(S:Finset Cover){u:Cover}(h:u∈reflectedBox j v S):∃w∈S,∀i,u i=if i=j then -w i+2*v else w i:=by obtain ⟨w,p,rfl⟩:= mem_image.mp h; refine ⟨w,p,fun i=>?_⟩; by_cases p:i=j <;> simp_all [fling_move,eq_comm (a:=i) (b:=j)]
lemma Between.relocate{x y}{S}(p:Between K j x y S)(v:ℤ):Between K j (b₀*v+x) (b₀*v+y) (plow K j v S):=by intro u t; obtain ⟨w,t',rfl⟩:=plow_stays K j v S t; rw [moves,if_pos rfl]; obtain ⟨h,p⟩:=p w t'; constructor <;> linarith
lemma Between.mirror{x y}{S}(p:Between K j x y S)(v:ℤ): Between K j (2*v-y) (2*v-x) (reflectedBox j v S):=by intro u t; obtain ⟨w,t',e⟩:=reflect_stays j v S t; rw [e,if_pos rfl]; obtain ⟨h,p⟩:=p w t'; constructor <;> linarith
lemma Transom.moved{S X d}(p:Transom j S X d)(v:ℤ):Transom j (plow K j v S) X d:=by intro i u w h; obtain ⟨w,h₀,rfl⟩:=plow_stays K j v S h; rw [moves,if_neg u]; exact p _ u _ h₀ -- shadow
lemma Transom.mirro{S X d}(p:Transom j S X d)(v:ℤ):Transom j (reflectedBox j v S) X d:=by intro i u w h; obtain ⟨w,g,e⟩:=reflect_stays j v S h; rw [e,if_neg u]; exact p _ u _ g
lemma even_tests (h:TestFamily K true F)(t:TestFamily K true G): F*G=G*F:=by
 obtain ⟨S,u⟩:=h.paid; obtain ⟨T,w⟩:=t.paid; funext m x
 have v:=((u.support m).mono (subset_univ _)).allV x
 have f:=((w.support m).mono (subset_univ _)).allV x
 simpa [Sector.grainB] using (v.sign_com f)
-- an oriented half-train (integer width w at scale, no cutoff parameter here)
private def toggled:ℕ→Bool
| 0=> true
| n+1=>!(toggled n)
def toward (v:ℤ)(f:Family K): ℕ→Family K
| 0=>f
| n+1=>mirror K j (gaugeT K v) (toward v f n)
-- prefix number n+1 tile at origin uses toward f n, so the *outermost* tile always f
def lace (v:ℤ)(f x:Family K): ℕ→Family K
| 0=> x
| n+1=> toward K j v f n * (U v) (lace v f x n)
local notation "I"=>toward K j
local notation "J"=>lace K j
lemma toward_step(v:ℤ)(f:Family K)(n:ℕ):I v f (n+1)=(R (r v)) (I v f n):=rfl
lemma lacing (v:ℤ)(f x:Family K)(n:ℕ):J v f x (n+1)=I v f n*(U v) (J v f x n):=rfl
lemma pin_zero (v:ℤ)(f x:Family K):J v f x 0=x:=rfl

lemma toward_paid(v:ℤ){f:Family K}(u:TestFamily K true f)(n:ℕ): TestFamily K true (I v f n):=by induction n with
| zero=>exact u
| succ n ih=>exact reflect_ok K j _ ih
lemma lace_paid(v:ℤ){f x:Family K}(u:TestFamily K true f)(p:TestFamily K true x)(n:ℕ): TestFamily K true (J v f x n):=by induction n with
| zero=>exact p
| succ n ih=> exact (toward_paid K j v u n).mul (move_ok K j _ ih)
lemma toggle_twice(v:ℤ)(p:TestFamily K true F)(n:ℕ): I v F (n+2)=I v F n:= mirror_invert K j _ (toward_paid K j v p n)
lemma unlace(v:ℤ){f x:Family K}(t:TestFamily K true f)(p:TestFamily K true x)(n:ℕ): J v f x n=J v f 1 n*(U (v*n)) x:=by induction n with
| zero=>rw [pin_zero,pin_zero,Nat.cast_zero,mul_zero,relocate_zero K j p,one_mul]
| succ n ih=>
   rw [lacing K j v f x n,lacing K j v f 1 n,ih,relocate_mul K j,relocate_sums K j _ _ p,mul_assoc,Nat.cast_add_one,show v*(↑n+1)=v+v*(↑n) by ring]
-- cost power (no θ expansion constants).
lemma toward_cost (v:ℤ)(q:ℝ){f:Family K}(h:pay f q)(i:ℕ):pay (I v f i) q:=by induction i with
| zero=> exact h
| succ i ih=> exact pay_flips K ih j _
lemma lace_cost(v:ℤ)(q Q:ℝ){f x:Family K}(h:pay f q)(p:pay x Q)(n:ℕ):pay (J v f x n) (q^n*Q):=by induction n with
| zero=> rw [pow_zero,one_mul,pin_zero]; exact p
| succ n ih=>rw [pow_succ',mul_assoc]; exact pay_mul (toward_cost K j v q h n) (chime_pay K j _ _ ih)

-- 2-step connection for T^n vector proof
lemma doubly(v:ℤ)(f:Family K)(p:TestFamily K true f)(n:ℕ):I v f (n+n)=f:=by induction n with
| zero=>rfl
| succ n ih=>rw [show (n+1+(n+1))=(n+n+2) from by omega, toggle_twice K j v p, ih]
lemma overlay(v:ℤ)(f x:Family K)(p:TestFamily K true f)(n:ℕ):
 J v f x (2*(n+1))= (R (r v)) f*(U v) (f*((U v) (J v f x (2*n)))):=by
 rw [show 2*(n+1)=(n+n+1+1) by omega,lacing,lacing,toward_step,doubly K j _ _ p, two_mul]

end direct
section election
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q:Resolution (E:=E) Y H D)
variable (j:Axis)(strict:Bool)
variable (C:Arena Y H Q j (0:ℤ) strict)
local notation "U" i:max=>relocate K j i
local notation "R" i:max=>mirror K j i
local notation "F" t:max=> Tower.Field Y H t j (0:ℤ) strict
local notation "p" => (K).ℓ
local notation "c"=> ruler Λ.block
noncomputable def Entry (w:ℕ) := {x:Tower.Field Y H s j (0:ℤ) strict // ∃ S:Finset Cover, InTest (tent Y H) true S false x.val ∧ Between (tent Y H) j 0 (ruler Λ.block*w) S}
local notation "A" s:max w:max=>Entry Y H s j strict w
lemma as_field{i}{z:F i}{w:ℕ}{S:Finset Cover}(h:InTest K true S false z.val)(t:Between K j 0 (c*w) S):∃ x:A i w, x.val=z:= ⟨(⟨z,S,h,t⟩:A i w),rfl⟩
lemma test_entry {w:ℕ}(x:A s w):TestFamily K true (show F s from x.val).val:=field_test_entry
where field_test_entry := aux_test x.property.choose_spec.1

lemma area0{i}:meshface (Λ:=Λ) (0:ℤ) i=0:=by unfold meshface Heat.gaugeShift; ring
noncomputable def inverse(w:ℕ)(x:Entry Y H s j strict w):Entry Y H s j strict w:=by
 let X:=(x.val:F s); let S:=x.property.choose; have ht:=x.property.choose_spec.1; have hx:=x.property.choose_spec.2
 let b:=gaugeT K w
 let f:=mirror K j b X.val; let T:=reflectedBox j b S
 have he : 2*b=c*w:=ruler_offset K _; have hf: InTest K true T false f:=axial K j b ht; have h:Between K j 0 (c*w) T:=by have h1:= hx.mirror K j b; rwa [he,sub_zero,sub_self] at h1
 have hv:Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ T:=by rw [area0]; exact fun i t=>(h i t).1
 exact ⟨(⟨f,(purpose_ok ..).2 ⟨(show _ from ⟨T,hf,hv⟩),fun z=>covariant_flips _ _ _ ht (((purpose_ok ..).mp X.property).2 z)⟩⟩ : F s),T,hf,h⟩
lemma inverse_twice{w}(x:A s w):inverse Y H s j strict w (inverse Y H s j strict w x)=x:= Subtype.ext (Subtype.ext (mirror_invert K j _ (test_entry Y H s j strict x)))
noncomputable def slabT (w:ℕ)(x:Entry Y H s j strict w): (Tower.Field Y H s j 0 strict) →ₗ[ℂ] (Tower.Field Y H s j 0 strict) where
 toFun y:=⟨x.val.val * (tick Y H s j 0 strict (2*w) y).val,Subalgebra.mul_mem (purpose ..) x.val.property (tick _ _ _ _ _ _ _ y).property⟩
 map_add' u v:=Subtype.ext (by change _*((tick _ _ _ _ _ _ _ (u+v):F s).val)=_; rw [map_add,AddSubmonoid.coe_add,mul_add]; rfl)
 map_smul' z u:=Subtype.ext (by change _*((tick _ _ _ _ _ _ _ (z • u):F s).val)=_; rw [map_smul,Submodule.coe_smul,Algebra.mul_smul_comm]; rfl)
local notation "κ" s:max=>actor Y H s Q j 0 strict C
lemma slab_eq (w:ℕ)(x:A s w)(z:F s): (slabT Y H s j strict w x z).val=(x.val:F s).val*(U (w:ℤ)) z.val:=by
 change _*chime K j (Heat.gaugeShift Λ.block ((2*w:ℕ):ℤ)) _= _*chime K j (Heat.gaugeShift Λ.block (2*(w:ℤ))) _; norm_cast
include V C
lemma symmetry {w}(x:A s w)(a b:F s):
 inner ℂ ((κ s) (slabT Y H s j strict w x a)) ((κ s) b)=inner ℂ ((κ s) a) ((κ s) (slabT Y H s j strict w (inverse Y H s j strict w x) b)):=by
 let hx:=test_entry Y H s j strict x; let hi:=test_entry Y H s j strict (inverse Y H s j strict w x)
 have hv(z:F s):TestFamily K true z.val:= (exam j _ K ((purpose_ok ..).1 z.property).1).1
 have he(g:Family K)(h:TestFamily K true g):E s ((U w) g)=E s g:=SWay Y H V s j (2*(w:ℤ)) h
 rw [stems Y H V,stems Y H V,area0,slab_eq,slab_eq]
 let f:=(x.val:F s).val
 let a':=a.val; let b':=b.val
 change E s ((R (0:ℤ)) (f*((U w) a')) * b')= E s ((R (0:ℤ)) a' * (mirror K j (gaugeT K w) f*(U w) b'))
 rw [←he _ ((reflect_ok K j _ (hx.mul (move_ok K j _ (hv a)))).mul (hv b)), mirror_times, relocate_mul,relocate_mul,mirror_relocate K j _ 0 (hv a),relocate_sums K j _ _ (reflect_ok K j 0 (hv a)),add_neg_cancel,relocate_zero K j (reflect_ok K j 0 (hv a))]
 have hw: mirror K j (gaugeT K w) f=(U w) ((R 0) f):=by rw [mirror_cancel K j (↑w:ℤ) 0 hx,sub_zero,gaugeT_zero]
 rw [hw, even_tests K (move_ok K j _ (reflect_ok K j _ hx)) (reflect_ok K j _ (hv a)), mul_assoc]
end election
end YM.CF.Buffered.Afterglow.Tower.SlabMark

#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.unlace
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.symmetry
