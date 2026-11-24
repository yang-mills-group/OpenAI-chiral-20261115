import YM.CF.Kea.Cool
import YM.CF.Volume.Carrier
import YM.CF.Graph.Pod
/-! # Controlled spin directions: Fourier retention all periods on this licensed sector
Build needed UNIFORM onsite invertibility for inserting spanning W. Heat/actual high observing
level Male arbitrary leads exactly this projector. Spin/case costs supported. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 14000
noncomputable section
namespace YM.CF.Signal.Sparkle
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace Kea
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
variable {N:Side}{a b u v:ℝ}{j:ℕ}
namespace Retain
section algebra
variable {A B:Op I}{x y:Ket I}(p:IsStarProjection A)(q:IsStarProjection B)
-- inner in FiniteGaugeData conventions. mapping left adjoint if want. real norms
include p
lemma loop_p(x:Ket I):inner ℂ x (acts A x)=(↑(‖acts A x‖^2):ℂ) := by
 have he:= p.isIdempotentElem.eq; nth_rw 1 [show acts A x=acts A (acts A x) by rw [←act_mul,he]]; rw [←act_inner,p.isSelfAdjoint,inner_self_eq_norm_sq_to_K]; push_cast; rfl
lemma cap [Nonempty I](x:Ket I): ‖acts A x‖≤‖x‖:= (Flare.opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) (p.norm_le _))
lemma bore (x:Ket I) : acts A (acts A x)=acts A x:=by rw [←act_mul,p.isIdempotentElem.eq]
omit p in
lemma lunar (x:Ket I):x=acts A x+acts (1-A) x:=by rw [act_sub,act_one]; abel
include q
lemma spark_p (w:B*A*B=(a:ℂ) • B)(u:acts B x=x): ‖acts A x‖^2=a*‖x‖^2:=by
 have h':inner ℂ x (acts A x)=inner ℂ x (acts (B*A*B) x):=by simp only [act_mul,u]; rw [←act_inner B,q.isSelfAdjoint,u]
 rw [loop_p p,w,act_smul,u,inner_smul_right,inner_self_eq_norm_sq_to_K] at h'; apply Complex.ofReal_injective; push_cast at h' ⊢; exact h' -- RCLike convert
end algebra
variable (M:Jill.Male){p:Bin}(hp:Bound Real.pi p)
local notation "q"=>tmap p
local notation "W"=> Fir.bar j M.val (tmap p)
local notation "P0"=> Aop
local notation "s·" M => disk j M p
local notation "B↓"=>1-Aop
lemma base(h: Bound Real.pi p): (tmap p)∈ realCube zone:= base_subset_realCube zone_pos (b_base h)
include hp
lemma bright0 : IsStarProjection (bar j M.val q):= by
 obtain ⟨t,r⟩:= firm_bar j M.val M.property (base hp); exact ⟨t,r⟩
lemma top_blend : Aop*W*Aop=(disk j M p:ℂ) • Aop:=by
 let S:=zen (mixL j M.val (tmap p)); have h:Aop*S*Aop=0:=by rw [zenA,mul_assoc,sub_mul,one_mul,AOne,sub_self,mul_zero]
 rw [(bar_side j M.val (base hp)).1,express j p M.val (base hp) M.property,Matrix.smul_mul,mul_add,mul_one,add_mul,h,AOne,add_zero]; rfl
lemma bot_blend : (1-Aop)*W*(1-Aop)=(↑(1-disk j M p):ℂ) • (1-Aop):=by
 let S:=zen (mixL j M.val (tmap p)); let f:=1-Aop; have he:IsStarProjection Aop:=⟨AOne,Aadj⟩; have hf:= he.one_sub.isIdempotentElem.eq; have h:f*S*f=0:=by change (1-Aop)*S*_=_; rw [zenAA,mul_assoc,Porth he,mul_zero]
 have hv:f*(1-W)*f=(disk j M p:ℂ) • f:=by change (1-Aop)*(1-_) * _ = _; rw [(bar_side j M.val (base hp)).2, express j p M.val (base hp) M.property,Matrix.smul_mul,mul_add,mul_one,add_mul,h,hf, add_zero]; rfl
 rw [mul_sub (1-Aop) 1 W,mul_one,sub_mul (1-Aop) ((1-Aop)* W) f, hf] at hv; rw [Complex.ofReal_sub,sub_smul,Complex.ofReal_one,one_smul]; unfold f at hv; rw [←hv]; abel
lemma bright (x:Ket SpinIdx) : ‖acts W (acts Aop x)‖^2=disk j M p*‖acts Aop x‖^2 ∧
    ‖acts W (acts (1-Aop) x)‖^2=(1-disk j M p)*‖acts (1-Aop) x‖^2 := by
 have h:IsStarProjection Aop:=⟨AOne,Aadj⟩; exact ⟨spark_p (bright0 M hp) h (top_blend M hp) (bore h x),spark_p (bright0 M hp) h.one_sub (bot_blend M hp) (bore h.one_sub x)⟩
omit hp M
private lemma ambL {x y:ℝ}(p:0≤x)(f:y^2≤x^2): y≤x:=by nlinarith [p]
/-- Parameters conditional are bought later. for ANY unit spin scale. U_ budget hight uses T norms. -/
lemma forecast (j:ℕ)(a b s:ℝ)(hz:0<s)(hs:s≤1)(h:s^2≤ a)(u:0≤b)(v:b<s/4)
    (i:Jill.Male)(p:Bin)(hp:Bound Real.pi p) (h': a ≤ disk j i p) (x:Ket SpinIdx) (vh:‖acts (1-Aop) x‖≤ b*‖x‖): s/2*‖x‖≤ ‖acts (bar j i.val (tmap p)) x‖:= by
 let G:= bar j i.val (tmap p); let z:=‖acts (1-Aop) x‖; let y:=‖acts Aop x‖; let A:=acts G; let t:= ‖x‖; have ht:0 ≤ t:=norm_nonneg _
 have VP:=bright (j:=j) i hp x; have W':s*y≤‖A (acts Aop x)‖:=by
    have he: ‖A (acts Aop x)‖^2=disk j i p*y^2:=VP.1; apply ambL (by positivity) -- extra variables
    rw [he,mul_pow]; exact mul_le_mul_of_nonneg_right (h.trans h') (sq_nonneg _)
 have hh:t≤ y+z:=by nth_rw 1 [show t= _ from congrArg (fun z=> ‖z‖) (lunar (A:=Aop) x)]; exact norm_add_le ..
 have hy:‖A (acts Aop x)‖ ≤ ‖A x‖ + z:=by
    have he2:‖A (acts Aop x)‖ ≤ ‖A x‖+‖A (acts (1-Aop) x)‖:= by nth_rw 1 [show A (acts Aop x)= A x-A (acts (1-Aop) x) by rw [eq_sub_iff_add_eq, ←map_add, ← lunar]]; exact norm_sub_le ..
    have he3:‖A (acts (1-Aop) x)‖≤ z:= cap (bright0 (j:=j) i hp) (acts (1-Aop) x); linarith only [he2,he3]
 change s/2*t ≤ ‖A x‖; have hy':0≤z:=norm_nonneg _; have hr:=mul_le_mul_of_nonneg_right v.le ht; change z≤b*t at vh; nlinarith only [hy,W',vh,mul_le_mul_of_nonneg_left hh hz.le,mul_le_mul_of_nonneg_right hs hy', hr] -- tune
/-- for instance choose δ=(b/4)^2. then
 ‖P positive‖ term costs b/4, minus on low = ≥3/4 of minus amplitude. -/
lemma temper (j:ℕ)(b:ℝ)(hz:0<b)(hb:b≤1)(i:Jill.Male)(p:Bin) (hp:Bound Real.pi p) (h: disk j i p ≤ (b/4)^2) (x:Ket SpinIdx)(w:b *‖x‖ ≤ ‖acts (1-Aop) x‖): b/2*‖x‖ ≤ ‖acts (bar j i.val (tmap p)) x‖:= by
 let Q:=acts (bar j i.val (tmap p)); let y:=acts Aop x; let z:=acts (1-Aop) x; have hl:= bright (j:=j) i hp x
 have hp: IsStarProjection Aop :=⟨AOne,Aadj⟩
 have hy: ‖Q y‖ ≤ b/4 *‖y‖:= ambL (by positivity) (by rw [show ‖Q y‖^2=disk j i p*‖y‖^2 from hl.1,mul_pow]; exact mul_le_mul_of_nonneg_right h (sq_nonneg _))
 have he: (3/4:ℝ)^2 ≤ 1-disk j i p:=by nlinarith
 have ht:3/4*‖z‖ ≤ ‖Q z‖:= ambL (by positivity) (by rw [mul_pow,show ‖Q z‖^2=(1-disk j i p)*‖z‖^2 from hl.2]; exact mul_le_mul_of_nonneg_right he (sq_nonneg _))
 have hv: ‖Q z‖ ≤ ‖Q x‖+‖Q y‖:= by nth_rw 1 [show Q z= Q x-Q y by rw [eq_sub_iff_add_eq,←map_add,add_comm]; exact congrArg Q (lunar (A:=Aop) x).symm]; exact norm_sub_le ..
 change b/2*‖x‖ ≤ ‖Q x‖; change b*_ ≤ ‖z‖ at w; have hr:b*‖y‖ ≤ b*‖x‖:=mul_le_mul_of_nonneg_left (cap hp x) hz.le
 linarith only [hv,hy,w,ht,hr]
end Retain
end YM.CF.Signal.Sparkle
