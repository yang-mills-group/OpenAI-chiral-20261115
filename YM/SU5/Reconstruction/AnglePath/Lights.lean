import YM.SU5.Reconstruction.Trap.Castle
/-!
# Comparison of three illuminated frames. Generic.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Cardio
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K J H D:Hilbert} {X:Type}
open Clasp

/-- Phase and gauge χ. Data-vacuum kit. d not generally onto; density will be proved. Coordinates chosen so H means *physical* clock-a, and $R$ is result AFTER rotating a second-axis reading back to a; no price equality assumed, rather exact Gram match. J determined by tilted-angle purchase. -/
structure Organ (X:Type)[AddCommGroup X][Module ℂ X](H D:Hilbert) where
 L:X→ₗ[ℂ]H
 R:X→ₗ[ℂ]H
 d:X→ₗ[ℂ]D
 live:DenseRange L
 vive:DenseRange R
 strive:DenseRange d
 pair (x y:X):inner ℂ (L x) (R y)=inner ℂ (d x) (d y)
namespace Organ
variable [AddCommGroup X][Module ℂ X] (A:Organ X H D)
local notation "L"=>A.L
local notation "R"=>A.R
local notation "D₀" => A.d
lemma pair' (x y:X): inner ℂ (A.R x) (A.L y)=inner ℂ (A.d x) (A.d y):=by
 rw [←inner_conj_symm, A.pair, inner_conj_symm]
def Pre (C:Clasp K H H):Prop:= Faces L R R L K C -- pairing order
lemma pre : ∃ (K:Hilbert)(C:Clasp K H H), A.Pre C:= cert _ _ _ _ A.live A.vive A.vive A.live (fun x y=>(A.pair' x y).trans (A.pair x y).symm)
def Core (C:Clasp J H D):Prop:= Faces L D₀ R D₀ J C
lemma core : ∃ (K:Hilbert)(C:Clasp K H D), A.Core C:= cert _ _ _ _ A.live A.strive A.vive A.strive A.pair'
variable (G:Clasp K H H)(p:A.Pre G) (C:Clasp J H D)(q:A.Core C)
local notation "L'"=> G.l
local notation "R'"=> G.r
lemma Pre.face : Pre A G=Faces L R R L K G:=rfl
lemma Core.face : Core A C=Faces L D₀ R D₀ J C:=rfl
noncomputable def graphing (l:X→ₗ[ℂ] H)(r:X→ₗ[ℂ] D) (C:Clasp K H D): X→ₗ[ℂ] K:= C.l.adjoint.toLinearMap.comp l+C.r.adjoint.toLinearMap.comp r
lemma grow (l:X→ₗ[ℂ] H)(r:X→ₗ[ℂ] D) {U:X→H}{V:X→D} (C:Clasp K H D)(p:Faces l r U V K C): DenseRange (graphing l r C) ∧ C.l.toLinearMap.comp (graphing l r C)=l ∧ C.r.toLinearMap.comp (graphing l r C)=r:= by
 have h(x:X): C.l (graphing l r C x)=l x ∧ C.r (graphing l r C x)=r x:= (latch_dual ..).1 (p.sees x)
 refine ⟨p.full.mono ?_,LinearMap.ext fun x=>(h x).1, LinearMap.ext fun x=>(h x).2⟩
 rintro y ⟨x,a,b⟩; exact ⟨x,C.j ((h x).1.trans a.symm)⟩
abbrev revenue:= graphing A.L A.R G
abbrev budget:=graphing A.L A.d C
include p
lemma revenue_funding(x:X): G.l (A.revenue G x)=A.L x ∧ G.r (A.revenue G x)=A.R x:= ⟨DFunLike.congr_fun (grow _ _ G p).2.1 x,DFunLike.congr_fun (grow _ _ G p).2.2 x⟩
noncomputable def spread (_p:A.Pre G): K→L[ℂ] D:= (D₀).extendOfNorm (A.revenue G)
local notation "Z"=> A.spread G p
lemma spread_at (x:X): A.spread G p (A.revenue G x)=A.d x:= by
 let M:= ‖G.l‖+‖G.r‖; have hm:0≤M:=add_nonneg (norm_nonneg _) (norm_nonneg _)
 apply LinearMap.extendOfNorm_eq ((grow _ _ G p).1); refine ⟨M,?_⟩; intro x; have h:=A.revenue_funding G p x; let z:= ‖A.revenue G x‖
 have hz: 0≤ z:= norm_nonneg _
 have h1: ‖L x‖≤M*z:= by rw [←h.1]; exact (G.l.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg _)) hz)
 have h2: ‖R x‖≤ M*z:= by rw [←h.2]; exact (G.r.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _)) hz)
 have he : ‖D₀ x‖ ^2 ≤ (M*z)^2:= calc
     _ = ‖inner ℂ (L x) (R x)‖:=by rw [A.pair,inner_self_eq_norm_sq_to_K,norm_pow]; change _= ‖(↑‖D₀ x‖:ℂ)‖^2; simp
     _ ≤ ‖L x‖*‖R x‖:= norm_inner_le_norm ..
     _ ≤ _:= by rw [pow_two]; exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hm hz)
 change _≤M*z; nlinarith [mul_nonneg hm hz, norm_nonneg (D₀ x)]
lemma spread_dense : DenseRange (A.spread G p):=A.strive.mono (by rintro _ ⟨x,rfl⟩; exact ⟨A.revenue G x,A.spread_at G p x⟩)
lemma spread_inner (x y:K) : inner ℂ (Z x) (Z y)= inner ℂ (G.l x) (G.r y) := by
 have h (x:X) (y:K): inner ℂ (Z (A.revenue G x)) (Z y)=inner ℂ (L' (A.revenue G x)) (R' y):= by
    refine congrFun (((grow _ _ G p).1).equalizer (g:=fun y:K=> inner ℂ (Z (A.revenue G x)) (Z y)) (h:=fun y:K=> inner ℂ (L' (A.revenue G x)) (R' y)) (by fun_prop) (by fun_prop) ?_) y
    funext y; change inner ℂ (Z (A.revenue G x)) (Z (A.revenue G y))=inner ℂ (L' (A.revenue G x)) (R' (A.revenue G y)); rw [A.spread_at,A.spread_at,(A.revenue_funding G p x).1, (A.revenue_funding G p y).2,A.pair]
 refine congrFun (((grow _ _ G p).1).equalizer (g:=fun x:K=> inner ℂ (Z x) (Z y)) (h:=fun x:K=> inner ℂ (L' x) (R' y)) (by fun_prop) (by fun_prop) (funext fun x=>h x y)) x
lemma spread_inj : Injective (A.spread G p):=by
 intro x y e; apply G.k; apply G.p.eq_of_inner_right ℂ; intro z; rw [← A.spread_inner G p, ← A.spread_inner G p,e]
omit p
include q in
lemma core_funding(x:X): C.l (A.budget C x)=A.L x∧C.r (A.budget C x)=A.d x:= ⟨DFunLike.congr_fun (grow _ _ C q).2.1 x,DFunLike.congr_fun (grow _ _ C q).2.2 x⟩
include p q in
lemma spread_ready (x:K): C.Latch (G.l x) (A.spread G p x):=by
 obtain ⟨t,ht,hu⟩:=mem_closure_iff_seq_limit.mp ((grow _ _ G p).1 x); refine C.latch_limit atTop ((G.l.continuous.tendsto _).comp hu) (((Z).continuous.tendsto _).comp hu) (Eventually.of_forall fun i=> ?_)
 obtain ⟨y,v⟩:=ht i; change A.revenue G y=t i at v; change C.Latch (L' (t i)) (Z (t i)); rw [←v,A.spread_at, (A.revenue_funding G p y).1]; exact (show Faces L D₀ R D₀ J C from q).sees y
end Organ
end YM.CrossedFrame.Cardio
