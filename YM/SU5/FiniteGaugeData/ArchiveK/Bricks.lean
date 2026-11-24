import YM.SU5.FiniteGaugeData.ArchiveK.Hinge
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
set_option linter.unusedSectionVars false
namespace Midway
open Waltz Violas
variable {S T:Finset Cover}(A B:Finset Cover) {N:Side}{σ c C f k r a:ℝ}{P₀:Momentum→Op SpinIdx}{F:Tulip.Male}{n m d j:ℕ}
variable {X Z:Type*}[Fintype X][DecidableEq X][Fintype Z][DecidableEq Z]
section cart
variable (M:Ruler (Beam B) X)(Y: Cover→ Ruler SpinIdx X)
local notation "U"=> Beam B
local notation "V"=> Beam T
local notation "Ψ"=>inp N T
abbrev reset (S:Finset Cover)(Y: Cover→Ruler SpinIdx X) : Cover→Ruler SpinIdx X:=fun x=>if x∈ S then Y x else 0
abbrev torso (T:Finset Cover)(Y:Cover→Ruler SpinIdx X) : Ruler (Beam T) X:=Matrix.of fun i x=> Y i.1.val i.2 x
lemma torso_bill {u:ℝ}(Z:0≤u)(p:∀ i∈ T,‖Y i‖≤u): ‖torso T Y‖ ≤ page (Beam T)*(page X:ℝ)*u:= jingle _ u Z (fun i j=> (mTouch (Y i.1.val) i.2 j).trans (p i.1.val i.1.property))
lemma torso_bill' (p:∀ i, i∉S→Y i=0) : cutM (wrist T S)*torso T Y=torso T Y:=by apply Matrix.ext; intro i j; rw [compass]; by_cases h:i∈wrist T S; rw [if_pos h]; rw [if_neg h]; unfold torso; rw [Matrix.of_apply,p _ (by simpa [wrist] using h)]; rfl
variable (H: Waltz N T)(P:S⊆T)(g:∀ v'∈S,∀ i:Cover,i∈ box d→v'-i∈T) (y:∀ i:Cover,i∉S→ Y i=0)
local notation "F"=> torso T Y
local notation "M₀"=> inp N T*torso T Y
-- actual op bound; exactly equal by embedding (apart+wind.Parse). need only approx.Cap.R.
include H P g y
lemma legg (f:Cover→Op SpinIdx)(w:Cover)(p:w∈box d) : wagon N f w*(Ψ * (torso T Y))= (Ψ)* (torso T (fun i=>f w *Y (i+w))):=by
 let A:= Ψ; let M:= M₀; let S':= cutM (wal N S); let R:=cutM (wrist T S); let X:= cutM (wal N T); let Z:= wagon N f w; have hm:M=A*(F):=rfl; have ht:R*(F)=F:=torso_bill' Y y; have hd:S'*M=M:=by rw [hm,←Matrix.mul_assoc, show S'*A=A*R from inp_inc H P univ, Matrix.mul_assoc,ht]
 have hk: X*(Z*M)= Z*M:= by nth_rw 1 [← hd]; rw [←Matrix.mul_assoc Z S', ←Matrix.mul_assoc X _ M,←Matrix.mul_assoc X Z S', wagonT_pay P g p, Matrix.mul_assoc, hd] -- tune
 let Q:= torso T (fun i:Cover=> f w * Y (i+w))
 have he:Aᴴ* Z * M=Q:=by
    rw [hm]; nth_rw 1 [←ht]; rw [←Matrix.mul_assoc A,←Matrix.mul_assoc,←Matrix.mul_assoc]; apply Matrix.ext; intro i j; rw [Matrix.mul_apply]; -- -- tune assoc to warp: want `Aᴴ*wagon*A*R` instead of `Aᴴ*Z*(A*R)`. rewrite
    let x:= i.1.val+w; by_cases h:x∈S
    · let q:T:=⟨x,P h⟩; change ∑ y:Beam T, _ = (f w* Y x) i.2 j; rw [Fintype.sum_prod_type]; rw [Finset.sum_eq_single q]
      · rw [Matrix.mul_apply (M:=f w) (N:=Y x)]; apply Finset.sum_congr rfl; intro k _ -- tune RHS matrix_mul_apply
        rw [show (Aᴴ*Z*A*R) i (q,k)=f w i.2 k from ?_]; rfl
        rw [H.wagon_inc P g p, if_pos ⟨h,eq_sub_of_add_eq rfl⟩]
      · intro b _ hb; apply Finset.sum_eq_zero; intro k a; rw [show (Aᴴ*Z*A*R) i (b,k) =_ from H.wagon_inc P g p i (b,k), if_neg (fun l=> hb (Subtype.ext (eq_sub_iff_add_eq.mp l.2).symm)),zero_mul]
      simp
    change _=(f w * Y x) i.2 j; rw [y _ h,Matrix.mul_zero]; refine Finset.sum_eq_zero fun k t=>?_ ; rw [show (Aᴴ*Z*A*R) i k =_ from H.wagon_inc P g p i k, if_neg (fun (p:k.1.val∈S∧i.1.val=k.1.val-w)=> h (by unfold x; rw [eq_sub_iff_add_eq.mp p.2]; exact p.1)),zero_mul]
 change Z*M=A*Q; rw [←he,←Matrix.mul_assoc A (Aᴴ*Z) M, ← Matrix.mul_assoc A _ Z, show A*Aᴴ=cutM (wal N T) from H.tendril, Matrix.mul_assoc (cutM (wal N T))]; exact hk.symm
-- estimate on mask + cut. op tun.
def tulp (P₀:Momentum→Op SpinIdx)(d:ℕ) (x:Cover): Ruler SpinIdx X:=∑ i∈ Lattice.box d,tub P₀ i * Y (x+i)
lemma boot : plateH P₀ N d * (M₀) = (Ψ)*torso T (tulp Y P₀ d):= by
 unfold plateH; rw [Matrix.sum_mul, show torso T (tulp Y P₀ d) = ∑ i∈Lattice.box d,torso T (fun x=> tub P₀ i * Y (x+i)) from ?_, Matrix.mul_sum]; apply Finset.sum_congr rfl (fun i p=> legg Y H P g y (tub P₀) i p); apply Matrix.ext; intro i j; rw [Matrix.sum_apply]; unfold torso tulp; simp_rw [Matrix.of_apply,Matrix.sum_apply]
omit H P g y
abbrev fleece (x:Cover): Ruler SpinIdx X:= fuelR B x * M
local notation "Φ"=> fleece B M
variable (v:Ream P₀ c C)(p0:0<c)(T0:∀ x∈T,∀ b∈B,‖∑ i∈Lattice.box d,tub P₀ i *fpS ((x-b)+i)‖ ≤ Real.exp (-c*d)*pride C)
include v p0
omit v p0 in
lemma bust (K:ℝ)(e:∀ z:Cover, ‖fpS z‖ ≤ K)(k:0≤ K)(x:Cover) : ‖fleece B M x‖ ≤ (4*page U *K)*‖M‖:= by
 unfold fleece; refine (Matrix.l2_opNorm_mul ..).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)); apply le_trans (jingle _ K k (fun i j=> ?_)); swap; · exact (mTouch (fpS _) i j.2).trans (e _)
 unfold page; rw [Fintype.card_fin]; push_cast; rfl -- ≤
lemma C_free :0≤ C:=le_trans (norm_nonneg (rollK P₀ 0)) (rollC p0 v _)
include T0
lemma knot_pay(i:Cover)(hx:i∈T): ‖tulp (Φ) P₀ d i‖ ≤ (4*(page U)*Real.exp (-c*d)*pride C)*‖M‖:= by
 unfold tulp fleece; simp_rw [←Matrix.mul_assoc,←Matrix.sum_mul]; let Y:=Real.exp (-c*d)*pride C; have hp:0 < Y:=mul_pos (Real.exp_pos _) (pride_p _ (C_free v p0)); refine (Matrix.l2_opNorm_mul ..).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)); apply le_trans (jingle _ Y hp.le (fun a b=>?_)); swap
 · let B':Cover:= b.1.val; let f(q:Cover):=fpS (i-B'+q); let F₁:=tub P₀; have he(q:Cover): (F₁ q*fuelR B (i+q)) a b=(F₁ q*fpS (i-B'+q)) a b.2:=by simp_rw [Matrix.mul_apply]; unfold fuelR; unfold B'; simp_rw [Matrix.of_apply,show i+q-b.1.val= i-b.1.val+q from (by abel)] -- rewrite under.B.
   rw [Matrix.sum_apply]; simp_rw [show ∀ z:Cover,(tub P₀ z*fuelR B (i+z)) a b=(F₁ z*fpS (i-B'+z)) a b.2 from he, ← Matrix.sum_apply]; exact (mTouch _ a b.2).trans (T0 i hx _ b.1.property)
 unfold Y page; rw [Fintype.card_fin]; push_cast; apply le_of_eq; ring
lemma clip (kH:ℕ)(tB:B⊆ S)(p:0<r)(t:r≤1)(u:tubeman B kH * M=0)(h:∀ x:Cover,x∉ S→∀ y∈B,River r (emitX x) (emitX y))(i: Cover)(y':i∈T) : ‖tulp (reset S Φ) P₀ d i‖ ≤ (4*page U*Real.exp (-c*d)*pride C+ (C*4*page U* rover)* r^kH)*‖M‖:=by
 let P:=tulp (reset S Φ) P₀ d i; let Q:=tulp Φ P₀ d i; let H(q:Cover):= Φ q; let V' := 4*(page U:ℝ)*rover*r^kH; let V'':= V'*‖M‖; have hp:0≤ V':=by unfold V'; have h:=rover_n; positivity
 have hk(q:Cover): ‖reset S H q-H q‖ ≤ V'* ‖M‖:=by
    unfold reset; split; · rw [sub_self,norm_zero]; exact mul_nonneg hp (norm_nonneg _)
    rename_i b; rw [zero_sub,norm_neg]; exact candle B q p t (h q b) (fun w=> b (tB w)) M u
 have hK:‖P-Q‖ ≤ C*(V'* ‖M‖):=by
    unfold P Q tulp; rw [←Finset.sum_sub_distrib]; simp_rw [←Matrix.mul_sub]; apply (norm_sum_le ..).trans; refine (Finset.sum_le_sum (g:=fun j:Cover=> ‖tub P₀ j‖*(V'* ‖M‖)) (fun j _=>?_)).trans ?_; · exact (Matrix.l2_opNorm_mul ..).trans (mul_le_mul_of_nonneg_left (hk _) (norm_nonneg _))
    obtain H' := v.reserve.unweighted p0.le; rw [← Finset.sum_mul]; apply mul_le_mul_of_nonneg_right ((H'.2.1.sum_le_tsum _ (fun i _=>norm_nonneg _)).trans H'.2.2) (mul_nonneg hp (norm_nonneg _))
 have hu: ‖Q‖ ≤ _:= knot_pay B M v p0 T0 i y'; unfold V' at hK; change ‖P‖ ≤ _; linarith only [hK,norm_sub_norm_le P Q, hu] -- hop
#print axioms clip
end cart
end Midway
end YM.CF.Window.ArchiveK
