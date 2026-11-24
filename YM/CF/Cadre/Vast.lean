import YM.CF.Cadre.Mora
import YM.CF.Cadre.Byte
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
open PowerSeries
variable (V: leaf A→ Finset A→PS)(v:∀ X:Palot.leaf A,∀ D ⊆ X.val,cent (V X D))(Q: leaf A→ℝ)(q:0≤Q)(κ:ℝ)(m:1≤κ)(L w:ℝ)(b:leaf A→ℝ)
abbrev bark (i:ℕ)(t:ℝ): leaf A→Finset A→ℝ:=fun X D=> mintL i t (V X D)
abbrev seed_v(i:ℕ)(t:ℝ):ΣA→ℝ:=roofL (bark V i t) κ
abbrev loom_v(t:ℝ)(X:ΣA):= Real.exp ((L-w*t)*b X)
local notation "Bt"=> loom_v L w b
local notation "G0"=> seed_v V κ
abbrev sched(i:ℕ)(t:ℝ):ΣA→ℝ:= roofL (fun X D=> mintL i t (derivative ℝ (V X D))) κ
abbrev serif(o:A)(i:ℕ)(t:ℝ):= nook (G0 i t*Bt t) o
abbrev cubL(o:A)(i:ℕ)(t:ℝ):=nook (sched V κ i t*Bt t) o
local notation "Ωv"=> serif V κ L w b
local notation "Ψs"=> cubL V κ L w b
abbrev foe(o:A)(i:ℕ)(t:ℝ):=nook (G0 i t * Bt t * b) o -- moment
local notation "XI"=> foe V κ L w b
lemma zap (X:ΣA)(i:ℕ)(t:ℝ):HasDerivAt (fun t=>G0 (i+1) t X) (sched V κ i t X) t:=HasDerivAt.fun_sum (fun j _=> (cent.lead (V X j) i t).const_mul _)
lemma zerk(X:ΣA)(t:ℝ): HasDerivAt (fun t=>Bt t X) ((Bt t) X*(-w*b X)) t:=by
 apply (((((hasDerivAt_id' t).const_mul w).const_sub L).mul_const (b X)).exp).congr_deriv; simp only [loom_v,mul_one] -- tune ordering
lemma trek(o:A)(i:ℕ)(t:ℝ): HasDerivAt (fun t=>Ωv o (i+1) t) (Ψs o i t-w*(XI o (i+1) t)) t:=by
 let F(t:ℝ)(X:ΣA):= G0 (i+1) t X * Bt t X; let g(X:ΣA):=sched V κ i t X * Bt t X + (G0 (i+1) t X) * (Bt t X * (-w*b X)); have hv(X:ΣA): HasDerivAt (fun t=>F t X) (g X) t:=(zap V κ X i t).mul (zerk L w b X t)
 apply (HasDerivAt.fun_sum (fun j (_:j∈spark o)=> hv j)).congr_deriv
 unfold cubL foe Cadre.nook g; rw [mul_sum,←sum_sub_distrib]
 apply sum_congr rfl; intro i _; simp only [Pi.mul_apply]; ring
abbrev moss (X:ΣA)(D:Finset A)(P₀:ΣA→ℝ):PS:= if D.Nonempty then 0 else PowerSeries.C (P₀ X)
abbrev arpX(X:ΣA)(D:Finset A)(Q': ΣA→ ℝ):PS:=∑ Y:ΣA, fizz X Y D V (Q' Y)
variable {k s t:ℝ}{s':Palot.leaf A→ℝ}
lemma rodp (i:ℕ)(X:ΣA)(K:ΣA→ℝ)(t:ℝ):∑ D∈X.val.powerset,duty κ D* mintL i t (moss X D K)=K X:=by
 rw [sum_eq_single ∅]; unfold moss duty mintL; rw [if_neg (Finset.not_nonempty_empty),if_neg (Finset.not_nonempty_empty),sum_eq_single 0,coeff_zero_C]; simp; intro j u w; rw [coeff_C,if_neg]; simp; exact w; simp; intro D _ p; rw [moss,if_pos (Finset.nonempty_iff_ne_empty.mpr p)]; simp [mintL]; simp
lemma mintP(X Y:PS)(i:ℕ): mintL i t (X+Y) = mintL i t X+mintL i t Y:=by simp_rw [mintL, map_add,mul_add,sum_add_distrib]
include v q m
lemma opt (X Y:ΣA)(i:ℕ)(t:ℝ)(h:0≤t):
 ∑ D∈ X.val.powerset,duty κ D*mintL i t (fizz X Y D V (Q Y))≤ ode0 Q (G0 i t) X Y:=by
 let S:=farW A; let w':= bark V i t; have ht:= nodeV Y w' (fun i D p=> (v i D p).negℜ _ h _) m X S; unfold ode0 tweak; refine le_trans ?_ (mul_le_mul_of_nonneg_left ht (q Y)); rw [mul_sum]; apply sum_le_sum; intro D n; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (reprice Y D h v X _ (q Y)) (zero_le_one.trans (duty_i _ m))
lemma seed_nn (i:ℕ)(t:ℝ)(h:0≤t):0≤ G0 i t:=fun X=> sum_nonneg fun D u => mul_nonneg (zero_le_one.trans (duty_i _ m)) ((v X D (mem_powerset.mp u)).negℜ t h _)
omit v q m
-- typed Marc inequality jets
lemma mintK{ι:Type*}(S:Finset ι)(K:ι→ PS)(i:ℕ):mintL i t (∑ j∈S,K j)=∑ j∈ S,mintL i t (K j):=by simp_rw [mintL,map_sum,mul_sum]; rw [sum_comm]
lemma trend {C G:PS}{x:ℝ}(t:0 ≤ x)(p:∀ i:ℕ,coeff i C ≤ coeff i G)(i:ℕ): mintL i x C ≤ mintL i x G:=sum_le_sum (fun j _=> mul_le_mul_of_nonneg_left (p j) (by positivity))
variable {R:Palot.leaf A→Finset A→PS}
abbrev flowZ(s:Palot.leaf A→ℝ)(v:Palot.leaf A→Finset A→PS):Prop:=∀ X:Palot.leaf A,∀ D ⊆ X.val,∀ n:ℕ,(coeff n) (derivative ℝ (v X D)) ≤ (coeff n) (moss X D s+arpX V X D Q)
variable (sR:Palot.leaf A →ℝ)(mF:flowZ V Q sR R)(mG:flowZ V Q sR V)(o:A)
include mF v q m
lemma roar(i:ℕ)(ht:0≤t)(x:ΣA):sched R κ i t x ≤ sR x +∑ Y:ΣA,ode0 Q (G0 i t) x Y:=by
 let D(X:ΣA)(u:Finset A):PS:=arpX V X u Q; let M:=x.val.powerset
 have hp(Y:ΣA):=opt V v Q q κ m x Y i t ht
 have hk:=sum_le_sum (s:=univ) (fun (Y:ΣA) _=>hp Y); rw [sum_comm] at hk
 apply le_trans _ (add_le_add_right hk _); rw [←rodp κ i x sR t, ←sum_add_distrib]; refine sum_le_sum fun D p=>?_ ; rw [←mul_sum,←mul_add,←mintK, ←mintP]; exact mul_le_mul_of_nonneg_left (trend ht (mF x D (mem_powerset.mp p)) _) (zero_le_one.trans (duty_i _ m)) -- tune
omit mF
end YM.CF.Cadre
