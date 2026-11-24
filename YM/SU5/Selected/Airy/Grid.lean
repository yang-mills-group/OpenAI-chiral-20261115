import YM.SU5.Selected.Airy.Frame
import YM.SU5.Selected.Airy.Trapeze
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset
open Lat Rush
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
abbrev Br (d:Type*):= d → roundC
abbrev Coast:= Br Axis
-- base samples restrict to quotient
variable (N:Side)
def brim (k:Site N):Coast:= fun i=> ((pm k i:ℝ): roundC)
variable {N}
def prefixG {d:Type*}[Fintype d](v:d→ℤ)(z:Br d):ℂ:= ∏ j:d, fourier (v j) (z j)
lemma paddles (v:Cover)(k:Site N) : mode (mel k) v=prefixG v (brim N k):=by
 unfold mode prefixG; rw [Finset.mul_sum,Complex.exp_sum]; apply Finset.prod_congr rfl; intro j _; unfold brim; rw [soldier]; unfold mel tmap surge; push_cast; congr 1; ring
lemma freeze_rim (k x: Site N) : Fourier N x k=prefixG (natural x) (brim N k)/normF N:=by rw [← paddles, freq_mode]; rfl
-- alias application restrict
lemma scene_coe (k:Per N) : ((Lat.principal k:ℝ):roundC)= ((winding k:ℝ):roundC):=by
 unfold Lat.principal; split; rfl; rw [AddCircle.coe_sub, AddCircle.coe_period,sub_zero]
variable (D:Side) (p:D.val∣N.val)
def blip (x y : roundC) := x+y
lemma bornT (i:Axis)(k:Site N): brim N k i=(((π/N.val:ℝ): roundC))+(k i).val • tier N:=by
 rw [brim,show pm k i=_ from (show _=Lat.principal _ from rfl),scene_coe,tier, ←AddCircle.coe_nsmul,←AddCircle.coe_add]; unfold winding; congr 1; rw [nsmul_eq_mul]; ring
lemma flipRoot : D.val • tier D=0:= by
 nth_rw 1 [← show addOrderOf (tier D)=D.val from AddCircle.addOrderOf_period_div (p:=φ) D.property]; exact addOrderOf_nsmul_eq_zero _
include p
lemma alias_seed : (N.val/D.val) • tier N=tier D:=by
 unfold tier; rw [←AddCircle.coe_nsmul]; congr 1; have hx:(((N.val/D.val:ℕ):ℝ)*D.val)=N.val:= by exact_mod_cast Nat.div_mul_cancel p
 have he : (N.val:ℝ)≠0:= (nPos N).ne'; have hk:= (nPos D).ne'; rw [nsmul_eq_mul]; field_simp; linear_combination hx
omit p
def raise (N:Side)(D:Side)(i:Axis)(s:ℕ)(x:Site N): Site N:= x + Pi.single i ((s*(N.val/D.val):ℕ):Per N)
def raised {d:Type*}[DecidableEq d](D:Side)(i:d)(s:ℕ)(w:Br d): Br d:= w + Pi.single i (s • tier D)
private lemma going (i:ℕ): (i%D.val) •tier D=i •tier D:=by
 nth_rw 2 [← Nat.mod_add_div i D.val]; conv_rhs => rw [add_smul,mul_comm D.val,mul_smul,flipRoot,smul_zero,add_zero]
include p
lemma rise_point (i:Axis)(s:ℕ)(x:Site N): brim N (raise N D i s x)=raised D i s (brim N x):=by
 ext1 j; rw [bornT, raised,Pi.add_apply,bornT]; by_cases k:j=i
 · subst j; rw [Pi.single_eq_same,raise,Pi.add_apply, Pi.single_eq_same,ZMod.val_add,going, add_smul,ZMod.val_natCast,going,mul_smul,alias_seed D p,add_assoc]
 rw [Pi.single_eq_of_ne k, raise,Pi.add_apply,Pi.single_eq_of_ne k,add_zero,add_zero]
lemma stay (i:Axis)(s:ℕ)(x k: Site N)(h:D.val ∣ (x i).val) : Fourier N x (raise N D i s k)= Fourier N x k:=by
 rw [freeze_rim,freeze_rim,rise_point D p]; unfold prefixG; congr 1; apply Finset.prod_congr rfl; intro j _
 rw [raised,Pi.add_apply]; by_cases e: j=i
 · subst j; have ht (f:ℤ)(g:(D.val:ℤ)∣ f): f • tier D=0:= addOrderOf_dvd_iff_zsmul_eq_zero.mp (by rwa [show addOrderOf (tier D)=D.val from AddCircle.addOrderOf_period_div (p:=φ) D.property]); have hr:(D.val:ℤ)∣ natural x i:= by unfold natural; exact_mod_cast h
   rw [Pi.single_eq_same, mon_add,mon_walk]; conv_lhs => rhs; rw [fourier_apply,ht _ hr]; -- then tune
   simp
 rw [Pi.single_eq_of_ne e,add_zero]
omit p

variable {X n:Type*} [Fintype X][DecidableEq X] [Fintype n][DecidableEq n]
attribute [local instance] opCStarAlgebra
def raiser (D:Side)(i:Axis)(F:Coast→ Op n):Coast→Op n:= (↑D.val:ℂ)⁻¹ • (∑ s∈ Finset.range D.val, F ∘ raised D i s)
variable (x:X→Site N × n)
-- horizontal mask layer
lemma levy (i:Axis)(F: Coast→ Op n)(a b:n)(w: Coast): raiser D i F w a b=(↑D.val:ℂ)⁻¹*∑ s∈ Finset.range D.val,F (raised D i s w) a b:=by unfold raiser; simp [Matrix.sum_apply,Finset.sum_apply]
include p
lemma tightrope (i:Axis)(e:∀ j,D.val∣ ((x j).1 i).val)(F:Coast→ Op n) :
   (mask x)ᴴ * freeze ((raiser D i F) ∘ brim N) * mask x= (mask x)ᴴ * freeze (F ∘ brim N) * mask x :=by
 let g(s:ℕ)(B:Site N):= F (raised D i s (brim N B));
 have he(s:ℕ) : (mask x)ᴴ * freeze (g s) * mask x=(mask x)ᴴ * freeze (F ∘ brim N) * mask x:=by
    ext a b; rw [mask_mem,mask_mem,mask_star_mem,mask_star_mem, ← Prod.eta (p:=x a), ← Prod.eta (p:=x b)] -- check name/order
    rw [freeze_charge,freeze_charge]; rw [←Equiv.sum_comp (Equiv.addRight (Pi.single i ((s*(N.val/D.val):ℕ):Per N))) (fun k:Site N=> Fourier N (x a).1 k * (((F ∘ brim N) k) _ _) * star (Fourier N (x b).1 k))]; -- binder
    apply Finset.sum_congr rfl; intro b0 v; change _*g s b0 _ _*_= Fourier N _ (raise N D i s b0)*F (brim N (raise N D i s b0)) _ _*star (Fourier N _ (raise N D i s b0)); rw [stay D p i s _ _ (e a),stay D p i s _ _ (e b),rise_point D p]; -- rfl?
 have hx:(raiser D i F)∘brim N = (↑D.val:ℂ)⁻¹ • (∑ s∈ Finset.range D.val,g s):=by
    ext1 k; unfold raiser; simp only [Pi.smul_apply,comp,Finset.sum_apply, g]; -- tune
 rw [hx,freeze_smul,freeze_sum,Matrix.mul_smul, Matrix.smul_mul, ships_add',ships_add]; simp_rw [he]
 rw [Finset.sum_const,card_range,←Nat.cast_smul_eq_nsmul ℂ]; exact inv_smul_smul₀ (side_ne _) _
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms tightrope
#print axioms rise_point
#print axioms paddles
