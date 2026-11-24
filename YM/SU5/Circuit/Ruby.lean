import YM.CF.Onyx.Quod
import YM.Next.FREE_KERNELS.Ground
set_option autoImplicit false
set_option linter.unusedSectionVars false
-- recall hats lobby
noncomputable section
namespace YM.Regis.Circuit
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Fir CF.Onyx
open Precision Exterior Matrix RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
/-! # Actual momentum grid. Don't replace periodic by anti-periodic! reuse
 sphere Pawns on proper shift. -/
variable {n:Side}{ι υ γ:Type*}[Fintype ι][Fintype υ][Fintype γ][DecidableEq ι][DecidableEq υ][DecidableEq γ]
variable (i:Site n)(p:Even n.val)
def rubyOff (n:Side):Offset n:= ⟨fun _=> -pinch n,(pi_norm_le_iff_of_nonneg (pinch_pos n).le).mpr fun i=> by simp [abs_of_nonneg (pinch_pos n).le]⟩
abbrev ruby(i:Site n):Bin:=glen (rubyOff n) i
def rubyM (i:Site n):Momentum:=tmap (ruby i)
include p in
lemma ruby_spin : rubyM i∈realCube Next.Free.zone:= base_subset_realCube Next.Free.zone_pos (b_base (orb i _ p)) -- include?
lemma ruby_pigment : physical (rubyM i):= tmap_physical _
private def plot : Cover:=fun j=>chert (i j)
lemma ruby_phase : ∃ k:Cover,rubyM i=mon i + reciprocal k:=by
 have h : wrap n (plot i)=i:=funext (fun j => chert_cast (i j))
 obtain ⟨z,e⟩:=cover_of_eq (lift i) (plot i) ((wrap_lift i).trans h.symm)
 refine ⟨z,?_⟩; funext j
 change ((principal (i j)+ -pinch n:ℝ):ℂ)= (n.val:ℂ)⁻¹ * (2*(Real.pi:ℂ)* (lift i j:ℤ))+2*Real.pi*(z j)
 have he: chert (i j)=(lift i) j+n.val • z j:=congr_fun e j; have ht:=side_ne n
 rw [ch_price,pinch,he,nsmul_eq_mul]; push_cast; field_simp; ring
lemma ruby_wrap (z:Cover) : Bloch.cell i (wrap n z)=charK (rubyOff n) i z:=by
 obtain ⟨k,hk⟩:=ruby_phase i; rw [cell_wrap]; change _=mode (rubyM i) z; rw [hk,mode_phase,mode_periodic,mul_one]
-- use abbreviations to avoid decidable
abbrev Expanse (n:Side) (A:Site n→Matrix ι υ ℂ)(X:Matrix (Co n ι) (Co n υ) ℝ):= Runs (rotations n ι) (rotations n υ) X (fiber A)
def tab (R:Row ι υ)(i:Site n):= R.read (rubyM i)
lemma expanse(R:Row ι υ)(a:R.safe) (n: Side):Expanse n (tab R) (R.acts n):=by
 have he: tab R=(fun i:Site n=>R.read (mon i)):= funext fun i=> by obtain ⟨z,h⟩:=ruby_phase i; rw [tab,h,Row.periods]
 rw [he]; exact circulant n R a
namespace Expanse
variable {A B: Site n→Matrix ι υ ℂ}{X Y: Matrix (Co n ι) (Co n υ) ℝ}
variable (a:Expanse n A X)(b:Expanse n B Y)
include a
lemma plusR (b:Expanse n B Y): Expanse n (fun i=> A i+B i) (X+Y):=by
 unfold Expanse Runs at *; have h : approached (X+Y)= approached X+ approached Y:=by ext i j; simp [approached]
 have hk : fiber (fun i=> A i+B i)=fiber A+fiber B:=by ext i j; by_cases h:i.1=j.1 <;> simp [fiber,h]
 rw [h,hk, Matrix.add_mul,Matrix.mul_add,a,b]
lemma chain {Z:Site n→Matrix υ γ ℂ}{z:Matrix (Co n υ) (Co n γ) ℝ}(k:Expanse n Z z):Expanse n (fun i=> A i*Z i) (X*z):=by
 have h:= a.product k; rw [fiber_mult] at h; exact h
lemma weight (t:ℝ): Expanse n (fun i=> (t:ℂ) • A i) (t• X):=by
 have h:= a.smult t; rw [fiber_weight] at h; exact h
lemma flip : Expanse n (fun i=> (A i)ᴴ) X.transpose:=by
 have h:= a.back (rotations_crew n ι) (rotations_crew n υ)
 rw [div_self (stage_ne _),one_smul,fiber_H] at h; exact h
lemma just (b:Expanse n B X):A=B:=by
 unfold Expanse Runs at *; let F:=rotations n ι
 have h:F*fiber A=F*fiber B:= a.symm.trans b
 have v:=congrArg (fun i=>Fᴴ*i) h
 have hk:Fᴴ*F=stageVolume n • (1: Matrix _ _ _):= (rotations_crew ..).2.2
 simp only [← Matrix.mul_assoc,hk, Matrix.smul_mul, Matrix.one_mul] at v
 replace v:=smul_right_injective _ (stage_ne n) v; funext i; ext a b; simpa [fiber] using congr_fun (congr_fun v (i,a)) (i,b)
end Expanse
lemma unit_exp (ι:Type*)[Fintype ι][DecidableEq ι](n:Side):Expanse n (fun _=> (1:Matrix ι ι ℂ)) 1:=by unfold Expanse; rw [fiber_one]; exact Runs.nil _
end YM.Regis.Circuit
#print axioms YM.Regis.Circuit.ruby_phase
#print axioms YM.Regis.Circuit.expanse
