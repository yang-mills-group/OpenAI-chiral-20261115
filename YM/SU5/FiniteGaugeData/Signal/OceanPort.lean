import YM.SU5.FiniteGaugeData.Signal.Hedging
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 14000
noncomputable section
namespace YM.CF.Signal.Sparkle
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace Kea
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b u v:ℝ}{i j d k:ℕ}
namespace LocalPlane
variable (x:Site N)(l:Slot)
def capsule (v:Ket SpinIdx): Ket (Single N):= ∑ i: SpinIdx,v.ofLp i • basisKet ((x,i),l)
lemma capsuleAt (v:Ket SpinIdx)(y:Single N): (capsule x l v).ofLp y= if y.1.1=x∧y.2=l then v.ofLp y.1.2 else 0 :=by
 unfold capsule; rcases y with ⟨⟨y,i⟩,s⟩; by_cases h:y=x <;> by_cases p:s=l <;> simp [WithLp.ofLp_sum,Finset.sum_apply,h,p]
 simp [Pi.single_apply,mul_ite]
lemma fitP {I:Type*}[Fintype I] (x:Ket I): ‖x‖^2 = ∑ i:I, ‖x.ofLp i‖^2 := PiLp.norm_sq_eq_of_L2 _ x
lemma budgetV (v:Ket SpinIdx): ‖capsule x l v‖=‖v‖:= by
 have he: ‖capsule x l v‖^2=‖v‖^2:=by
   rw [fitP,fitP]; simp_rw [capsuleAt]; -- Fintype.Sum prod (expands Slot too) simplify
   rw [show (∑ i:Single N,_)=∑ i:Site N×SpinIdx,∑ k:Slot, ‖if i.1=x ∧ k=l then v.ofLp i.2 else 0‖^2 from Fintype.sum_prod_type _]; rw [Fintype.sum_prod_type]; simp only []; -- tune; change?
   rw [sum_eq_single x]; · simp [apply_ite (fun x:ℂ=> ‖x‖),ite_pow]
   · intro y _ n; simp [n]
   simp
 nlinarith [he,norm_nonneg (capsule x l v),norm_nonneg v]
def hall (v:Ket (Single N)) (l:Slot)(x: Site N): Ket SpinIdx:= WithLp.toLp 2 fun i:SpinIdx=> v.ofLp ((x,i),l)
lemma color_fee (v:Ket (Single N)): ‖v‖^2=∑ t:Site N, ∑ k:Slot, ‖hall v k t‖^2:=by
 simp_rw [fitP]; rw [← sum_comm, show (∑ i:Single N, ‖v.ofLp i‖^2) = ∑ a: Site N × SpinIdx, ∑ k:Slot, ‖v.ofLp (a,k)‖^2 from Fintype.sum_prod_type _]; rw [sum_comm (f:=fun a k=> ‖v.ofLp (a,k)‖^2)]; apply sum_congr rfl; intro i _; rw [Fintype.sum_prod_type]; rfl
private lemma optic_norm (x y:Site N): ‖star (Fourier N x y)‖^2=(↑N.val : ℝ)⁻¹ ^4:= by
 rw [norm_star,Lat.Fourier]; simp only [Matrix.of_apply,norm_div]; have he:= frequency_unit y x; have hx : ‖frequency y x‖^2=1:=by
   rw [pow_two]; nth_rw 1 [← norm_star (frequency y x)]; rw [← norm_mul,he,norm_one]
 rw [div_pow,hx]; simp only [Lat.normF,norm_pow, Complex.norm_natCast]; rw [one_div,inv_pow]; ring_nf

local notation "U0"=> colU N
lemma optic (v:Ket SpinIdx)(t:Site N)(g:Slot): hall (acts (star (colU N).val) (capsule x l v)) g t= if g=l then star (Fourier N x t) • v else 0:=by
 unfold capsule; apply PiLp.ext; intro i; rw [map_sum]; by_cases h:g=l<;> simp [hall, Finset.sum_apply, WithLp.ofLp_sum,basis_act, Matrix.star_apply, coil, h, Pi.single_apply,apply_ite (starRingEnd ℂ),mul_ite,eq_comm (a:=l) (b:=g),mul_comm]
lemma hall_field (A:Stag N→Op SpinIdx)(v:Ket (Single N)) : hall (acts (arch A) v) l x=acts (A (x,l)) (hall v l x):=by
 apply PiLp.ext; intro j; unfold hall; change (acts (arch A) v).ofLp ((x,j),l)= _; rw [act_at,act_at]; change ∑ a: Single N, arch A ((x,j),l) a * v.ofLp a= ∑ i:SpinIdx,A (x,l) j i*v.ofLp ((x,i),l); simp_rw [arch_at]; rw [Fintype.sum_prod_type]; rw [Fintype.sum_prod_type]; simp only []; -- maybe second expands Slot wrong
 rw [sum_eq_single x]; swap; · intro z u h; simp [Ne.symm h]
 swap; · simp
 apply sum_congr rfl; intro i _; simp [ite_mul]
lemma receipt (A:Stag N→Op SpinIdx)(v:Ket SpinIdx) : ‖acts (Dofu N A) (capsule x l v)‖^2=(↑N.val:ℝ)⁻¹ ^ 4 * ∑ i:Site N, ‖acts (A (i,l)) v‖ ^2 :=by
 rw [show Dofu N A=twist (colU N) (arch A) from rfl,twist_formula, mul_assoc, act_mul, act_unit_norm, act_mul]; rw [color_fee,mul_sum]; apply sum_congr rfl; intro i _; rw [sum_eq_single l]; swap; · intro x u h; rw [hall_field, optic,if_neg h]; simp
 swap; simp
 rw [hall_field, optic,if_pos rfl,map_smul,norm_smul,mul_pow,optic_norm]

lemma free1 : (Kea.tax emptyC : Bkg (More N))=1:=by funext i; apply group.mat_injective; change Matrix.diagonal (pw ∘ skyV.val)=(1:Op SU.F); ext a b; by_cases e:a=b <;> simp [e,Matrix.one_apply,pw,BZ.phase,skyV]
variable (M:Jill.Male)
local notation "P"=> funde j M N 1
lemma nightly (h:Kea.Pad j N) : funde j M N 1=Dofu N (fun i=> bar j M.val (tmap (pm i.1))) :=by
 let S:= too N; have he:= h.2 _ S M; rw [free1,profile_trivial] at he; rw [he]; apply congrArg; funext t; rw [Kea.field, too_u]
lemma compass (j:ℕ)(p:Pad j N): IsStarProjection (funde j M N 1):=by
 rw [nightly M p]; have he: (fun i:Stag N=> bar j M.val (tmap (pm i.1)))= field (too N) j M:= by ext1; rw [field,too_u]
 rw [he]; exact idol _ j M p.1
-- Solo color at FREE. direct requested for slot reading invariance
lemma colorOne (A:Stag N→ Op SpinIdx)(i j:Single N)(h:i.2≠j.2): Dofu N A i j=0:=by
 rw [show Dofu N A=twist (colU N) (arch A) from rfl,twist_formula,Matrix.mul_apply]; apply sum_eq_zero; intro k _; rw [Matrix.star_apply,coil, wool]; by_cases u:i.2=k.2; · simp only [if_pos u,if_neg (show ¬ (j.1.2=k.1.2∧j.2=k.2) from fun l=> h (u.trans (l.2.symm))),star_zero,mul_zero]
 rw [if_neg u]; simp
end LocalPlane
end YM.CF.Signal.Sparkle
