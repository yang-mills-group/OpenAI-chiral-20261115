import YM.SU5.Relativistic.Icefall
import YM.SU5.FiniteGaugeData.Pannier.Blizzard
import YM.CF.Buffered.Lifted
/-! # Torus mass prefactor/all letters. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Cube Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Lat Fock Nacre Skye Scroll Rush Dial Tulip Pannier.Chancel UpStart Buffered
open Lifted (nodeC basisC node_of)
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra screen_fin
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
variable {d:ℕ}{s:Finset ℤ}{c:ℤ→Behind→ℂ}{a r:ℝ} (P:UpStart d s c r (2*a))
variable (n:Side)(M:Jill.Male)
local notation "Q"=> spar 4 M (1:Pane n)

def ear(n:Side): UNI (Single n):= ⟨(overU n SpinIdx).val ⊗ₖ (1:Op SU.Slot), Matrix.kronecker_mem_unitary (overU n SpinIdx).property (unitary _).one_mem⟩
local notation "W" => ear n
def snowMark (n:Side)(M:Jill.Male): Op (Single n):= Rush.mark n (bar 4 M.val) ⊗ₖ (1:Op SU.Slot)
lemma prime_fourier : Q= twist (ear n) (snowMark n M) :=by
 rw [spar,profile_trivial, funde_flat _ (by norm_num), show cart n (tub (bar 4 M.val))=plates n (bar 4 M.val) from cart_traded (cBar 4 M.val true (by decide) M.property) n,plates,twist_formula,twist_formula]
 let Y:=overU n SpinIdx; have hx: (star (ear n).val)=star Y.val ⊗ₖ (1:Op SU.Slot):=by
    ext ⟨i,j⟩ ⟨k,l⟩; rw [Matrix.star_apply]; unfold ear Y; simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.star_apply, star_mul]; by_cases p:j=l <;> simp [p, Ne.symm]
 rw [hx]; unfold ear Y snowMark; rw [op_kron_mul,op_kron_mul,mul_one,mul_one] -- placement
lemma over_basis (x:Single n)(k: Single n): (acts (star (ear n).val) (basisKet x)).ofLp k=if x.1.2=k.1.2 ∧ x.2=k.2 then star (frequency k.1.1 x.1.1)/(Lat.normF n) else 0:=by
 obtain ⟨⟨x,i⟩,s⟩:=x; obtain ⟨⟨k,j⟩,v⟩:=k; rw [basis_act,Matrix.star_apply]; unfold ear normF overU Lat.Fourier; simp only [Matrix.kronecker_apply,Matrix.star_apply, Matrix.one_apply, Matrix.of_apply]; by_cases u:i=j <;> by_cases t:s=v <;> simp [u,t,normF] -- extra
lemma windWave (x:Cover)(k:Site n): Lifted.winding n x * star (frequency k (wrap n x))=mode (mel k) (-x):=by
 have ht:=freq_advance k 0 x; have hu:natural (0: Site n)=0:=by ext1 i; simp [natural]
 unfold Rush.wind at ht; rw [hu,zero_add,zero_add,show frequency k (0:Site n)=1 from (by simp [frequency]), one_mul] at ht
 have hx:star (mode (mel k) x)=mode (mel k) (-x):=by nth_rw 1 [←(show star (mel k)=mel k from (mel_h k).1)]; rw [mode_adjoint]
 rw [←hx,←ht,star_mul,fee_real]; unfold Lifted.winding; ring

lemma tagF (k:Behind)(t:ℝ)(j:ℤ)(x:WalkA): mode (tmap (tack k t)) (-tack x j)= spax (-x) k*soundT j t:=by
 unfold mode spax surge soundT
 rw [mul_sum,Complex.exp_sum]; simp only [Axis, Fin.prod_univ_castSucc]
 -- expanded sums maybe fins too much
 simp only [Pi.neg_apply,tmap,tack,Fin.lastCases_last,Fin.lastCases_castSucc, surge]; push_cast; ring_nf -- tune

def shellV (n:Side) (s:SU.Slot)(f:Site n→Ket SpinIdx): Ket (Single n):= WithLp.toLp 2 fun i=> if i.2=s then (Lat.normF n)⁻¹*(f i.1.1).ofLp i.1.2 else 0
lemma shellBound {C:ℝ}(s:SU.Slot) (f:Site n → Ket SpinIdx)(t:0≤C)(p:∀ i,‖f i‖≤C): ‖shellV n s f‖≤ C:=by
 apply (sq_le_sq₀ (norm_nonneg _) t).1; rw [EuclideanSpace.norm_sq_eq]; unfold shellV Single; change ∑ i : (Site n × SpinIdx) × SU.Slot, (‖if i.2=s then _ else 0‖)^2≤ _
 rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
 calc
    _ ≤ ∑ i:Site n, (((n.val:ℝ)^4)⁻¹*C^2):= by
       refine sum_le_sum fun a _=>?_ ; rw [show ∑ j:SpinIdx, _ =((n.val:ℝ)^4)⁻¹*‖f a‖^2 from ?_]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (p a) _) (by positivity)
       rw [EuclideanSpace.norm_sq_eq,mul_sum]; refine sum_congr rfl fun j _=> ?_; rw [Finset.sum_eq_single s]; · simp [normF]; ring
       · intro _ _ p; simp [p]
       simp
    _=C^2:=by rw [sum_const,nsmul_eq_mul,card_univ,site_card]; push_cast; field_simp [nPos n|>.ne']

lemma shell_sub (f g:Site n→Ket SpinIdx)(s:SU.Slot): shellV n s f-shellV n s g=shellV n s (f-g):=by
 apply PiLp.ext; rintro ⟨i,j⟩; by_cases p:j=s <;> simp [p,shellV,mul_sub,WithLp.ofLp_sub]
lemma shell_bands (s:SU.Slot)(f:Site n→Ket SpinIdx) : acts (snowMark n M) (shellV n s f)=shellV n s (fun i=>acts (bar 4 M.val (mel i)) (f i)):=by
 apply PiLp.ext; rintro ⟨⟨i,b⟩,t⟩; unfold snowMark; rw [act_at]; unfold Matrix.mulVec dotProduct Single; rw [Fintype.sum_prod_type,Fintype.sum_prod_type] -- second keeps Slot?
 unfold shellV Rush.mark; simp only [Matrix.kronecker_apply,jump_apply,Equiv.refl_apply,Matrix.one_apply,WithLp.ofLp_toLp, mul_ite,mul_zero,ite_mul, zero_mul]; -- ite
 rw [sum_eq_single i];
 · simp only [ite_true, Finset.sum_ite_eq,pow_one,true_and]; by_cases v:t=s
   · rw [if_pos v]; -- rewrite sums
     rw [act_at]; unfold Matrix.mulVec dotProduct; rw [mul_sum]; apply Finset.sum_congr rfl; intro j _; simp [v]; ring
   rw [if_neg v]; apply sum_eq_zero; intro j _; simp [v]
 · intro j _ p; simp [Ne.symm p]
 simp
end YM.CF.Crest.Sleet
