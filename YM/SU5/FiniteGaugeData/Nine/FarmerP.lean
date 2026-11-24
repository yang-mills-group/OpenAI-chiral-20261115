import YM.SU5.FiniteGaugeData.Nine.Tundra
import YM.SU5.FiniteGaugeData.Brique.Etude
set_option autoImplicit false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Window.Pivot
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Tenant Fock Tulip Dial Fir Ember Buffered Skye Scree Nacre
attribute [local instance] opCStarAlgebra
variable {N:Side}(o:Cover)
open Brique Mir Phase RP Largo Spire
local notation "Μ"=> Single N
local notation "G"=> prepU (incX 1) ChiT inert N
local notation "C"=> (0: SpinIdx)
local notation "D"=> (3: SpinIdx)
private lemma inc_fee (x:Site N): (incX 1).payA x=1:=by
 have h:= prep_one N; let i:SpinIdx:=0; let j:=Classical.arbitrary SU.Slot; have hv:(prepU (incX 1) 1 inert N).val ((x,i),j) ((x,i),j)=1:=by rw [h]; exact Matrix.one_apply_eq ..
 change jump (Tofu (incX 1) N) (fun i=> (milU (incX 1) (1:UNI SpinIdx) inert i).val) _ _=1 at hv; rw [jump_apply] at hv; split at hv; next p=>
    change (incX 1).payA x *(1 ⊗ₖ (1:Op SU.Slot)) (i,j) (i,j)=1 at hv; simpa using hv
 next p=> exact (zero_ne_one hv).elim
lemma flairG : (prepU (incX 1) ChiT inert N).val= plates N (fun _=> ChiT.val) ⊗ₖ (1:Op SU.Slot):=by
 ext ⟨⟨x,i⟩,j⟩ ⟨⟨y,w⟩,u⟩; rw [pilesV]; change jump (Tofu (incX 1) N) (fun i=> (milU (incX 1) ChiT inert i).val) (x,(i,j)) (y,(w,u))= jump (Equiv.refl (Site N)) (fun _=> ChiT.val) (x,i) (y,w)*(1:Op SU.Slot) j u
 rw [jump_apply,jump_apply, show Tofu (incX 1) N x=x from (by change Shape.mills (lagX 0) N x=x; rw [lag_i,map_zero,add_zero])]; by_cases h:x=y <;> simp only [Equiv.refl_apply,h,↓reduceIte]; change (incX 1).payA _ • (ChiT.val ⊗ₖ (1:Op SU.Slot)) (i,j) (w,u)=_; rw [inc_fee,one_smul]; rfl; exact (zero_mul ..).symm -- tune
abbrev loci (N:Side)(s:Finset SpinIdx)(t:Finset SU.Slot): Finset (Single N):=(univ ×ˢ s) ×ˢ t
abbrev Θ (N:Side)(i:SpinIdx)(c:SU.Slot): Finset (Single N):= loci N {i} {c}
lemma cut_expand (s:Finset SpinIdx)(t:Finset SU.Slot) : cutM (loci N s t)=plates N (fun _=>cutM s)⊗ₖ cutM t :=by
 rw [pilesV]; ext ⟨⟨x,i⟩,j⟩ ⟨⟨y,w⟩,u⟩
 by_cases h:x=y <;> by_cases p:i=w<;>by_cases t':j=u <;>simp_all [cutM,Matrix.diagonal_apply,jump_apply,loci]<;> repeat' split <;> simp_all
 all_goals tauto
-- preserve.Pay formulas. Need zero at other spins.
lemma shell_slot : (Tset N)ᶜ= loci N plusHalfᶜ univ :=by ext ⟨⟨x,i⟩,j⟩; simp only [Finset.mem_compl,grade_one,loci,mem_product,mem_univ,and_true,true_and]
private lemma frank : cutM (Finset.univ : Finset SU.Slot)=(1:Op SU.Slot):=by ext i j; by_cases h:i=j <;> simp [h,cutM,Matrix.one_apply]
variable (k:ℕ)(M: Male)
abbrev PeakP (N:Side):= funde k M N 1
abbrev toolP (N:Side):= 1-funde k M N 1
local notation "Z"=> bar k M.val
local notation "Y"=> toolP k M N
variable (p:1 ≤ k)
include p
lemma PeakP_flat : funde k M N 1= plates N Z ⊗ₖ (1:Op SU.Slot):=by rw [funde_flat k p, show cart N (tub (bar k M.val)) = plates N (bar k M.val) from cart_traded (A:=Z) (cBar k M.val true p M.property) N]
lemma PeakP_comp : toolP k M N = plates N (fun x=>1-(Z x)) ⊗ₖ (1:Op SU.Slot):=by rw [toolP,PeakP_flat k M p, ← pilesM (g:=Z) (f:=fun _=>1), piles1]; simp only [sub_eq_add_neg, Matrix.add_kronecker,Matrix.one_kronecker_one,op_kron_neg] -- maybe name.
lemma PeakP_pro : IsStarProjection (funde k M N 1):= by
 rw [PeakP_flat k M p]; have he(i:Momentum)(v:i∈realCube zone)(w:i≠0):= bar_frames k M.val v w M.property; constructor
 · unfold IsIdempotentElem; rw [op_kron_mul,pilesP,mul_one]; rw [pilesE (fun i=>bar k M.val i*bar k M.val i) _ (fun i v w=> (he i v w).1)] -- type function metavariable
 unfold IsSelfAdjoint; rw [op_star_kron,star_one,pilesS]; rw [pilesE (fun i=>star (bar k M.val i)) _ (fun i v w=> (he i v w).2)]
lemma poles (t:Aptitude k N): piQu o N (toolP k M N)= plates N (fun x=> twist ChiT (Z x)) ⊗ₖ (1:Op SU.Slot):=by
 rw [show piQu _ _ _= twist (G) (funde k M N 1) from parity_edge o k M t,PeakP_flat k M p, twist_formula,flairG,op_star_kron,star_one,op_kron_mul, op_kron_mul,one_mul,one_mul, pilesP,pilesS,pilesP]; simp only [twist_formula]
omit p in
lemma pNeg (h:Momentum→Op SpinIdx): -plates N h= plates N (fun x=>-(h x)):=by
 have ht: plates N (fun _=>(0:Op SpinIdx))=0:=by rw [←sub_self (plates N (fun _=> (1:Op SpinIdx))),pilesM]; simp
 rw [←zero_sub,← ht,pilesM]; simp
lemma low_sweep (t:Aptitude k N)(g:SU.Slot) : cutM (Θ N D g)*(Y)*cutM (Θ N D g)= cutM (Tset N)ᶜ*(Y)*cutM (Θ N D g) := by
 have hp(x): cutM {D}*(1-Z x)*cutM {D}=shell k M.val x • cutM {D}:=by
    let V:=cutM {D}; let W:=cutM plusHalfᶜ; have hx:V*W=V:=by unfold V W; rw [Fock.Brique.cut_meet,inter_eq_left.mpr (by decide : ({D}:Finset SpinIdx)⊆ plusHalfᶜ)]
    have he:= low_formula (skin k M.val x) (shell k M.val x); rw [←bar_look] at he; change V*_ *V = _ • V; nth_rw 1 [← hx]; rw [mul_assoc V W, mul_assoc V, (show W*_ * V=_ from he), Algebra.mul_smul_comm, show V*V=V from (cutM_idp _).1]
 let U:=fun x=>cutM plusHalfᶜ*(1-(Z x))*cutM {D}; have he:plates N (fun x=> cutM {D}*(1-(Z x))* cutM {D})=plates N U:= pilesE _ _ fun x p u=> by rw [hp]; unfold U; rw [bar_look]; exact (low_formula ..).symm
 rw [PeakP_comp k M p,Θ,cut_expand,shell_slot,cut_expand,frank]; simp only [op_kron_mul,one_mul,mul_one,pilesP]; rw [show cutM {g} * cutM {g}= _ from ((cutM_idp {g}).1 : _ =_), he]
lemma low_agree (t:Aptitude k N)(g:SU.Slot) : cutM (Tset N)ᶜ*(Y)*cutM (Θ N D g)=cutM (Tset N)ᶜ*(piQu o N (Y))*cutM (Θ N D g):=by
 rw [poles o k M p t,PeakP_comp k M p,Θ,cut_expand,shell_slot,cut_expand]; simp only [op_kron_mul,pilesP]
 let U:=fun x=>cutM plusHalfᶜ*(1-Z x)*cutM {D}; have he: plates N U = plates N (fun x=>cutM plusHalfᶜ*(twist ChiT (Z x))*cutM {D}):= pilesE _ _ (fun x z t=> by unfold U; rw [bar_look,low_formula,low_formulaP])
 rw [show plates N (fun p=> _ *(1-Z p)* _)=_ from he] -- pragma notation
lemma tap_agree(t:Aptitude k N)(g:SU.Slot): cutM (Θ N C g)*(Y)*cutM (Θ N D g)= -(cutM (Θ N C g)*(piQu o N (Y))*cutM (Θ N D g)):=by
 let U:=fun x=>cutM {C}*(1-Z x)*cutM {D}; let Vx:=fun x=>cutM {C}*twist ChiT (Z x)*cutM {D}; have he: plates N U= -plates N Vx:=by
    rw [pNeg]; apply pilesE; intro x b u; unfold U Vx; rw [bar_look]; exact mid_formulaP ..
 rw [poles o k M p t,PeakP_comp k M p]; simp only [Θ,cut_expand,op_kron_mul,pilesP,←op_kron_neg]; rw [show plates N (fun p=> _ *(1-Z p)* _)=_ from he]
#print axioms low_sweep
section size
variable (g:SU.Slot)
abbrev preF(N:Side)(g:SU.Slot):= toolP k M N*cutM (Θ N D g) *toolP k M N
omit p in
private lemma fourier_p(x k:Site N): Fourier N x k * star (Fourier N x k)= ((N.val:ℂ)^4)⁻¹:=by
 unfold Fourier; simp only [Matrix.of_apply,star_div₀]; rw [div_mul_div_comm, mul_comm (frequency k x),frequency_unit]; unfold normF; simp only [star_pow,star_natCast,one_div]; ring
-- correct weight
lemma formulaF : preF k M N g= plates N (fun x=> (1-bar k M.val x)*cutM {D}*(1-bar k M.val x)) ⊗ₖ cutM {g}:= by rw [preF,PeakP_comp k M p, Θ, cut_expand,op_kron_mul,op_kron_mul, one_mul,mul_one,pilesP,pilesP]
lemma formula_α (s:Site N)(i j:SpinIdx): preF k M N g ((s,i),g) ((s,j),g)= ((↑N.val:ℂ)^4)⁻¹ * ∑ v:Site N,(((1-bar k M.val (mel v))*cutM {D}*(1-bar k M.val (mel v))) i j):= by
 rw [formulaF k M p]; let P(x):= (1-bar k M.val x)*cutM {D}*(1-bar k M.val x); change plates N P (s,i) (s,j)*cutM {g} g g =_; rw [show cutM {g} g g=1 from (by simp [cutM]),mul_one,Rush.price,mul_sum]; exact sum_congr rfl (fun v _=>by rw [mul_right_comm (Fourier _ _ _),fourier_p])
lemma staple (s:Site N): preF k M N g ((s,C),g) ((s,C),g)= rubra k N M:=by
 have hz:= same_twice k M N; rw [formula_α k M p]; simp_rw [left_norm,←eta_v]; simp only [←Complex.ofReal_pow,←Complex.ofReal_add,←Complex.ofReal_sum]; unfold rubra; rw [←hz]; push_cast; ring_nf -- zpow
lemma stapleB (s:Site N):preF k M N g ((s,D),g) ((s,D),g)=villa k N M:=by rw [formula_α k M p]; simp_rw [bottom_norm,pilot_add]; unfold villa; push_cast; ring
lemma stapleC (s:Site N):preF k M N g ((s,C),g) ((s,D),g)=0:=by rw [formula_α k M p,dawn_cross,mul_zero]
lemma tool_proj : IsStarProjection (Y):= (PeakP_pro k M p).one_sub
lemma preF_star : star (preF k M N g)=preF k M N g:=by simp only [preF,star_mul,(show star (Y)=(Y) from (tool_proj k M p).2.star_eq),(cutM_idp _).2.star_eq]; exact (mul_assoc ..).symm
lemma stapleE(s:Site N): preF k M N g ((s,D),g) ((s,C),g)=0:=by rw [←preF_star k M p g,Matrix.star_apply,stapleC k M p,star_zero] -- order p g?
#print axioms staple
end size
end YM.CF.Window.Pivot
