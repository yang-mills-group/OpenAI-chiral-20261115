import YM.CF.Tye.Spin
import Verses.Dilation
import YM.SU5.Relativistic.Rebuke
import YM.SU5.Relativistic.Raspa
import YM.CF.Continuum.Extensive
/-! # pinpoint charge. On clean ORBIT. (For unrepaired dirty count by t.) -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Papyrus.Franc
open  Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
open CF.Window Matrix Papyrus.Granat Thera Graph Font
namespace Verses
variable {N:Side}{g:Skye.Seat N→SU.E}
lemma sit_card (G:Finset (Site (More N))) : (univ.filter (fun i:Single N=>node i.1.1∈ G)).card ≤ G.card*180:=by
 let f(i:Single N):=(node i.1.1,i.1.2,i.2)
 let T:=G ×ˢ (univ: Finset (SpinIdx × SU.Slot))
 let S:= univ.filter (fun i:Single N=>node i.1.1∈ G)
 have he:S.image f ⊆ T:= image_subset_iff.mpr (fun i h=> mem_product.mpr ⟨(mem_filter.mp h).2,mem_univ _⟩)
 have hu:Injective f:=fun ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ e=> by obtain ⟨v,h,w⟩ : x=y ∧ i=k ∧ j=l:= ⟨Tenant.needle (congrArg Prod.fst e),congrArg (fun i=> i.2.1) e, congrArg (fun i=> i.2.2) e⟩; rw [v,h,w]
 have hi:= card_le_card he; rw [card_image_of_injective _ hu] at hi
 apply hi.trans (le_of_eq _); rw [show T=G ×ˢ univ from rfl,card_product,card_univ,Fintype.card_prod,SU.slots,show Fintype.card SpinIdx=4 from Fintype.card_fin _]
lemma mint_unit (P:UNI (Single N))(u:Site (More N)→ Site (More N))(h:∀ i j,P.val i j ≠0→ node i.1.1=u (node j.1.1)): condor P.val 180:=by -- vSeat edit
 intro j; let a:=u (node j.1.1); let D:Finset (Site (More N)):= {a}; let S:=univ.filter (fun i:Single N=>node i.1.1 ∈ D )
 have he:(S.card:ℝ)≤180:=by unfold S; exact_mod_cast ((sit_card D).trans (by simp [D]; first | omega | skip))
 have hv: ∑ i:Single N,‖P.val i j‖≤ ∑ _∈S,(1:ℝ):=by
    rw [sum_filter]; apply sum_le_sum; intro i _; split_ifs with hP
    · exact (norm_entry P.val _ _).trans_eq (CStarRing.norm_of_mem_unitary P.property) -- tune trans_eq returns ≤
    exact le_of_eq (by rw [show P.val i j=0 from not_ne_iff.mp (fun e=>hP (Finset.mem_singleton.mpr (h i j e))),norm_zero])
 rw [sum_const,nsmul_eq_mul,mul_one] at hv; exact hv.trans he
lemma uniform_trade (g:Skye.Seat N → SU.E): condor (tradew N g).val 180:= mint_unit (tradew N g) id (fun i j e=>by exact Tye.birth_g i j g e)
lemma preparation_usage (s:Signed): let A:=prepU (Nacre.incX s) (Nacre.spinX s) inert N; condor A.val 180 ∧ condor (star A.val) 180 :=by -- spinx namespace
 intro A; let W:= Nacre.incX s; let f:Equiv.Perm (Site (More N)):=Equiv.ofBijective _ (W.anon_b)
 have h(i j:Single N)(p:A.val i j≠0): f (node i.1.1)=node j.1.1:= Tye.birth_l i j W (Nacre.spinX s) false p
 refine ⟨mint_unit A f.symm (fun i j e=> ?_),mint_unit (star A) f (fun i j e=> ?_)⟩
 · simpa only [Equiv.symm_apply_apply] using congrArg (fun v=> f.symm v) (h i j e)
 exact (h j i (fun v=> e (by change star (A.val j i)=_; rw [v,star_zero]))).symm
lemma twist_budget (i:Signed)(F:Op (Single N)) :entryBudget (twist (prepU (Nacre.incX i) (Nacre.spinX i) inert N) F) ≤ 180*180*entryBudget F:=by
 obtain ⟨p,q⟩:= preparation_usage (N:=N) i
 rw [twist_formula]; refine (condor_right _ _ (by rw [star_star]; exact p)).trans ((mul_le_mul_of_nonneg_left (condor_budget _ _ p) (by norm_num)).trans_eq (by ring))
end Verses
end YM.CF.Papyrus.Franc
