import YM.SU5.May.TorqueCloth
/-! Torque gains. actual Petri telescope L^-1/2 EXP, no link hypotheses! -/
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Stent.Purchase
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Pointwise Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Kronecker ENNReal
attribute [local instance] opCStarAlgebra
variable (R:Patch)
set_option quotPrecheck false
local notation "Λ"=> R.L
local notation "J"=> R.J
open Cube Stencil Tenant Tap Tulip Branch Spire Peaks Advance Skye Lifted CF.Stent
variable {x:Cover}
open NormedSpace
variable {N: Side}{b:Bool}{F:Op SU.Slot}
local notation "Ω"=> Op SU.Slot
variable {ι κ ν:Type*}[LinearOrder κ] [Fintype κ] [LinearOrder ι][Fintype ι][LinearOrder ν][Fintype ν]
open SU
variable {P:Side}(G:Ratio N P) (p:G.count=R.L) (u:Nom N P) {d:ℕ} (w:LaurentRadius R.J G.count d)
-- critical! path depends on BOTH k indices; we only care spine column at t=(0,η)
local notation "tok[" p "," r "," i "," v "]" => ((p,(r,i)),v)
-- finite bounds, no dependencies on Male m (beyond the receipts used). Eu ℓ² projection.
def tariffP (r:Site G.count) (A:Op (Iota G)) : Op (Single N):= Matrix.of fun i j=> A (tok[i.1.1,r,i.1.2,i.2]) (patchQ G j)
def curve (r:Site G.count)(z:Cover)(o:Lattice.Order): Op (Single N):= jump ((Equiv.addRight (wrap N z)).prodCongr (Equiv.refl _)) fun i=> (wind i.1 z) • (matter (guardU G u r z o i.1 i.2)).val
lemma curve_unit (r:Site G.count)(z:Cover)(o:Lattice.Order): ‖curve G u r z o‖ ≤ 1:=by
 unfold curve; apply jump_bound _ _ zero_le_one; intro i; rw [norm_smul,show ‖wind i.1 z‖=1 from fee_norm _, CStarRing.norm_of_mem_unitary (matter _).property]; exact le_of_eq (one_mul _)
include w p
variable (m:Male)(r:Site G.count)
noncomputable abbrev scaleT (s:Side) := ((s.val:ℝ)^2)⁻¹ * (Real.sqrt s.val)⁻¹
lemma adjustedT : ∑ i∈ LabelSet d, ‖cash R (lift r) i‖= scaleT G.count:=by revert r; rw [p]; intro t; exact Wallet.cash_weight R (p ▸ w) t
local notation "K" => Fintype.card Lattice.Order
local notation "q" => (K:ℝ)⁻¹
local notation "Σ"=> Peaks.cloth R.J m G (unionP u)
lemma crypto : tariffP G r Σ=q • ∑ o:Lattice.Order,∑ z∈LabelSet d, (cash R (lift r) z) • curve G u r z o:=by
 ext ⟨⟨x,i⟩,a⟩ ⟨⟨y,j⟩,b⟩; rw [tariffP,Matrix.of_apply,margin R G p u w,amount R G p u w,Matrix.smul_apply,Matrix.sum_apply]; apply congrArg
 simp_rw [Matrix.sum_apply]; refine sum_congr rfl fun i' _=> sum_congr rfl fun z _ =>?_ ; rw [curve,Matrix.smul_apply,jump_apply]; simp only [Matrix.smul_apply,smul_eq_mul,Equiv.prodCongr_apply, mul_ite,mul_zero]
 by_cases e:i=j <;> by_cases h:y=x+wrap N z<;> simp_all [eq_comm, mul_assoc,mul_left_comm] -- tune
lemma tariffP_norm : ‖tariffP G r Σ‖ ≤ scaleT G.count := by
 have he : 0< (Fintype.card Lattice.Order:ℝ) := by positivity
 rw [crypto R G p u w m r, norm_smul, Real.norm_of_nonneg (inv_pos.mpr he).le]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_pos.mpr he).le)
 refine (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=> scaleT G.count) fun i _=> (norm_sum_le ..).trans ?_) (inv_pos.mpr he).le).trans_eq ?_
 · rw [←adjustedT R G p w r]; exact sum_le_sum fun z _=>by rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (curve_unit G u r z i)
 simp only [sum_const,card_univ,nsmul_eq_mul]; rw [←mul_assoc,inv_mul_cancel₀ he.ne',one_mul]
omit p w
noncomputable def radialCut (r:Site G.count)(X: Ket (Iota G)) : Ket (Single N):= WithLp.toLp 2 (fun i=> X (tok[i.1.1,r,i.1.2,i.2]))
set_option maxHeartbeats 650000 in
lemma profit (x:Ket (Single N)) (A:Op (Iota G)): radialCut G r (acts A (coat (patchQ G) x))=acts (tariffP G r A) x:=by
 apply PiLp.ext; rintro ⟨⟨t,i⟩,b⟩
 change (acts A (coat (patchQ G) x)).ofLp (tok[t,r,i,b])=(acts (tariffP G r A) x).ofLp ((t,i),b); nth_rw 1 2 [← basis_expand x]; simp_rw [map_sum,map_smul,basis_shell, WithLp.ofLp_sum,Finset.sum_apply, WithLp.ofLp_smul,Pi.smul_apply,basis_act]; rfl
private def isob : Site G.count × Single N ≃ Iota G :=
 ⟨fun x=> tok[x.2.1.1,x.1,x.2.1.2,x.2.2],fun x=>(x.1.2.1,(x.1.1,x.1.2.2),x.2),fun _=>rfl,fun _=>rfl⟩
lemma overview (X:Ket (Iota G)): ‖X‖^2=∑ r:Site G.count,‖radialCut G r X‖^2:=by
 simp_rw [EuclideanSpace.norm_sq_eq]; rw [← Equiv.sum_comp (isob G), Fintype.sum_prod_type]; rfl
include p w
lemma boundPose(v:Ket (Single N)): ‖acts Σ (coat (patchQ G) v)‖ ≤ (Real.sqrt (G.count.val:ℝ))⁻¹ * ‖v‖:=by
 let s:=scaleT G.count; apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
 rw [overview G]; simp_rw [profit G]
 apply le_trans (sum_le_sum (g:=fun _=>(s*‖v‖)^2) fun i _=> pow_le_pow_left₀ (norm_nonneg _) ((Flare.opy (tariffP G i Σ) v).trans (mul_le_mul_of_nonneg_right (tariffP_norm R G p u w ..) (norm_nonneg _))) _); apply le_of_eq
 unfold s scaleT; simp only [sum_const,card_univ,site_card,nsmul_eq_mul] -- tune
 have he:(G.count.val:ℝ)≠0:=by positivity
 push_cast; field_simp -- maybe lack sqrt lemma
lemma byMode_bill (b:Bool)(F:Op SU.Slot)(x:Ket (Single N)) :‖byMode G R.J F m u b x‖ ≤ (Real.sqrt G.count.val)⁻¹* (Real.exp (lockPrice*‖F‖)*‖x‖):= by
 unfold byMode; simp only [LinearMap.comp_apply]; let y : Ket (Iota G):= acts Σ (coat (patchQ G) (acts (feeL b N F) x))
 change ‖trailK (switchG G).symm.toEmbedding y‖ ≤ _; rw [show ‖trailK (switchG G).symm.toEmbedding y‖ = ‖y‖ from ?_]; · exact (boundPose R G p u w m _).trans (mul_le_mul_of_nonneg_left (fee_price x) (by positivity))
 apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp; rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,←Equiv.sum_comp (switchG G)]; refine sum_congr rfl fun j _=>?_ ; rw [seamK, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
#print axioms byMode_bill
end YM.CF.Buffered.Stent.Purchase
