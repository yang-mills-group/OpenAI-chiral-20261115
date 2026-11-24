import YM.SU5.Reconstruction.Moat.Sonic
import YM.SU5.Reconstruction.Anvil.Era
import YM.SU5.Reconstruction.FirstWindows.Grid
import YM.SU5.Reconstruction.Chambers.Strips
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Moat
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup ConePrice
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
open Anvil
open scoped Classical
open Finset
variable (a:Axis)(n:ℕ)
abbrev Desk : Set Axis := {i|i≠a}
abbrev Choir (a:Axis)(n:ℕ) := (i:{i // i≠a})→ Fin n -- numbering
lemma desk_card : Fintype.card {i // i≠a}=3:= by simp [Axis]
lemma choir_card : Fintype.card (Choir a n)=n^3:=by unfold Choir; simp [Fintype.card_fun,desk_card]
variable {Γ:AddSubgroup ℝ}{n a}
def chorale (h:Γ) (i:Choir a n) : Axis→Γ := fun k=> if p:k≠a then (i ⟨k,p⟩).val • h else 0
@[simp] lemma chorale_head (i:Choir a n)(h:Γ): chorale h i a=0:=by simp [chorale]
@[simp] lemma chorale_coe (i: Choir a n)(h:Γ)(k:{i // i≠a}) : ((chorale h i k.val):ℝ)=(i k).val*(h:ℝ):=by simp [chorale,k.property,nsmul_eq_mul] -- nsmul simp maybe
abbrev account (a:Axis)(x:Axis→Γ):=rimPay a (fun i=>(x i:ℝ))
private lemma coordinate_bill (i:Choir a n)(h:Γ)(p:0≤(h:ℝ))(k:{i // i≠a}):0 ≤ ((chorale h i k.val):ℝ) ∧ ((chorale h i k.val):ℝ) ≤ n * (h:ℝ):=by rw [chorale_coe]; exact ⟨by positivity,mul_le_mul_of_nonneg_right (by exact_mod_cast (i k).isLt.le) p⟩
lemma balanced (i:Choir a n)(h:Γ)(p:0≤ (h:ℝ)) : ‖account a (chorale h i)‖≤ 2*(n*(h:ℝ)):=by
 apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
 rw [Anvil.rimPay_norm]; calc
    _ ≤ ∑ _∈ Finset.univ.erase a,(n*(h:ℝ))^2:= Finset.sum_le_sum fun k t=> (pow_le_pow_left₀ (coordinate_bill i h p ⟨k,ne_of_mem_erase t⟩).1 (coordinate_bill i h p ⟨k,ne_of_mem_erase t⟩).2 2)
    _ ≤ _:= by rw [sum_const, card_erase_of_mem (mem_univ _), card_univ]; simp [Axis]; nlinarith only [sq_nonneg (n*(h:ℝ))] -- tune pushes
lemma interval (i j:Choir a n)(h:Γ)(p:0≤(h:ℝ))(t:i≠j) : ∃ k:Axis,k≠ a ∧ ((chorale h j k:ℝ)+h ≤ (chorale h i k:ℝ) ∨ (chorale h i k:ℝ)+h ≤ (chorale h j k:ℝ)):=by
 obtain ⟨k,d⟩:= Function.ne_iff.mp t
 have v:(i k).val ≠ (j k).val:= fun e=>d (Fin.ext e)
 refine ⟨k,k.property,?_⟩; rw [chorale_coe, chorale_coe]
 rcases lt_or_gt_of_ne v with q|q -- search
 · right; have he :(i k).val+1 ≤ (j k).val:=q; have hb:((i k).val:ℝ)+1 ≤ (j k).val:=by exact_mod_cast he
   simpa [add_mul] using (mul_le_mul_of_nonneg_right hb p)
 left; have he :(j k).val+1 ≤ (i k).val:=q; have hb:((j k).val:ℝ)+1≤(i k).val:=by exact_mod_cast he
 simpa [add_mul] using mul_le_mul_of_nonneg_right hb p
end YM.Moat
