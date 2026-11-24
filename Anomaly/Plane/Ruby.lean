import YM.Next.FREE_KERNELS.Pulled
import YM.SU5.Circuit.Regale
import YM.Next.MAXWELL.House
import YM.Next.MAXWELL.Pole
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Regis.Circuit.Pier
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open Maxwell Maxwell.Free
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace
-- adapt from positive pigmentS
abbrev e01:PlaqAxes:= ⟨(0, 1),by decide⟩
abbrev e02:PlaqAxes:= ⟨(0, 2),by decide⟩
abbrev e03:PlaqAxes:= ⟨(0, 3),by decide⟩
abbrev e12:PlaqAxes:= ⟨(1, 2),by decide⟩
abbrev e13:PlaqAxes:= ⟨(1, 3),by decide⟩
abbrev e23:PlaqAxes:= ⟨(2, 3),by decide⟩
lemma sixS (i:PlaqAxes): i=e01 ∨ i=e02 ∨ i=e03 ∨ i=e12 ∨ i=e13 ∨ i=e23:=by
 revert i; decide
local notation "X"=> YM.basis 3
lemma poleX:X ≠0:=norm_pos_iff.mp (by rw [basis_norm]; exact one_pos)
abbrev paleN:ℝ:=4*Maxwell.normal
lemma sealN:0<paleN:=mul_pos (by norm_num) Maxwell.normal_pos
set_option maxHeartbeats 1800000 in
lemma rubyLead (i j:PlaqAxes): specter i j X= if i=j then (↑(turned (Signed.mirror 3) i*paleN):ℂ) else 0:=by
 unfold specter; rw [bare_formula _ _ _ _ poleX]; unfold house Maxwell.Free.wedge; dsimp only; rcases sixS i with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases sixS j with rfl|rfl|rfl|rfl|rfl|rfl <;> simp +decide [houseM,kr,e01,e02,e03,e12,e13,e23,turned,Signed.mirror,paleN]
 all_goals ring
abbrev fareX (t:ℝ):ℝ:= t⁻¹^4*paleN
lemma fare_w {t:ℝ}(p:0<t):0<fareX t:=mul_pos (pow_pos (inv_pos.mpr p) _) sealN
lemma gladsome(i j:PlaqAxes)(t:ℝ)(p:0<t): specter i j (t • X)=if i=j then (↑(turned (Signed.mirror 3) i*fareX t):ℂ) else 0:=by
 have he: specter i j (t • X)= t⁻¹^4 • specter i j X:= by unfold specter; rw [(bare_pole ..).degree t p X poleX]; simp [Complex.real_smul]
 rw [he, rubyLead]; split <;> simp only [fareX,Complex.real_smul] <;> push_cast <;> ring
lemma rotated_down(i:PlaqAxes): i.rotate (Signed.mirror 3)=i:=by rcases sixS i with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
lemma original(i:PlaqAxes): turned 1 i=1:=by rcases sixS i with rfl|rfl|rfl|rfl|rfl|rfl <;> simp +decide [turned]
lemma rotated_one(i:PlaqAxes): i.rotate 1=i:=by rcases sixS i with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
end YM.Regis.Circuit.Pier
