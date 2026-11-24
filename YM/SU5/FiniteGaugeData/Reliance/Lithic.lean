import YM.SU5.FiniteGaugeData.Concord.Aligned
import YM.CF.Continuum.PayTax
/-! # A localized exponential cost (real gauge, shared Pane)

Use magnitude exponent of face curvature of the FIRST link argument, retaining both links
in the norm comparison. The comparison is on all Fields, if the weight involves a generated
probe it doesn't imply that the probe has this whole stencil support (the weight is allowed
to name slightly surrounding faces). At support S, sum over local anchor sites. Split total
face charge up exactly across base sites and orientations, in order to allow doubling at ANY
sufficiently supported alignments, no divisibility of the course. Also use this to price rare
local curvature events. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Reliance
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal Classical
attribute [local instance] opCStarAlgebra
variable {m:Side}(x : Site m) (r:ℝ)

-- real face * r (inverse temp scaling from elected data later). No exponent of number of all sites on the RHS of growth pledge.
def lobe (r:ℝ)(p:Face (Per m))(U:Config SU.group m):ℝ:= r*SU.group.chord (faceValue U p)
private def snail (s:Signed): Config SU.group m→ℝ:= fun U=>∑ i:PlaqAxes, lobe r (0,i) (Lattice.pull s x U)

def signs : ℝ:= Fintype.card Signed
lemma signs_pos : 0< signs:= by unfold signs; positivity

def glow (r:ℝ)(S:Support m)(U:Config SU.group m):= signs⁻¹ * ∑ x∈S,∑ s:Signed,snail x r s U
local notation "xC"=> Config SU.group m
lemma lobe_n (p:0 ≤ r)(U:Config SU.group m)(x:Face (Per m)): 0 ≤ lobe r x U:= mul_nonneg p (SU.group.chord_nonneg _)
private lemma swing (f:Face (Per m))(s:Signed)(U:xC): lobe r f (Lattice.pull s x U)= lobe r (Face.send s x f) U:=by unfold lobe; exact congrArg (r*·) (Face.send_price U f s x SU.group.chord SU.group.chord_inv (fun _ u => SU.group.chord_conj u _))

lemma glow_n (p:0 ≤ r)(S:Support m)(U:xC): 0 ≤ glow r S U := mul_nonneg (inv_nonneg.mpr signs_pos.le) (sum_nonneg fun i _=> sum_nonneg fun j _=> sum_nonneg (fun k _=> lobe_n r p _ _)) -- ` ..` syntax fix
lemma glow_grows (p:0≤r) {S T:Support m} (t:S⊆T)(U:xC): glow r S U ≤ glow r T U:=
 mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg t (fun i _ _=> sum_nonneg (fun j _=>sum_nonneg (fun k _=>lobe_n r p _ _)))) (inv_nonneg.mpr signs_pos.le)
lemma fill_till (S:Support m)(U:xC)(v:ℝ)(p:0≤r)(u:r≤v): glow r S U ≤ glow v S U:= by
 refine mul_le_mul_of_nonneg_left (sum_le_sum (fun x _=> sum_le_sum (fun s _=>?_))) (inv_nonneg.mpr signs_pos.le)
 exact sum_le_sum fun i _=> mul_le_mul_of_nonneg_right u (SU.group.chord_nonneg _)

private lemma origin (i:PlaqAxes) (U:xC): faceValue (Lattice.pull 1 x U) (0,i)= faceValue U (x,i):=by
 unfold faceValue; rw [travel_pull]; simp [affine,square]
private def rotates (s:Signed): Equiv.Perm (Site m):= ⟨s.act,s⁻¹.act, fun _=>s.inv_act _,fun x=>by simpa using (s⁻¹).inv_act x⟩
private lemma totals (s:Signed)(U:xC): (∑ x:Site m, snail x r s U)=∑ x:Face (Per m),lobe r x U:=by
 have he(x:Site m):snail (s.act x) r s U=∑ i:PlaqAxes,lobe r (x,i) (Lattice.pull s 0 U):= by
    unfold snail; rw [show Lattice.pull s (s.act x) U=Lattice.pull 1 x (Lattice.pull s 0 U) from by rw [Lattice.pull_pull,mul_one]; simp only [affine,add_zero]]
    refine sum_congr rfl fun i _=>?_ ; unfold lobe; rw [origin]
 calc
   _ = ∑ x:Site m,snail ((rotates s) x) r s U := (Equiv.sum_comp (rotates s) (fun x=>snail x r s U)).symm
   _ = ∑ x:Face (Per m),lobe r x (Lattice.pull s 0 U):=by
       change (∑ x:Site m,snail (s.act x) r s U)=∑ x: Site m × PlaqAxes, _; rw [Fintype.sum_prod_type]; simp_rw [he]
   _ = _ := by
       let Y:Equiv.Perm (Face (Per m)):= Equiv.ofBijective (Face.send s 0) ⟨Face.injective_send s 0,Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩
       simp_rw [swing]
       exact Equiv.sum_comp Y (fun p=>lobe r p U)

-- all faces once
lemma glows (U:xC) : glow r univ U=∑ x:Face (Per m), lobe r x U := by
 unfold glow; rw [Finset.sum_comm]; simp_rw [totals]; rw [sum_const,card_univ,nsmul_eq_mul]; exact inv_mul_cancel_left₀ signs_pos.ne' _

lemma reflect_till (S:Support m)(s:Signed)(y:Site m)(U:xC): glow r S (Lattice.pull s y U)=glow r (S.image (affine s y)) U := by
 have he(x:Site m) : (∑ t:Signed,snail x r t (Lattice.pull s y U))=(∑ t:Signed,snail (affine s y x) r t U):=by
   have p(t:Signed):snail x r t (Lattice.pull s y U)=snail (affine s y x) r (s*t) U:=by unfold snail; rw [Lattice.pull_pull] -- pattern inside ∑
   simp_rw [p]; exact Equiv.sum_comp (Equiv.mulLeft s) (fun t=> snail _ _ t U)
 unfold glow; rw [sum_image]; simp_rw [he]; intro i _ j _ e; exact (rotates (m:=m) s).injective (add_right_cancel e)

lemma proper_chord (U:SU.group.El): SU.group.chord U ≤ 2:=by nlinarith [SU.group.chord_nonneg U,SU.group.chord_price U, (SU.group.price_range U).2]
def posted (k:ℕ):ℝ:= r*2*(Fintype.card PlaqAxes)*k
lemma glow_cap (p:0≤r)(U:xC)(S:Support m)(k:ℕ)(v:S.card ≤ k): glow r S U ≤ posted r k:=by
 let c:= (Fintype.card PlaqAxes:ℝ); let K:= (Fintype.card Signed:ℝ); have hc:0≤c:=Nat.cast_nonneg _; have ht:0<K:= signs_pos
 unfold glow; apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=>sum_le_sum (fun s _=>sum_le_sum (fun j _=> mul_le_mul_of_nonneg_left (proper_chord _) p)))) (inv_nonneg.mpr signs_pos.le)); simp_rw [sum_const,card_univ,nsmul_eq_mul]
 change K⁻¹*((S.card:ℝ)*(K*(c*(r*2)))) ≤ _; calc
   _ = r*2*c*S.card:=by field_simp
   _ ≤ _:= mul_le_mul_of_nonneg_left (Nat.cast_le.mpr v) (by positivity)

lemma lobe_paid (f:Face (Per m))(U:xC)(S:Support m)(h:0 ≤ r)(t:f.1∈S) : signs⁻¹*lobe r f U ≤ glow r S U:=by
 apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr signs_pos.le)
 have hp (p : Support m):= glow_n r h p U
 have hSn(x:Site m)(i:Signed):0 ≤ snail x r i U:= sum_nonneg fun j _=> lobe_n r h _ _
 apply le_trans ?_ (single_le_sum (f:=fun x=>∑ s:Signed, snail x r s U) (fun i _=> sum_nonneg (fun j _=> hSn i j)) t)
 apply le_trans ?_ (single_le_sum (f:=fun s=> snail f.1 r s U) (fun i _=> hSn f.1 i) (mem_univ (1:Signed)))
 rcases f with ⟨y,i⟩; apply le_trans ?_ (single_le_sum (f:=fun i=>lobe r (0,i) (Lattice.pull 1 y U)) (fun j _=>lobe_n r h _ _) (mem_univ i)); unfold lobe; rw [origin]
lemma glow_plus {S T:Support m}(h:Disjoint S T)(U:xC): glow r (S∪T) U= glow r S U + glow r T U:=by unfold glow; rw [Finset.sum_union h, mul_add]
end YM.CF.Buffered.Reliance
#print axioms YM.CF.Buffered.Reliance.glows
#print axioms YM.CF.Buffered.Reliance.reflect_till
#print axioms YM.CF.Buffered.Reliance.glow_cap
