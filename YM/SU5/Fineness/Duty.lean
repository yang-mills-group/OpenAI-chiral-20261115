import YM.SU5.Fineness.Spokes
/-! # Gaussian torsion at a fitted step. Exact, *every* tag.
    Given real counting Budget of Bed metrics H and tree retention. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.Fineness
open Function Lattice RG Matrix Exterior Precision Tree Finset
open scoped Topology Matrix BigOperators Kronecker
variable {f c n:Side}(S:StepData c f)(F:Forest S.ratio)
local notation "r"=> S.ratio
local notation "βW" => branchesZ S.ratio F ℝ
local notation "P"=> S.kernel.penalty
local notation "q"=> probe S
open FreeResolvent (treeMatrix baseMatrix FaceRow)
section
lemma stem_rep {g: Ratio c f} (F:Forest g) : branchesZ g F ℝ=FreeResolvent.insertion (turnBond f ∘ fun i:F.Free=>i.val):=by ext i j; simp [branchesZ,FreeResolvent.insertion,eq_comm]
lemma rpos : 0 < (S.patch.L.val:ℝ):=by positivity
abbrev realBlock (H : Sheet (Body 2 f)) := K H+ (probe S)ᵀ*(P • (1:Sheet (Body 1 c)))*probe S
def inBoard (H:Sheet (Body 2 f)): Sheet F.Free:= (branchesZ (r) F ℝ)ᵀ* realBlock S H*βW
lemma footmark (H:FaceRow): realBlock S (H.acts f)=baseMatrix S H:=by unfold baseMatrix realBlock; rw [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
lemma tree_eq (G:Gauge) (H:FaceRow) : treeMatrix G S F H= (inBoard S F (H.acts f)) ⊗ₖ (1:Sheet G.ColorIndex) := by
 unfold treeMatrix FreeResolvent.fullMatrix inBoard; rw [footmark,stem_rep, FreeResolvent.insertion.compress]
 ext ⟨x,i⟩ ⟨y,j⟩; change (if i=j then _ else 0) = _; rw [Matrix.kronecker_apply]; by_cases g:i=j <;> simp [g,one_apply]; rfl
lemma scalar_gap (G:Gauge)[Nonempty G.ColorIndex] (H:FaceRow){a:ℝ}(h:FreeResolvent.Gap (treeMatrix G S F H) a): FreeResolvent.Gap (inBoard S F (H.acts f)) a:=by
 classical
 let i:G.ColorIndex:= Classical.arbitrary _; let w(x:F.Free):FreeResolvent.Active G F:= (x,i)
 have he:(treeMatrix G S F H).submatrix w w = inBoard S F (H.acts f):=by rw [tree_eq]; ext x y; simp [w]
 exact he ▸ h.submatrix w (fun x y h=> congrArg Prod.fst h)
lemma board_symm (H: Sheet (Body 2 f))(h:Hᵀ=H) : (inBoard S F H)ᵀ = inBoard S F H:=by
 let H':= realBlock S H; have hp:H'ᵀ=H':=by unfold H' realBlock; rw [transpose_add, (lattice_null H h).symmA,transpose_mul,transpose_mul,transpose_smul,transpose_transpose,transpose_one,Matrix.mul_assoc _ (P • 1)]
 unfold inBoard; rw [transpose_mul,transpose_mul,transpose_transpose,hp]; simp only [Matrix.mul_assoc]; rfl
lemma tree_det (G:Gauge)(H:FaceRow) : (treeMatrix G S F H).det=(inBoard S F (H.acts f)).det^(Fintype.card G.ColorIndex):=by rw [tree_eq, det_kronecker]; simp
end
abbrev leasePart (H:Sheet (Body 2 n)):= torsion (Precision.K H) (sightZero n)
private lemma arbor (W : Tab (Body 1 f) (Body 1 c)) : ∃ T : Tab F.Free (Body 1 c), branchesZ (r) F ℝ*T=extracted S F W:=by
 let U:= extracted S F W
 let t: F.Free→ Body 1 f:=turnBond f ∘ fun i=> i.val
 let X:= U.submatrix t id
 refine ⟨X,?_⟩; ext i j
 obtain ⟨⟨x,k⟩,rfl⟩:= (turnBond f).surjective i
 let y0:Edge (Site f):=(x,k); by_cases h:y0∈F.trunks
 · have hu: U (x,coord k) j=0:=by
      have hv : marked (S:=S) F (U *ᵥ Pi.single j (1:ℝ)):=stays F W _; simpa [Matrix.mulVec, dotProduct_single,y0] using hv y0 h
   change (∑ i, branchesZ (r) F ℝ (turnBond f y0) i*X i j) = U (x,coord k) j; rw [hu]; apply sum_eq_zero; intro i g; simp only [branchesZ,Matrix.of_apply,EmbeddingLike.apply_eq_iff_eq,ite_mul,zero_mul,one_mul]; rw [if_neg]; rintro v; apply i.property; rw [←v]; exact h
 let z:F.Free:=⟨y0,h⟩; change (∑ i, branchesZ (r) F ℝ (turnBond f z.val) i*X i j)=X z j; simp [branchesZ,Subtype.coe_inj]
/-- Exact classical factor accounting. -/
theorem hinges (W : Tab (Body 1 f) (Body 1 c)) (H : Sheet (Body 2 f))(Kc : Sheet (Body 2 c)) (h : Inputs S W H Kc)(u:Hᵀ=H)(t:Kcᵀ=Kc)(v:IsUnit (inBoard S F H)) :
    (S.patch.L.val:ℝ)^8*leasePart H * (S.kernel.penalty^(Fintype.card (Body 1 c)))=(inBoard S F H).det*leasePart Kc:=by
 let Hp:= leasePart H; let A:=Precision.K Kc; let T:=inBoard S F H; let R:=βW; let Z:= -(Rᵀ* (probe S)ᵀ * (P • (1:Sheet (Body 1 c))))
 let L:= S.patch.L; let w:= tagsZ (r) ℝ
 let Q:= probe S; let G:= allocation (r)
 let e :=(Equiv.sumAssoc ..).symm.trans (Equiv.sumCongr (footCount r) (Equiv.refl Axis)); obtain ⟨X,hX⟩:= (lattice_null H u).page e; rw [← spokes r] at X hX
 obtain ⟨⟨U',g⟩,p⟩:= bolt_split (r) F; obtain ⟨T',e⟩:=arbor S F W; obtain ⟨Xc,Hc⟩:= Precision.stationed F W H Kc h;
 let E:= extracted S F W; have hP: P≠0:= S.kernel.penalty_pos.ne'
 have ht: T*T'+Z=0:=by
    let D:=realBlock S H; have he: D*E=Qᵀ *(P • (1:Sheet (Body 1 c))):=by
      unfold D realBlock E; rw [Matrix.add_mul,Hc,Matrix.mul_assoc _ (probe S),Xc, Matrix.mul_sub]; simp only [Matrix.mul_assoc,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,Matrix.one_mul,smul_smul]; -- tune
      rw [inv_mul_cancel₀ hP]; unfold Q; simp
    change Rᵀ * D * R * T'+ -_= _; rw [Matrix.mul_assoc _ R,e,Matrix.mul_assoc Rᵀ D,he]; simp only [Z,Q,← Matrix.mul_assoc, add_neg_cancel]
 have hz: Zᵀ*T'+P • (1:Sheet (Body 1 c))= A:=by
    unfold Z; rw [transpose_neg, transpose_mul, transpose_mul,transpose_transpose,transpose_transpose,transpose_smul,transpose_one, Matrix.neg_mul, Matrix.smul_mul,Matrix.one_mul,Matrix.smul_mul,Matrix.mul_assoc _ R,e,Xc,smul_sub,smul_smul,mul_inv_cancel₀ hP,one_smul]; unfold A; abel
 let hp':(P • (1:Sheet (Body 1 c)))ᵀ=_:= (show _=(P • (1:Sheet (Body 1 c))) from by rw [transpose_smul,transpose_one]); -- h incomplete
 have hg:=(ZeroBasis.siege w G X (internalBond r F) R U' g (P • 1) hp' Q (slope_zero S) T' ht v).2
 rw [p,hX,det_smul,det_one,mul_one,one_mul, hz] at hg
 unfold leasePart; rw [repayment S Kc t]; calc
    _ = ((↑S.patch.L.val:ℝ)^8)* (Hp*P^Fintype.card (Body 1 c)):= by unfold Hp leasePart; ring
    _ =_ := by
      have hh: Hp*P^Fintype.card (Body 1 c)= T.det*torsion A (probe S*allocation r):=hg
      rw [hh]; unfold T A; ring
end YM.Fineness
#print axioms YM.Fineness.hinges
