import YM.CF.Buffered.Stencil
import YM.CF.Buffered.Mark

/-! # The unsimplified gaugeM substitution

`byMode` is exactly the one-particle linear image used in `Volume.adv1`.
Index true for CREATIONS. `subF` implements substitution on OPERATORS as
in subF. Proof that it respects the defining letters and relations of the
manuscript's test subspace. No frame, gauge vertex or Slater/ordering data
to guess after a substitution. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Buffered.Advance
open Function Fock NormedSpace Lattice Cube SU Lat Fock Spire Scroll MeasureTheory Finset Peaks Drapes Rush Precision Tree Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree Window
open Reed (think Fine Plain Absorb eval_blade)
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P : Side} (G : Ratio N P) (j : ℕ) (Q : Op Slot) (M : Male)
local notation "φ" => (patchQ G)
local notation "I" => Iota G
def feeL (b : Bool) (N : Side) (Q : Op Slot) := if b then exp (plankP N Q) else exp (-plankP N Q)
def byMode (z : Nom N P) (b : Bool) : Ket (Single N) →ₗ[ℂ] Ket (Single P) :=
 (trailK (switchG G).symm.toEmbedding).comp
    ((acts (Peaks.cloth j M G (unionP z))).toLinearMap.comp
      ((coat φ).comp (acts (feeL b N Q)).toLinearMap))
lemma byMode_eq (z : Nom N P) (b : Bool) (v) : byMode G j Q M z b v=
   trailK (switchG G).symm.toEmbedding (acts (Peaks.cloth j M G (unionP z)) (coat φ (acts (feeL b N Q) v))) := rfl

lemma route_foot (A : Op (Single P)) (v : Ket I) :
    acts A (trailK (switchG G).symm.toEmbedding v) = trailK (switchG G).symm.toEmbedding (acts (foot G A) v) := by
  let H := (switchG G); let D := H.symm.toEmbedding
  have hx(i : I) : trailK D (basisKet i) = basisKet (H i) := by apply PiLp.ext; intro k; rw [seamK,basis_apply,basis_apply]; simp [D, Equiv.symm_apply_eq]
  change acts A (trailK D v)=trailK D _
  nth_rw 1 2 [← basis_expand v]; simp_rw [map_sum,map_smul,hx]
  refine sum_congr rfl fun i _=> congrArg (fun w : Ket (Single P) => _ • w) ?_
  apply PiLp.ext; intro k; rw [basis_act,seamK,basis_act]; change A k _= A (H (H.symm k)) _; rw [H.apply_symm_apply k]
variable (ho : Odd G.count.val)
lemma fee_t (b : Bool) : Commute (tickA N) (feeL b N Q) := by
  letI : NormedAlgebra ℚ (Op (Single N)) := NormedAlgebra.restrictScalars ℚ ℂ _; cases b
  · exact (Commute.exp_right (plank_tick Q).neg_right)
  exact (Commute.exp_right (plank_tick Q))
include ho
lemma tickF (z : Nom N P) (b : Bool) (v : Ket (Single N)) :
    acts (cutM (Tset P)) (byMode G j Q M z b v) = byMode G j Q M z b (acts (cutM (Tset N)) v) := by
  simp only [byMode_eq,←touchP]; rw [route_foot,← lobe_t, ← act_mul]
  rw [show lobe G true * Peaks.cloth j M G (unionP z) = _ from ((canUse j G.count ho).orients M G _).eq]
  rw [act_mul,whale_plus, origin _ _ (reefS_deck ..),←act_mul,(fee_t Q b).eq,act_mul]
lemma carried_up (z : Nom N P) (b : Bool) {v : Ket (Single N)} (p : withinM (Tset N) v) : withinM (Tset P) (byMode G j Q M z b v) := by
  unfold withinM; rw [tickF G j Q M ho, p]
lemma carried_down (z : Nom N P) (b : Bool) {v : Ket (Single N)} (p : withinM (Tset N)ᶜ v) : withinM (Tset P)ᶜ (byMode G j Q M z b v) := by
  rw [within_compl, tickF G j Q M ho, within_compl.mp p, map_zero]

def stroke (z : Nom N P) (i : Single N) : FC (Single P) := if i∈ Tset N then create (byMode G j Q M z true (basisKet i)) else Fock.remove (byMode G j Q M z false (basisKet i))
lemma stroke_fine (z : Nom N P) (i : Single N) : Fine (Tset P) univ true (stroke G j Q M z i) := by
  unfold stroke; split
  next h=> exact fine_create _ (carried_up G j Q M ho z _ (within_basis _ _ h)) (within_univ _)
  next h=> exact fine_remove _ (carried_down G j Q M ho z _ (within_basis _ _ (mem_compl.mpr h))) (within_univ _)

def stringS (z : Nom N P) : Poly (Single N) (Single P) where
  term := stroke G j Q M z
  anti i k := by
    have he := (stroke_fine G j Q M ho z i).sign_com (stroke_fine G j Q M ho z k)
    unfold antiB; rw [he]; simp [Sector.grainB]

def subF (z : Nom N P) : FC (Single N) →ₗ[ℂ] FC (Single P) where
  toFun A:= (stringS G j Q M ho z).eval (twist (star (flake (Tset N)ᶜ)) A)
  map_add' A B := by rw [map_add,map_add]
  map_smul' c A := by rw [twist_scalar,map_smul]; rfl

local notation "sub" => subF G j Q M ho
variable (z : Nom N P)
lemma strokes (i : Single N) : sub z (drift (Tset N)ᶜ i)= stroke G j Q M z i := by
  change Poly.eval _ _= _; rw [flake_flip_p, eval_blade]; rfl
lemma sub_put (i : Single N) (h : i∈ Tset N) : sub z (put i)=create (byMode G j Q M z true (basisKet i)) := by
  rw [← show drift (Tset N)ᶜ i= put i from if_neg (by simpa), strokes, stroke,if_pos h]
lemma sub_take (i : Single N) (h : i∉ Tset N) : sub z (takeF i)=Fock.remove (byMode G j Q M z false (basisKet i)) := by
  rw [← show drift (Tset N)ᶜ i=takeF i from if_pos (mem_compl.mpr h), strokes, stroke,if_neg h]
lemma sub_create {v : Ket (Single N)} (h : withinM (Tset N) v) : sub z (create v)=create (byMode G j Q M z true v) := by
  nth_rw 1 2 [← basis_expand v]; simp_rw [map_sum,map_smul]; apply sum_congr rfl; intro i _; by_cases p : i∈ Tset N
  · rw [create_put,sub_put G j Q M ho z i p]
  rw [(within_test ..).mp h i p, zero_smul,zero_smul]
lemma sub_remove {v : Ket (Single N)} (h : withinM (Tset N)ᶜ v) : sub z (Fock.remove v)=Fock.remove (byMode G j Q M z false v) := by
  nth_rw 1 2 [← basis_expand v]
  unfold Fock.remove; simp_rw [map_sum,map_smul, star_sum,star_smul,map_sum,map_smul]; apply sum_congr rfl; intro i _; by_cases p : i∈ Tset N; swap
  · rw [create_put]; exact congrArg (fun w : FC (Single P) => _ • w) (sub_take G j Q M ho z i p)
  rw [(within_test ..).mp h i (by simpa), star_zero,zero_smul,zero_smul]
lemma sub_one : sub z 1=1 := by change Poly.eval _ _= _; rw [map_one]; exact Poly.eval_one ..
omit ho
lemma sub_plain {S : Finset (Single N)} {A : FC (Single N)} {b : Bool} (h : Fine (Tset N) S b A) : Absorb S (twist (star (flake (Tset N)ᶜ)) A) := by
  induction h with
  | empty=> rw [map_zero]; exact Absorb.zero
  | one=> rw [map_one]; exact Absorb.one
  | seed i u=>
    by_cases p:i∈ Tset N
    · rw [show (think (Tset N)).term i=put i from if_pos p, ←show drift (Tset N)ᶜ i=put i from if_neg (by simpa), flake_flip_p]; exact Absorb.blade u
    rw [show (think (Tset N)).term i= -takeF i from if_neg p, map_neg, ←show drift (Tset N)ᶜ i=takeF i from if_pos (mem_compl.mpr p), flake_flip_p]; simpa using (Absorb.blade u).scale (-1)
  | grow _ _ ih ig=> rw [map_mul]; exact ih.times ig
  | add _ _ ih ig => rw [map_add]; exact ih.sum ig
  | scale _ _ ih=> rw [twist_scalar]; exact ih.scale _
include ho
lemma sub_mul {S T : Finset (Single N)} {A B : FC (Single N)} {b c : Bool} (h : Fine (Tset N) S b A) (p : Fine (Tset N) T c B) : sub z (A*B) = sub z A * sub z B := by
  change Poly.eval _ _=Poly.eval _ _ * Poly.eval _ _
  rw [map_mul, (sub_plain h).eval (sub_plain p)]

omit ho
variable {R : ℕ} (p : Stencil.LaurentRadius j G.count R)
include p
lemma cont_mode (b : Bool) (v : Ket (Single N)) : Continuous (fun z=> byMode G j Q M z b v) := by
  simp_rw [byMode_eq]; have ht := Stencil.cloth_cont G j p M
  exact (LinearMap.continuous_of_finiteDimensional _).comp ((acts_cont.comp ht).clm_apply continuous_const)
lemma stroke_cont (i : Single N) : Continuous (fun z=> stroke G j Q M z i) := by
  unfold stroke; split
  · exact create_cont.comp (cont_mode G j Q M p ..)
  exact (create_cont.comp (cont_mode G j Q M p ..)).star
include ho
lemma string_cont (s : Finset (Single N)) : Continuous (fun z=> (stringS G j Q M ho z).tag s) := by
  induction s using Finset.induction_on with
  | empty=> simp_rw [Poly.tag_void]; exact continuous_const
  | insert i s ei ih=> simp_rw [Poly.tag_any _ _ _ ei]; exact (continuous_const (y:=parity i s)).smul ((stroke_cont G j Q M p _).mul ih)
lemma sub_cont : Continuous (fun V : Nom N P × FC (Single N)=> sub V.1 V.2) := by
  change Continuous (fun V : Nom N P × FC (Single N)=> ∑ S : Finset (Single N), crumb (twist (star (flake (Tset N)ᶜ)) V.2) S • (stringS G j Q M ho V.1).tag S)
  exact continuous_finsetSum _ fun i _=> (((breeze _).comp continuous_snd).matrix_elem i ∅).smul ((string_cont G j Q M ho p _).comp continuous_fst)
end YM.CF.Buffered.Advance
