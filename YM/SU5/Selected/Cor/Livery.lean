import YM.SU5.Selected.Cor.Silks
import YM.SU5.Selected.Cor.Clasp
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
set_option synthInstance.maxSize 24000
namespace Mezz
open Payroll Caste Silks
local notation "ⅈ" => Complex.I
variable {N:Side}{T:Type}[Fintype T][DecidableEq T]
local notation "U" => Ro N
variable (P:Mezz)(A:Society T)
local notation "N₂" => More N
local notation "P'" => P.beams
local notation "W" i:max => WRect i A.Club
local notation "S" => park N P.Broad
variable (i:P.Lot)(b:Bool)
local notation "Ω" => wrap N₂ (P.grape i.1 b)
local notation "Κ" => park N (P.yard i.1 b)
-- dance action around lamp. `cab.feels` not here. input body $bare c$ constant, prior normalized scale x, may commute twist right; guarantee after sym.
variable (F:WRect (Single N) A.Club)(x:ℝ)
local notation "D"=> dressedK (Ω) F
-- ℝ x chosen positive later. 
noncomputable def spangle (Z:Pane N):W (Single N):= (x:ℂ) • (D Z -ⅈ • ((U).val*D (swoop Z)))
local notation "s" Z:max => spangle P A i b F x Z
lemma blankH:s (1:Pane N) = design (Ro N) F x:= by unfold spangle; rw [swoop_one,bareL]; rfl
lemma spangle_r (Z:Pane N): (U).val* (s (swoop Z))=ⅈ • (s Z):=by
 unfold spangle; simp only [swoop_f Z]; rw [Matrix.mul_smul,Matrix.mul_sub,Matrix.mul_smul, ←Matrix.mul_assoc (U).val (U).val,Ro_square, Matrix.neg_mul, Matrix.one_mul,smul_comm ⅈ (x:ℂ),smul_sub ⅈ, smul_neg, sub_neg_eq_add,smul_smul ⅈ ⅈ,Complex.I_mul_I,neg_one_smul,sub_neg_eq_add,add_comm]
-- exact gauge invariance† for BOTH frames (own root for each block & each timeband).
local notation "ι₀" a:max => (plane a 0).anon N
lemma spangle_gauge (g:Seat N→SU.E)(Z:Pane N)(p:∀ g:SU.E,(tradew N (fun _=>g)).val* F= F*(A.arm g).val): s (gauge g Z) * (A.arm (g (Ω))).val= (tradew N g).val*s Z := by
 let A':=tradew N g; let q:=(Ω); let g':=(g∘(ι₀ 0))∘(ι₀ 1); have ht(t:Axis)(h:t≠3): (ι₀ t) q=q:= (Shape.anno ..).trans (congrArg _ (motion_home _ _ (P.fork_tr i.1 b t h))) -- tune trailing ..
 have hp:g' q=g q:=by unfold g'; dsimp only [Function.comp_apply]; rw [ht _ (by decide), ht _ (by decide)]
 unfold spangle; rw [swoop_g,Matrix.mul_smul,Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,Matrix.sub_mul, Matrix.smul_mul];
 rw [pennant (Ω) g F Z _ (p _), Matrix.mul_assoc, pennant (Ω) g' _ _ _ ?_]; · congr 3; rw [←Matrix.mul_assoc, ←Matrix.mul_assoc,show (U).val*(tradew N g').val= (tradew N g).val*(U).val from congrArg Subtype.val (Ro_stream g).symm]; unfold dressedK; simp only [Matrix.mul_assoc] -- `congr` brittle
 rw [show g' (Ω)= g (Ω) from hp]; exact p _

lemma spangle_size {R:ℝ} (u:‖F‖ ≤ R)(p:0≤x)(Z:Pane N) : ‖s Z‖ ≤ x*2*R:=by
 have he:0 ≤ R:=(norm_nonneg _).trans u; unfold spangle; rw [norm_smul,Complex.norm_of_nonneg p]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sub_le ..) p); rw [norm_smul, Complex.norm_I,one_mul]; exact (mul_le_mul_of_nonneg_left (add_le_add ((toll_1 ..).trans_le u) ((rent_v ..).trans_le ((toll_1 ..).trans_le u))) p).trans_eq (by ring)
@[fun_prop] lemma spangle_c : Continuous (spangle P A i b F x):= (continuous_const (y:=(x:ℂ))).smul ( (dressed_c (Ω) F).sub ( (continuous_const (y:=ⅈ)).smul ((continuous_const (y:=(U).val)).matrix_mul ((dressed_c (Ω) F).comp swoop_c))))
lemma spangle_hold (L:Finset Cover)(u:Contained (modesIn N (park N L)) F)(p:gleams L 0)(h:gleams L 1) (Z:Pane N): Contained (modesIn N (park N L)) (s Z):= by unfold spangle; rw [sub_eq_add_neg,←neg_smul]; exact ((Contained.add (holdsK (Ω) F _ _ u) ( (sparkleT (holdsK (Ω) F _ _ u) (Ro_clasp p h)).smul _ )).smul _)
lemma spangle_label (u:Contained (labelQ N A.qu.kin) F)(Z:Pane N): Contained (labelQ N A.qu.kin) (s Z):=by unfold spangle; rw [sub_eq_add_neg,←neg_smul]; exact ((Contained.add (holds_label (Ω) F _ u) ((sparkleT (holds_label (Ω) F _ u) (Ro_label ..)).smul _)).smul _)
lemma spangle_section (p: (hand b (cutM (Tset N)))* F=F)(Z:Pane N): (hand b (cutM (Tset N)))* s Z= s Z:=by unfold spangle; let L(Z:Pane N):= holdsT (Ω) F b Z p; rw [Matrix.mul_smul,Matrix.mul_sub,L Z,Matrix.mul_smul,parlance (hand b (cutM (Tset N))) _ _ (Ro_angle b) (L (swoop Z))]; -- tune let binder type Prop treated let? `let := proof` ok
variable {C ε:ℝ}{w:ℕ}{M:Tulip.Male}{X Z: Coast→ Wq P.marks}(u:Caste (N:=N) P M C ε w X Z) (v:Contained (modesIn N (park N (P.yard i.1 b))) F)
include u v
lemma spangle_dep (Y Y':Pane N)(p:Agrees (Κ) Y Y') : s Y=s Y':=by
 have h(Q Z:Pane N)(p:Agrees (Κ) Q Z): D Q = D Z:=by
    refine parks_at (Κ) (Ω) _ ?_ v; intro i' w; refine stamps_loc (o:=P.pal) P.beams (P.grape_at ..) ((P.yard_core _ b u.value).trans P.Core_subset) (?_) p _ w -- syntax
    have hv:=u.enoughN; change _< N.val*2; omega
 unfold spangle; rw [h Y Y' p,h (swoop Y) (swoop Y') (swoop_local (P.yard_spin ..) (P.yard_spin ..) p)]; all_goals decide
lemma sparkle_bill {γ R:ℝ}(h:0≤γ)(p:0≤ x)(t:‖F‖ ≤ R)(Y:Pane N)(k:Rightful S Y 1 γ): ‖s Y - design (U) F x‖ ≤ x*2*((8*P.beams*γ)*R):= by
 let J:=(8*(P.beams:ℝ)*γ); have hk:0 ≤ J:=by unfold J; positivity
 have ht(Z: Pane N)(k:Rightful S Z 1 γ):‖D Z - F‖≤ J*R:=by
    refine (tally _ F (Ω) Z v hk (fun i' w=> stampsL (o:=P.pal) _ (P.grape_at ..) ((P.yard_core _ b u.value).trans P.Core_subset) ?_ k h i' w)).trans (mul_le_mul_of_nonneg_left t hk); have hv:= u.enoughN; change _ < N.val *2; omega
 unfold spangle design; rw [←smul_sub,norm_smul,Complex.norm_of_nonneg p, sub_sub_sub_comm, ←smul_sub,←Matrix.mul_sub]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sub_le ..) p); rw [norm_smul,Complex.norm_I,one_mul]; let v':=ht _ (swoop_right (P.Broad_spin _ (by decide)) (P.Broad_spin _ (by decide)) k); change _ ≤ x*2*(J*R); exact (mul_le_mul_of_nonneg_left (add_le_add (ht _ k) ((rent_v ..).trans_le v')) p).trans_eq (by ring)
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms spangle_gauge
#print axioms spangle_r
#print axioms sparkle_bill
#print axioms spangle_hold
#print axioms spangle_dep
