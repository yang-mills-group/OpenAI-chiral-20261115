import Bay.D.Lasso
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
local notation "T4"=>SU.group
open Buffered Py Py.Rate LocalLimit Preparation Buffered.Afterglow
open Tower VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal

open SlabMark MeshClock

variable (K:Calibration) (j:Axis) (t:ℕ)
local notation "w" => ruler K.B
def Nup (t i:ℕ):ℕ:=2^i*t
def Reach (S:Finset Cover):Prop := ∀p∈S, K.ℓ≤p j ∧ p j+(K.ℓ:ℤ) ≤ w*t

lemma reach_grow (S:Finset Cover) (H: Reach K j t S): Reach K j (2*t)
   (plow K j (t:ℤ) (reflectedBox j 0 S ∪ S)):=by
 have z:0≤w*t:=mul_nonneg (show (0:ℤ) ≤w from le_trans (by norm_num: (0:ℤ) ≤1) (ruler_gene _)) (by positivity)
 intro p u
 obtain ⟨v,a,rfl⟩:=plow_stays K j (t:ℤ) _ u
 rw [moves,if_pos rfl]
 rw [Nat.cast_mul,Nat.cast_ofNat,mul_comm (2:ℤ),←mul_assoc]
 rcases mem_union.mp a with b|b
 · obtain ⟨x,e,rfl⟩:=mem_image.mp b
   have h:=H x e
   rw [fling_move,if_pos rfl]; omega
 · have h:=H v b
   omega

lemma Reach.above {S:Finset Cover}(H:Reach K j t S): region j 0 K.ℓ S:=
 fun _ a=> (zero_add _).trans_le (H _ a).1

def bow (F: Buffered.Family K) :Buffered.Family K:= relocate K j t (Tower.mirror K j 0 F * F)
def singing (F:Buffered.Family K) : ℕ→ Buffered.Family K
| 0=>F
| m+1=>bow K j (Nup t m) (singing F m)

lemma singing_up {F} {S:Finset Cover}
   (h:InTest K true S false F) (a:Reach K j t S) (i:ℕ):
 ∃ S': Finset Cover, InTest K true S' false (singing K j t F i) ∧ Reach K j (Nup t i) S':=by
 induction i with
 | zero=> rw [singing,Nup,pow_zero,one_mul];exact ⟨_,h,a⟩
 | succ i ih=>
   obtain ⟨T,b,r⟩:=ih
   rw [singing,show Nup t (i+1)=2*Nup t i by unfold Nup; rw [pow_succ']; ring]
   exact ⟨_, flow_port K j (gaugeT K (Nup t i)) ((axial K j 0 b).mono subset_union_left |>.mul (b.mono subset_union_right)),reach_grow _ _ _ _ r⟩

lemma reap (P:VacuumSelection.Spine) (W:P.Register) (s:ℕ)
 (f:P.Test) {S:Finset Cover} (u:InTest P.calibration true S false f.val)
 (p:Reach P.calibration j t S)
 {C:ℝ} (h:0<C) (r:∀n, ‖P.E s (singing P.calibration j t f.val (n+1))‖≤C^(2^(n+1):ℕ)):
 ∀y, ‖P.singleState j s y f‖ ≤ C := by
 let m n:=singing P.calibration j t f.val n
 have g n:=singing_up _ _ _ u p n
 let b n:P.Test:=⟨m n,aux_test (g n).choose_spec.1⟩
 have h' n : b (n+1)=recoil P j (Nup t n) (b n):=by
   apply Subtype.ext
   change m (n+1)=bow P.calibration j (Nup t n) (m n)
   simp only [m, singing]
 change ∀y, ‖P.singleState j s y f‖ ≤ C
 rw [show f=b 0 by apply Subtype.ext; change f.val=m 0;simp only [m, singing]]
 refine sprouts P j s W h b ?_ r
 intro n y
 obtain ⟨S',u',v'⟩:=g n
 rw [h']
 exact rips P j s (b n) u' (Reach.above _ _ _ v') _ _
