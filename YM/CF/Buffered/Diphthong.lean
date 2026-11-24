import YM.CF.Buffered.Curriculum
/-!
# Cover translations of the physical marks, on the paired hot data

No assertion of symmetry between a mark and a freshly placed one *at
cutoffs* in Cap. Show here that the warm-side square or linear mark used for
the comparison can actually be positioned at the chosen tile on its period,
with equality of the actual readings because two reflected steps of advancement
land on the right microscopic `4B`-aligned translation. Twice-theta pays the
phase ON CAR. We do not need any `pc` estimates for this. In each partner on
its common regulator, this identifies the single-tiled mark; for tile
replication will instead use the odd reflection mark.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure Nacre Window Tulip Skye Brace
attribute [local instance] opCStarAlgebra
namespace Heat
lemma theta_theta {I:Type*}[Fintype I][LinearOrder I] (A B C:UNI I)(p:A.val*B.val= -C.val){s:Finset I}{b:Bool}{T:FC I}(h:Sector s b T): theta A (theta B T) = twist (quantU C) T := by
 have up(i:I): theta A (theta B (put i))=twist (quantU C) (put i):=by
    rw [←create_put,theta_upV,theta_smul,theta_downV, twist_create, ←act_mul,p,act_neg]; simp [smul_smul]
 induction h with
 | zero=> rw [theta_zero,theta_zero,map_zero]
 | one=> rw [theta_one,theta_one,map_one]
 | up i _ => exact up i
 | down i _ => rw [takeF, theta_star,theta_star,up,map_star]
 | mul _ _ a b=> rw [theta_mul,theta_mul,a,b,map_mul]
 | add _ _ a b=> rw [theta_add,theta_add,a,b,map_add]
 | scale _ c a=> rw [theta_smul,theta_smul,twist_scalar,a,star_star]
variable {m B n:Side}
variable (i:Axis)(a b :ℤ)
lemma plane_join : joinX (plane i a) (plane i b)=lagX ((a-b) • step i):=by
 simp only [joinX,plane,lagX,mirror_axial]; congr 1; nth_rw 1 [←Signed.mirror_inv i]; exact inv_mul_cancel _
 rw [sub_smul]; abel
lemma firm_join : (carR i b n).val * (carR i a n).val= -(prepU (lagX ((a-b) • step i)) 1 inert n).val:=by
 change (carR i b n * carR i a n).val= _; rw [carR,carR,kio,plane_join]; have ht: (pinLift i * pinLift i).val=(-1:ℂ) • (1 : UNI SpinIdx).val := by rw [neg_one_smul]; exact pin_square i
 rw [Ygs _ _ 1 ht,neg_one_smul]
-- b-a controls forward translation, while prep uses -difference.
def pitchT (B : Side) (z : ℤ) : ℤ:=2*B.val*z
lemma refl_rephase {z:ℤ} (c:a-b=pitchT B z) (f : Evaluation n) {l:Bool} {S:Finset (Single n)}(h:∀ x, Sector S l (f x)): Buffered.refl i b (Buffered.refl i a f)=liftShift i B z f:=by
 funext x; unfold Buffered.refl fling liftShift; rw [←kor,plane_join]; rw [theta_theta _ _ _ (firm_join i a b) (h _), c, show (b-a) • step i= -coverShift i B z from by rw [←neg_sub _ _,neg_smul, c]; rfl]; rfl
lemma oven_move {p : Pinning m B} {c':Phase.Part m B}{W:Scroll m B c'}{clip:Clip}{β t e u:ℝ} {z:ℤ} (c:a-b=pitchT B z) (f : Evaluation (CSide m B)) {l:Bool} {S:Finset (Single (CSide m B))} (h:∀ x, Sector S l (f x)): heatNum p W clip β t e u (Brace.northZ m B) (insertTop f)=heatNum p W clip β t e u (Brace.northZ m B) (insertTop (Buffered.refl i b (Buffered.refl i a f))):=by
 rw [refl_rephase i a b c f h]; apply heatNum_shift _ _ _ _ _ _ ((2*z) • step i); intro x; unfold insertTop liftShift; rw [pack_shift,lag_cancel,shift_eq]; exact CF.Fixed.across_twist (helix _).symm _ _ rfl _
end Heat
namespace Burn
open Heat Advance Scree
variable {K:Calibration}(C:Conveyor K)(m:Side)(n:ℕ)(k:ℕ)
variable {h:K.Allowed m n}
def liner := nextMark (ho:=K.R.odd_side) (j:=K.K.j) (C.warm m n) (C.loom m) K.η K.J.d (C.wave' n) (steps K.V m K.B n) k -- tune odd
noncomputable def postV (A:Mark (cell m K.B K.R.L 0)) := advanceMark (j:=K.K.j) (ho:=K.R.odd_side) (C.warm m n) (C.loom m) K.η K.J.d (C.wave' n) (steps K.V m K.B n) A k
lemma postV_step (A:Mark (cell m K.B K.R.L 0)): postV C m n (k+1) A=liner C m n k (postV C m n k A):=by unfold postV liner; rw [advanceMark]
local notation "N₀" => (cell m K.B K.R.L 0)
local notation "ℒ" => Vale.cell m K.B K.R.L
variable {C n m k}
namespace Bedded
variable (P:Bedded C h) {A D:Mark (cell m K.B K.R.L k)} {S T:Support (More (cell m K.B K.R.L k))} {b:Bool}
include P
lemma surrounds (t:k<n)(v: AtSupport b S A) : AtSupport b (Advance.padded (apt m K.B K.R.L k) S (K.R.L.val*gross K.D K.w K.R.J)) (liner C m n k A) := by
 obtain ⟨g⟩:=(Shots.warm_grant P.pair).grant k t; obtain ⟨V,d,c,Y,l⟩:=g.cap; have hz:=surround (apt m K.B K.R.L k) (steps K.V m K.B n k) K.K.j ((C.wave' n k).val) (C.warm m n (k+1)).J.M K.R.odd_side K.η K.J.d (C.warm m n (k+1)).beta (C.loom m k) (show Stencil.LaurentRadius _ _ _ from K.legal) Y.bill ((Shots.warm_grant P.pair).branch k t) g.legal.1 g.legal.2 _ v (C.lawn m h.1 k) ((Shots.warm_grant P.pair).aligned k t); rw [(Shots.warm_grant P.pair).radius k t] at hz; exact hz
lemma global {E:Mark (cell m K.B K.R.L 0)} (u:k≤n) (a: AtSupport b univ E) : AtSupport b univ (postV C m n k E):=by
 induction k with
 | zero => exact a
 | succ k ih => rw [postV_step]; exact (P.surrounds u (ih (by omega))).mono (subset_univ _)
lemma trips_num {E:Mark (cell m K.B K.R.L 0)}(g:AtSupport false univ E) (p:k≤n): markedRead E (C.loom m 0) (denZ (C.warm m n 0) K.P (C.loom m 0))= markedRead (postV C m n k E) (C.loom m k) (denZ (C.warm m n k) K.P (C.loom m k)):= by
 induction k with
 | zero => rfl
 | succ k ih => rw [ih (by omega),postV_step]; exact single_num _ _ _ _ _ _ _ _ K.legal (Shots.warm_grant P.pair) (P.global (by omega) g) p
lemma trips_ref {E:Mark (cell m K.B K.R.L 0)}(g:AtSupport b univ E) (p:k≤n)(i:Axis)(s:ℤ): postV C m n k (reflMark i s E)= reflMark i (planeAt s K.R.L k) (postV C m n k E):=by
 induction k with
 | zero=> simp only [postV, planeAt,pow_zero,one_mul,advanceMark]
 | succ k ih=>
   rw [postV_step, postV_step,ih (by omega), ←step_plane]; obtain ⟨g'⟩:=(Shots.warm_grant P.pair).grant k p; obtain ⟨u,d,c,Y,H⟩:=g'.cap; exact rising (apt m K.B K.R.L k) (steps K.V m K.B n k) K.K.j ((C.wave' n k).val) (C.warm m n (k+1)).J.M K.R.odd_side K.η K.J.d (C.warm m n (k+1)).beta (C.loom m k) _ _ ((Shots.warm_grant P.pair).aligned k p) (P.global (by omega) g) ((Shots.warm_grant P.pair).branch k p) Y (show Stencil.LaurentRadius _ _ _ from K.legal) g'.legal.1 g'.legal.2
lemma warm_move {a b z:ℤ}(c:a-b=pitchT K.B z)(i:Axis){f: Mark (cell m K.B K.R.L 0)} (w: AtSupport false univ f):
 markedRead (reflMark i b (reflMark i a f)) (C.loom m 0) (denZ (C.warm m n 0) K.P (C.loom m 0))= markedRead f (C.loom m 0) (denZ (C.warm m n 0) K.P (C.loom m 0)):=by
 have u:=((w.refl i a).mono (subset_univ _)); let V:Mark (cell m K.B K.R.L 0):=reflMark i b (reflMark i a f); have v: AtSupport false univ V:=(u.refl i b).mono (subset_univ _)
 rw [P.trips_num w le_rfl, P.trips_num (show AtSupport false univ (reflMark i b (reflMark i a f)) from v) le_rfl,P.pays_num _ (P.global le_rfl v).env,P.pays_num _ (P.global le_rfl w).env, P.trips_ref u le_rfl,P.trips_ref w le_rfl]
 have ht: planeAt a K.R.L n-planeAt b K.R.L n=pitchT K.B ((K.R.L.val:ℤ)^n*z):=by rw [planeAt,planeAt,←mul_sub,c]; unfold pitchT; ring
 exact (oven_move i (planeAt a K.R.L n) (planeAt b K.R.L n) ht (both (postV C m n n f)) (fun x=> ((P.global le_rfl w).allV (x,x)).sector)).symm
lemma hot_times (t:k<n)(v:AtSupport false S A)(u:AtSupport false T D)(e:∀ x∈S,∀ y∈T,2*(nearZero K.D+K.w)<separation x y) : liner C m n k (A*D)=liner C m n k A * liner C m n k D:= by
 obtain ⟨g⟩:=(Shots.warm_grant P.pair).grant k t; obtain ⟨V,d,c,Y,l⟩:=g.cap; exact separated_mult (apt m K.B K.R.L k) (steps K.V m K.B n k) K.K.j ((C.wave' n k).val) (C.warm m n (k+1)).J.M K.R.odd_side K.η K.J.d (C.warm m n (k+1)).beta (C.loom m k) (show Stencil.LaurentRadius _ _ _ from K.legal) Y.bill ((Shots.warm_grant P.pair).branch k t) g.legal.1 g.legal.2 _ _ v u (C.lawn m h.1 k) e
end Bedded
end Burn
end YM.CF.Buffered
#print axioms YM.CF.Buffered.Burn.Bedded.warm_move
