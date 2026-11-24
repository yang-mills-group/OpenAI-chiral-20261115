import YM.SU5.Selected.Cor.Valve
/-! # Trait of rotation around the transverse pair $0,1$.
Spin rotation exactly (θ double on even). Envelope/slots. on ALL n. -/
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

section
open Mir Phase RP Reflect Window Nacre
open Mir.Trip
variable (i j : Axis) (p : i ≠ j) (x y : ℤ)

include p
private theorem keeps_step (k : ℤ) : (Signed.mirror i).act (k • step j : Cover) = k • step j := by
  funext a; by_cases h : a=i
  · subst a; simp [Signed.mirror,Signed.act,p]
  simp [Signed.mirror,Signed.act,h,Ne.symm h]
private theorem shape_cross : joinX (plane i x) (plane j y) = joinX (plane j y) (plane i x) := by
  unfold joinX plane
  have he : Signed.mirror i * Signed.mirror j = Signed.mirror j * Signed.mirror i := by
    refine Signed.ext rfl ?_; ext1 k; simp [Signed.mirror,Bool.xor_comm]; rfl
  dsimp only; rw [he, keeps_step i j p, keeps_step j i p.symm,add_comm]

private lemma fling_cross (n : Side) (t) : fling i x n (fling j y n t) = fling j y n (fling i x n t) := by
  unfold fling; rw [←kor,←kor,shape_cross i j p]

private lemma car_cross (n : Side) :
    (carR i x n).val * (carR j y n).val = -((carR j y n).val * (carR i x n).val) := by
  have hp : pin i * pin j = -(pin j * pin i) := by
    unfold pin; simp only [←mul_assoc]
    rw [mul_assoc (gammaOp i), gradingSwap, mul_neg, ←mul_assoc, neg_mul, gammaSwap i j p,
        neg_mul, neg_mul,neg_neg, mul_assoc (gammaOp j) grading, gradingSwap, mul_neg, neg_mul,
        neg_neg, mul_assoc]; simp only [mul_assoc]
  change (carR i x n * carR j y n).val = -(carR j y n * carR i x n).val
  unfold carR; rw [kio,kio,shape_cross i j p]
  have hz : (pinLift i * pinLift j).val = (-1:ℂ) • (pinLift j * pinLift i).val := by rw [neg_one_smul]; exact hp
  rw [Ygs _ _ _ hz, neg_one_smul]

end
variable {N:Side}
def swoop : Pane N→Pane N:= fling 1 0 N ∘ fling 0 0 N
lemma swoop_f : Involutive (swoop (N:=N)):= by intro U; unfold swoop; rw [Function.comp_apply,Function.comp_apply,fling_cross 0 1 (by decide) 0 0 N,fling_invol,fling_invol] -- may canc inner then outer? expand fling1(fling0(fling1(fling0...))) rw -> fling 1 1?.. tune
@[fun_prop] lemma swoop_c: Continuous (swoop (N:=N)):= (fling_cont ..).comp (fling_cont ..)
lemma swoop_g (U:Pane N)(g : Seat N→SU.E) : swoop (gauge g U)=gauge ((g∘(plane 0 0).anon N) ∘(plane 1 0).anon N) (swoop U):= by unfold swoop; simp only [Function.comp_apply, fling, Nacre.van]
lemma swoop_local {S:Finset Cover}{x y:Pane N} (u:gleams S 0)(v:gleams S 1)(p:Agrees (park N S) x y): Agrees (park N S) (swoop x) (swoop y):= by
 unfold swoop; simp only [Function.comp_apply]; apply fling_local; have he(a:Axis) (h:gleams S a): Finset.image ((plane a 0).anon N) (park N S)=park N S:= park_shimmer a (N:=N) ⟨S,h⟩
 rw [he 1 v]; apply fling_local; rw [he 0 u]; exact p
lemma swoop_right {δ:ℝ}{S:Finset Cover}{x:Pane N}(u:gleams S 0)(v:gleams S 1)(p:Rightful (park N S) x 1 δ): Rightful (park N S) (swoop x) 1 δ:=Rightful.land ((park_shimmer 1 (N:=N) ⟨S,v⟩).symm ▸ Rightful.land ((park_shimmer 0 (N:=N) ⟨S,u⟩).symm ▸ p))
lemma fling_blank (a:Axis): fling a 0 N (1:Pane N)=1:= by rw [fling_eq]; unfold Lattice.pull; funext i; unfold Lattice.Step.read; split; exact inv_one; rfl
@[simp] lemma swoop_one :swoop (N:=N) 1=1:= by rw [swoop, Function.comp_apply,fling_blank,fling_blank]
noncomputable def Ro (N:Side):= carR 0 0 N * carR 1 0 N
local notation "P"=> (Ro N)
lemma Ro_square (N:Side): (Ro N).val*(Ro N).val=-1:=by
 let A:=(carR 0 0 N).val; let B:=(carR 1 0 N).val; change A*B*(A*B)=-1; rw [mul_assoc,←mul_assoc B A B, car_cross 1 0 (by decide) 0 0]; simp only [mul_neg,neg_mul,mul_assoc]; -- tune
 rw [carR_square,mul_neg_one, mul_neg, carR_square]; abel
variable {S:Finset Cover}
local notation "σ" g:max => tradew N g
lemma Ro_stream (g:Seat N→SU.E): σ g * P = P * tradew N ((g∘(plane 0 0).anon N)∘(plane 1 0).anon N):=by
 unfold Ro; rw [mul_assoc (carR _ _ _),Lifted.gaugeSquare, ←mul_assoc, ←Lifted.gaugeSquare 0 0 N,mul_assoc]
lemma ro_box (S:Finset Cover)(a:Axis) : (park N S).image ((plane a 0).anon N)=park N (S.image (plane a 0).motion):=by
 unfold park; rw [image_image,image_image]; apply congrArg (fun t:Cover → Seat N=> S.image t); exact funext (fun _=> Shape.anno ..)
lemma one_twist {n:Type*}[Fintype n][DecidableEq n](A B:UNI n)(Q: Op n): twist (A*B) Q= twist A (twist B Q):=by simp only [twist_formula,Submonoid.coe_mul,star_mul,mul_assoc]
lemma Ro_trip : twist P (cutM (modesIn N (park N S))) = cutM (modesIn N (park N ((S.image ((plane 1 0).motion)).image (plane 0 0).motion))):=by rw [Ro,one_twist,refl_modes,refl_modes,ro_box S 1,ro_box]
lemma Ro_clasp (u:gleams S 0)(v:gleams S 1): twist P (cutM (modesIn N (park N S))) = cutM (modesIn N (park N S)):=by rw [Ro_trip,v,u] -- maybe unfold gleams
lemma Ro_angle (b:Bool): twist P (hand b (cutM (Tset N)))=hand b (cutM (Tset N)):=by rw [Ro,one_twist,handTogether (flatTset 1 0) b,handTogether (flatTset 0 0), Bool.not_not]
lemma Ro_preserve (b:Bool){δ:ℝ}{M:Tulip.Male}{j:ℕ}(h:0≤δ)(v:safeReflect M j δ N): twist P (sp b j M (1:Pane N))= sp b j M (1:Pane N):=by rw [Ro,one_twist,v _ (guard0 h),fling_blank,v _ (guard0 h),fling_blank,Bool.not_not]

-- label support all columns (Unit mask comm). Use constant gauge central id for label invariance? central charge only determines generation species not same gen. Need projection on fixed label & root transformations. carR unchanged colors from `prep` formula.
open Window (family)
private lemma label_spin (a:Axis)(b:Window.Family): twist (carR a 0 N) (cutM (labelQ N b))=cutM (labelQ N b):=by
 apply Mir.twist_comm; ext ⟨⟨i,b'⟩,z⟩ ⟨⟨j,c⟩,x⟩; unfold cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; simp only [labelAt]; by_cases f:z=x; subst x; ring
 let U:= (carR a 0 N).val; rw [show (carR a 0 N).val ((i,b'),z) ((j,c),x)= 0 from ?_]; · rw [zero_mul,mul_zero]
 change jump (Tofu (plane a 0) N) (fun x=> (milU (plane a 0) (Window.pinLift a) inert x).val) (i,b',z) (j,c,x)=0; rw [jump_apply]; split_ifs; -- pin tune
 · change _*( (Mir.pin a b' c)* ((1:Op SU.Slot) z x))=0; rw [Matrix.one_apply_ne f,mul_zero,mul_zero]
 rfl
lemma Ro_label (b:Window.Family): twist P (cutM (labelQ N b))=cutM (labelQ N b):=by rw [Ro,one_twist,label_spin,label_spin]
-- matrix helpers. 
section genus
variable {n m:Type*} [Fintype n][LinearOrder n][Fintype m][DecidableEq m] {X:WRect n m}
lemma peels_m (K Q:Op n)(T:UNI n)(h:twist T K= Q): T.val*(K*X)=Q*(T.val*X):=by rw [←Matrix.mul_assoc, ←Matrix.mul_assoc, ←h, twist_product]
lemma parlance (K Q:Op n)(T:UNI n)(h:twist T K= Q)(t:K*X=X): Q*(T.val*X)=T.val*X:=by rw [←peels_m K Q T h,t]
lemma sparkleT {S T: Finset n}{U:UNI n}(p:Contained S X)(h:twist U (cutM S)= cutM T):Contained T (U.val*X):=parlance _ _ _ h p
lemma cross (T:UNI n) (A:WRect n m): T.val*(star T).val*A=A:= by rw [show T.val*(star T).val=1 from T.property.2, Matrix.one_mul]
end genus

end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb
#print axioms Ro_trip
#print axioms Ro_preserve
#print axioms Ro_label
#print axioms swoop_f
#print axioms swoop_g
