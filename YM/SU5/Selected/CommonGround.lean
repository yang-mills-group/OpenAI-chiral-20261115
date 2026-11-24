/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Selected.Contrast
/-!
# A common compression-system of vacuum components for every axis

Here a schematic issue is actually critical in applying the certified moment tests:
the star on each cap is reflection in the indicated axis. One cannot just identify
all stars and read off the Isometry. Use BOTH (degree two) moments and positivity
(in both full ground algebras), after first showing that the two stars on the LABELS
commute (true even spin parity!). Then use *third* moments to intertwine actions on arbitrary
ground vectors. The coordinates of a label are **unchanged** across this equivalence; not
rotating the entire Hilbert space/time. This helps ensure consistency of measuring the
joint rank of a ground state, retaining the mixed gauge-matter experiment.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

-- mirrorTurn directly on this Test; no other rotation or continuity postulate
private lemma join_commutes (i j : Axis) : joinX (plane i 0) (plane j 0) = joinX (plane j 0) (plane i 0) := by
  have h : Signed.mirror i * Signed.mirror j= Signed.mirror j*Signed.mirror i:=by
    refine Signed.ext rfl ?_; ext1 k; simp [Signed.mirror,Bool.xor_comm]; rfl
  simp [joinX,plane,h]
private lemma odd_turn (n : Side) (i j : Axis) (p : i≠j) :
    (carR i 0 n).val*(carR j 0 n).val= -((carR j 0 n).val*(carR i 0 n).val) := by
  -- spin calculation (cf. Buffered Flips) fed to the actual geometric carR
  have he : pin i*pin j= -(pin j*pin i):=by unfold pin; simp only [←mul_assoc]; rw [mul_assoc (gammaOp i), gradingSwap, mul_neg, ←mul_assoc, neg_mul, gammaSwap i j p, neg_mul, neg_mul,neg_neg, mul_assoc (gammaOp j) grading, gradingSwap, mul_neg, neg_mul, neg_neg, mul_assoc]; simp only [mul_assoc]
  change (carR i 0 n * carR j 0 n).val= -(carR j 0 n * carR i 0 n).val
  have v : (pinLift i*pinLift j).val=(-1:ℂ) • (pinLift j*pinLift i).val:= by rw [neg_one_smul]; exact he
  unfold carR; rw [kio,kio,join_commutes i,Ygs _ _ _ v,neg_one_smul]
private lemma odd_car (n : Side) (i j : Axis) (p : i≠j) {S : Finset (Single n)} {b : Bool}
    (x : FC (Single n)) (h : Sector S b x) :
    Fock.theta (carR i 0 n) (Fock.theta (carR j 0 n) x)=
      (if b then (-1:ℂ) else 1) • Fock.theta (carR j 0 n) (Fock.theta (carR i 0 n) x) := by
  have up (i j : Axis) (x:Ket (Single n)) : Fock.theta (carR i 0 n) (Fock.theta (carR j 0 n) (create x))= -create
      (acts ((carR i 0 n).val*(carR j 0 n).val) x):=by
    rw [theta_upV,theta_smul,theta_downV,←act_mul]; simp [smul_smul]
  induction h with
  | zero=> simp only [theta_zero,smul_zero]
  | one=> simp only [theta_one]; simp
  | up k _=> rw [←create_put,up,up,odd_turn n i j p,act_neg,map_neg]; simp
  | down k _=> rw [takeF,theta_star,theta_star,theta_star,theta_star,← create_put,up,up,odd_turn n i j p,act_neg,map_neg]; simp
  | add _ _ p q=> rw [theta_add,theta_add,theta_add,theta_add,p,q,smul_add]
  | scale _ z h=> rw [theta_smul,theta_smul,theta_smul,theta_smul,star_star,h,smul_comm]
  | @mul a b _ _ x y p q=> rw [theta_mul,theta_mul,theta_mul,theta_mul,p,q]; cases a <;> cases b <;> simp
lemma evenTurn (K : Calibration) (i j : Axis) (f : Dome K) : aureole K i 0 (aureole K j 0 f)= aureole K j 0 (aureole K i 0 f) := by
  rcases eq_or_ne i j with rfl|p; · rfl
  apply Subtype.ext; funext n x; obtain ⟨S,h⟩:= findsBay K f
  have he (v:Pane (K.c n)) : fling i 0 _ (fling j 0 _ v)=fling j 0 _ (fling i 0 _ v):=by unfold fling; rw [←kor,←kor,join_commutes]
  have hx := odd_car (K.c n) i j p _ (((Tapestry.locates ..).mp h).support n|>.allV
        (reflFields j 0 (reflFields i 0 x))).sector
  simp only [Bool.false_eq_true,↓reduceIte,one_smul] at hx
  change Fock.theta _ (Fock.theta _ (f.val n (reflFields _ 0 (reflFields _ 0 x)))) =
    Fock.theta _ (Fock.theta _ (f.val n (reflFields _ 0 (reflFields _ 0 x))))
  rw [hx, show reflFields i 0 (reflFields j 0 x) = reflFields j 0 (reflFields i 0 x) from Prod.ext (he ..) (he ..)]

section lifts
variable {X : Type}{A B : Hilbert}(a : X → A)(b : X → B)
local notation "R" => Finsupp.linearCombination ℂ
lemma send_buds (h : Dense (Submodule.span ℂ (Set.range a) : Set A))
    (f : ∀ x y, inner ℂ (a x) (a y)= inner ℂ (b x) (b y)) :
    ∃ U : A →L[ℂ] B, ‖U‖ ≤ 1 ∧ ∀ x, U (a x)=b x := by
  let W : _root_.YM.Kernel.Gram (fun x y => inner ℂ (a x) (a y)):=⟨A,a,h,fun _ _=>rfl⟩
  have he (x y : X→₀ℂ) : inner ℂ (R a x) (R a y)=inner ℂ (R b x) (R b y):=by
    induction x using Finsupp.induction_linear with
    | zero=> simp
    | add i j h p => simp only [map_add,inner_add_left,h,p]
    | single i c=>
      induction y using Finsupp.induction_linear with
      | zero=> simp
      | add x y p v=> simp only [map_add,inner_add_right,p,v]
      | single j d=> simp only [Finsupp.linearCombination_single,inner_smul_left,inner_smul_right,f]
  apply W.by_bound b 1 zero_le_one; intro x
  rw [one_mul]; change ‖R b x‖≤ ‖R a x‖; apply le_of_eq
  nth_rw 1 [@norm_eq_sqrt_re_inner ℂ]; rw [← he x x,←@norm_eq_sqrt_re_inner ℂ]
lemma intertwine (p : Dense (Submodule.span ℂ (Set.range a) : Set A))
    (q : Dense (Submodule.span ℂ (Set.range b) : Set B))
    (f : ∀ x y, inner ℂ (a x) (a y)= inner ℂ (b x) (b y)) :
    ∃ u : A ≃ₗᵢ[ℂ] B, ∀ x, u (a x)= b x := by
  obtain ⟨U,t,e⟩:= send_buds a b p f; obtain ⟨V,g,h⟩:= send_buds b a q (fun x y=> (f x y).symm)
  have A' : V.comp U=ContinuousLinearMap.id ℂ _:= ContinuousLinearMap.ext_on p (by rintro _ ⟨x,rfl⟩; simp [e,h])
  have B' : U.comp V=ContinuousLinearMap.id ℂ _:= ContinuousLinearMap.ext_on q (by rintro _ ⟨x,rfl⟩; simp [h,e])
  have he (x : A) : V (U x)=x:=by rw [←ContinuousLinearMap.comp_apply,A',ContinuousLinearMap.id_apply]
  have ht (x : B) : U (V x)=x:=by rw [←ContinuousLinearMap.comp_apply,B',ContinuousLinearMap.id_apply]
  have hx (x : A) : ‖U x‖=‖x‖:=by
    apply le_antisymm (_root_.le_trans (U.le_opNorm x) (mul_le_of_le_one_left (norm_nonneg _) t))
    calc ‖x‖ = ‖V (U x)‖ := congrArg _ (he x).symm
         _ ≤ ‖U x‖ := _root_.le_trans (V.le_opNorm _) (mul_le_of_le_one_left (norm_nonneg _) g)
  exact ⟨{ U.toLinearMap with invFun:=V, left_inv:=he, right_inv:=ht, norm_map':=hx }, e⟩
end lifts

namespace Spine
variable (P : Spine)(j k : Axis)
local notation "ω" i:max=> P.groundZero i
local notation "T" i:max=> P.labelled i
local notation "turn" i:max=> P.reflectTest i

lemma doubles(x y : ℕ × P.Test) :
    inner ℂ (ω j) ((P.labelled j x) ((P.labelled j y) (ω j))) = inner ℂ (ω k) ((P.labelled k x) ((P.labelled k y) (ω k))) := by
  rcases eq_or_ne j k with rfl|p; · rfl
  let U (v:ℕ × P.Test) : Beacon P.calibration false:=(v.1,P.obs v.2)
  exact between_axes P.run P.large P.law P.history P.projection.clipped j false (P.room j)
      (show Fin 2 → _ from ![U x,U y]) k (P.room k) p [0,1] [0,1] (by decide) (List.Perm.refl _)
lemma star_agrees (s : ℕ) (x : P.Test) : P.reading j s (P.reflectTest j x)=P.reading j s (P.reflectTest k x):=by
  -- v mirror pinned both: want θi x-θk x vanishes. θi v= -θk v.
  let v:=(turn j) x-(turn k) x
  have he : ((turn j) v) = - (turn k) v:=by
    unfold v; rw [map_sub,map_sub]
    rw [reflectTest, reflectTest, aureoleTwice, aureoleTwice, evenTurn]; abel
  let f:= (turn j) v
  have hp : star (P.labelled k (s,v)) = - P.labelled k (s,f) := by
    change star (P.compressed k s v)= - P.compressed k s f
    unfold f; rw [he, P.reflected k s v,← P.at_label k, ← P.at_label k s (-(P.reflectTest k v)), map_neg]
    exact (neg_neg _).symm
  let a: (P.vacuum j):= P.labelled j (s,v) (ω j); let b: (P.vacuum k):= P.labelled k (s,v) (ω k)
  have hf : inner ℂ a a = -inner ℂ b b:=by
    unfold a b; rw [←ContinuousLinearMap.adjoint_inner_right,←ContinuousLinearMap.adjoint_inner_right (P.labelled k (s,v))]
    rw [show ContinuousLinearMap.adjoint (P.labelled j (s,v))=P.labelled j (s,f) from P.reflected j s v,
        show ContinuousLinearMap.adjoint (P.labelled k (s,v)) = - P.labelled k (s,f) from hp,
        neg_apply, inner_neg_right,neg_neg,P.doubles j k]
  apply sub_eq_zero.mp; rw [←map_sub]; apply P.separating j
  change (P.reading j s v).val (ω j)=0; rw [P.at_label]
  have hu (x : P.groundHil j) : inner ℂ x x= (‖x‖^2 :ℝ) := by push_cast; exact inner_self_eq_norm_sq_to_K x
  have hn (x:P.groundHil k) : inner ℂ x x=(‖x‖^2:ℝ):=by push_cast; exact inner_self_eq_norm_sq_to_K x
  rw [hu a, hn b] at hf
  change a=0
  have hd:=congrArg Complex.re hf; rw [Complex.neg_re,Complex.ofReal_re,Complex.ofReal_re] at hd; exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖b‖])
lemma across_pair (x y : ℕ× P.Test) : inner ℂ ((P.labelled j x) (ω j)) ((P.labelled j y) (ω j)) =
    inner ℂ ((P.labelled k x) (ω k)) ((P.labelled k y) (ω k)) := by
  rw [←ContinuousLinearMap.adjoint_inner_right,←ContinuousLinearMap.adjoint_inner_right (P.labelled k x)]
  let f:=(x.1, P.reflectTest j x.2)
  have h : ContinuousLinearMap.adjoint (P.labelled j x)= P.labelled j f := P.reflected ..
  have p : ContinuousLinearMap.adjoint (P.labelled k x)= P.labelled k f := (P.reflected ..).trans (congrArg Subtype.val (P.star_agrees k j x.1 x.2))
  rw [h,p]; exact P.doubles ..
noncomputable def planeChoice : (P.vacuum j) ≃ₗᵢ[ℂ] (P.vacuum k) :=
  (intertwine (A:=P.groundHil j) (B:=P.groundHil k) _ _ (P.spanning j) (P.spanning k) (P.across_pair j k)).choose
lemma flips_spaces (x : ℕ×P.Test) : P.planeChoice j k (P.labelled j x (ω j))=P.labelled k x (ω k) :=
   (intertwine (A:=P.groundHil j) (B:=P.groundHil k) _ _ (P.spanning j) (P.spanning k) (P.across_pair j k)).choose_spec x
lemma plane_vacuum : P.planeChoice j k (P.groundZero j)=P.groundZero k:=by
  have he (i:Axis): P.labelled i (0,1)=1:= congrArg Subtype.val (P.reading_unit i 0)
  have hp:=P.flips_spaces j k (0,1); rw [he,he] at hp; exact hp
lemma across_triple (f x y : ℕ×P.Test) : inner ℂ (P.labelled j y (ω j)) (P.labelled j f (P.labelled j x (ω j))) =
    inner ℂ (P.labelled k y (ω k)) (P.labelled k f (P.labelled k x (ω k))) := by
  rcases eq_or_ne j k with rfl|p; · rfl
  let a:=(y.1,P.reflectTest j y.2); let E(x:ℕ×P.Test):Beacon P.calibration false := (x.1,P.obs x.2)
  rw [←ContinuousLinearMap.adjoint_inner_right,←ContinuousLinearMap.adjoint_inner_right (P.labelled k y),
    show ContinuousLinearMap.adjoint (P.labelled j y)=P.labelled j a from P.reflected .., show ContinuousLinearMap.adjoint (P.labelled k y)=P.labelled k a from (P.reflected ..).trans (congrArg Subtype.val (P.star_agrees k j y.1 y.2))]
  exact between_axes P.run P.large P.law P.history P.projection.clipped j false (P.room j)
      (show Fin 3 → _ from ![E a,E f,E x]) k (P.room k) p [0,1,2] [0,1,2] (by decide) (List.Perm.refl _)
/-- Identify even the generators, even for fields not in each other's positive time sectors. -/
lemma transports_cap (v : ℕ×P.Test) : (P.planeChoice j k).conjStarAlgEquiv (P.labelled j v)=P.labelled k v := by
  let A:=P.planeChoice j k
  apply P.extGroundOperator k; intro f; apply P.extGroundVector k; intro x
  rw [←P.flips_spaces j k f, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply]
  nth_rw 1 [← P.flips_spaces j k x]
  rw [LinearIsometryEquiv.inner_map_map,P.flips_spaces j k]
  exact P.across_triple ..

lemma planeChoice_back : (P.planeChoice j k).symm = P.planeChoice k j := by
  have h : ((P.planeChoice j k).symm : (P.vacuum k) →L[ℂ] (P.vacuum j))=
      (P.planeChoice k j).toLinearIsometry.toContinuousLinearMap:=by
    apply P.extGroundOperator k; intro v
    change (P.planeChoice j k).symm _=P.planeChoice k j _
    rw [P.flips_spaces k j,←P.flips_spaces j k,LinearIsometryEquiv.symm_apply_apply]
  exact LinearIsometryEquiv.ext fun x=> congrArg (fun f : (P.vacuum k)→L[ℂ](P.vacuum j)=>f x) h
local notation "E" j:max k:max=> (P.planeChoice j k).conjStarAlgEquiv
lemma conjugate_eq {x : P.GroundOp k} : (E j k).symm x=(E k j) x:=by
  rw [LinearIsometryEquiv.symm_conjStarAlgEquiv,P.planeChoice_back]
lemma ensemble_forward {x : P.GroundOp j} (h : x∈ P.compressionAlgebra j) :
    (P.planeChoice j k).conjStarAlgEquiv x∈ P.compressionAlgebra k:=by
  let f : P.GroundOp j →⋆ₐ[ℂ] P.GroundOp k := (E j k).toStarAlgHom
  let U:=P.compressionAlgebra k; let V:=StarAlgebra.adjoin ℂ (Set.range (P.labelled j))
  have ht : IsClosed ((show StarSubalgebra ℂ (P.GroundOp j) from U.comap f) : Set (P.GroundOp j)):= by
    change IsClosed ((E j k) ⁻¹' (P.compressionAlgebra k : Set (P.GroundOp k)))
    exact (P.closureC k).preimage (show Continuous ⇑(E j k) from (P.planeChoice j k).toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous)
  have he : V ≤ U.comap f:= by
    apply StarAlgebra.adjoin_le; rintro z ⟨x,rfl⟩; change (E j k) (P.labelled j x)∈ U
    rw [P.transports_cap]; exact (P.preRead k x).property
  exact (StarSubalgebra.topologicalClosure_minimal he ht) h

def migrateHom : P.Ensemble j →⋆ₐ[ℂ] P.Ensemble k:=by
  let f : P.GroundOp j →⋆ₐ[ℂ] P.GroundOp k := (E j k).toStarAlgHom
  exact (f.comp (P.compressionAlgebra j).subtype).codRestrict (P.compressionAlgebra k)
    (fun x=> P.ensemble_forward j k (show x.val∈P.compressionAlgebra j from x.property))
lemma migrant (x : P.Ensemble j) : (P.migrateHom j k x).val=(P.planeChoice j k).conjStarAlgEquiv x.val:= rfl
lemma migrate_reverse (x : P.Ensemble j) : P.migrateHom k j (P.migrateHom j k x)=x:=by
  apply Subtype.ext; rw [P.migrant,P.migrant,← P.conjugate_eq j k,StarAlgEquiv.symm_apply_apply]
noncomputable def portals : P.Ensemble j ≃⋆ₐ[ℂ] P.Ensemble k :=
  { P.migrateHom j k with invFun := P.migrateHom k j,
                           left_inv:= P.migrate_reverse j k,
                           right_inv:= P.migrate_reverse k j,
                           map_smul':= map_smul (P.migrateHom j k) }
lemma through_plane (x : P.Ensemble j) : (P.portals j k x).val=(E j k) x.val:=rfl
lemma returns_reading (s : ℕ)(f : P.Test) : P.portals j k (P.reading j s f)=P.reading k s f:=Subtype.ext (P.transports_cap j k (s,f))
lemma invariant_integrator (x : P.Ensemble j) :
    inner ℂ (ω k) ((P.portals j k x).val (ω k))= inner ℂ (ω j) (x.val (ω j)):=by
  rw [through_plane,← plane_vacuum P j k,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]

open WeakDual CharacterSpace
-- name character in k by specifying point in j. no reliance on preservation
-- of an unspecified class of continuum-label stars.
noncomputable def otherSpectrum : C(P.Spectrum0 j,P.Spectrum0 k):= compContinuousMap (P.migrateHom k j)
lemma translates (x : P.Spectrum0 j) (b : P.Ensemble k) :
    P.chi k (P.otherSpectrum j k x) b=P.chi j x (P.migrateHom k j b):=rfl
lemma single_agrees (x : P.Spectrum0 j) (s : ℕ) (f : P.Test) :
    P.singleState k s (P.otherSpectrum j k x) f=P.singleState j s x f:= by
  rw [P.single_state,P.single_state,P.translates]
  exact congrArg _ (P.returns_reading k j s f) -- portals defeq
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.star_agrees
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.portals
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.single_agrees
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.invariant_integrator
