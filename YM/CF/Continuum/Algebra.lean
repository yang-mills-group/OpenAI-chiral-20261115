import YM.CF.Continuum.MirrorGrid

/-!
# One net of local FiniteGaugeData probes

Use the insertions at the bra, with coefficients continuous functions of the
physical gauge variable. No tag dependence. The matter site and the positive
bond supports are tracked independently, so regions can be used both in
fermion-contraction and gauge-invariance estimates. (The *strictly* local
hierarchy one would want in the continuum also requires conventions for
scaling/transferring the stencils. Here these are native lattice units at the
specified tower level.)

Use the even observable algebra. Letters of `Fine` are in the SAME
polarization as the FiniteGaugeData amplitudes, and `star` of FC matrices usually does NOT
preserve that exterior algebra. Use instead `Window.dagger` for adjoint in the
given time convention. On even stencils it gives the physical order-reversing
convention of `Reed.reverseW`. `Window.flipTime` includes the reflection of
the sites and transports in addition. Neither should be used on odd letters
without the extra `chord` for order reversal. There is no ordinary
C⋆-positivity under this adjoint being claimed.
-/
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 4096
namespace YM.CF.Window
open Function Finset Lattice SU Fock Lat Cube Mir Mir.Trip Phase RP Spire Scroll Tulip Reed Reflect
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
section
variable {I : Type*} [Fintype I] [LinearOrder I]

lemma fine_enlarge {S T R : Finset I} (p : T ⊆ R) {b : Bool} {A : FC I} (h : Fine S T b A) :
    Fine S R b A := by
  induction h with
  | empty => apply Fine.empty
  | one => exact Fine.one
  | seed i u => exact Fine.seed i (p u)
  | add _ _ ih jh => exact ih.add jh
  | grow _ _ ih jh => exact ih.grow jh
  | scale _ _ ih => exact ih.scale _

lemma theta_twist_right (U V W : UNI I) (h : U.val*V.val=W.val*U.val) {S : Finset I} {b : Bool} {T : FC I} (p : Sector S b T) :
    theta U (twist (quantU V) T)=twist (quantU W) (theta U T) := by
  have up (k : I) : theta U (twist (quantU V) (put k))=twist (quantU W) (theta U (put k)) := by
    rw [←create_put, twist_create, theta_upV, theta_upV, twist_scalar, twist_remove,
      ←act_mul, ←act_mul,h]
  induction p with
  | zero => simp [theta_zero]
  | one => simp [theta_one]
  | up i _ => exact up i
  | down i _ => rw [takeF,map_star,theta_star,theta_star,up, map_star]
  | add _ _ ih jh => rw [map_add,theta_add,theta_add,ih,jh,map_add]
  | mul _ _ ih jh => rw [map_mul,theta_mul,theta_mul,ih,jh,map_mul]
  | scale _ q ih => rw [twist_scalar, theta_smul, theta_smul, ih, twist_scalar]

lemma theta_comp_comm (U V : UNI I) (h : U.val*V.val=V.val*U.val)
    {S : Finset I} {b : Bool} {T : FC I} (p : Sector S b T) :
    theta U (theta V T)=theta V (theta U T) := by
  have up (k : I) : theta U (theta V (put k)) = theta V (theta U (put k)) := by
    rw [theta_up,theta_up,theta_smul,theta_smul,theta_downV,theta_downV,←act_mul,←act_mul,h]
  induction p with
  | zero=> rw [theta_zero,theta_zero,theta_zero]
  | one=> rw [theta_one,theta_one,theta_one]
  | up i _=> exact up i
  | down i _=> rw [takeF,theta_star,theta_star,theta_star,theta_star,up]
  | add _ _ ih jh=> rw [theta_add,theta_add,theta_add,theta_add,ih,jh]
  | mul _ _ ih jh=> rw [theta_mul,theta_mul,theta_mul,theta_mul,ih,jh]
  | scale _ q ih=> rw [theta_smul,theta_smul,theta_smul,theta_smul,ih]
end

abbrev Evaluation (N : Side) := Bkg (More N) → FC (Single N)
/-- Note these are occupancy stencils on the physical **and** gauge grids
(see `matterSet` and `node`). They can be evaluated on either top or blocked
amplitudes; no assertion such direct evaluation of two stencils is a block
transport of their product made on a different level. -/
def localObs (N : Side) (G : Finset (Tenant.Edges (More N))) (M : Finset (Site N)) :
    Subalgebra ℂ (Evaluation N) where
  carrier := {Q | Continuous Q ∧ (∀ x y, (∀ i ∈ G, x i=y i) → Q x=Q y) ∧
    (∀ x, Fine (Tset N) (matterSet N M) false (Q x)) ∧
    ∀ (g : Site (More N)→E) x, Q (gauge g x) = twist (quantU (tradew N g)) (Q x) }
  mul_mem' := by
    rintro A B ⟨ca,la,ma,ga⟩ ⟨cb,lb,mb,gb⟩
    exact ⟨ca.mul cb, fun x y h=>congrArg₂ (· * ·) (la x y h) (lb x y h),
      fun x=>(ma x).grow (mb x), fun g x=>by simp only [Pi.mul_apply,ga,gb,map_mul]⟩
  add_mem' := by
    rintro A B ⟨ca,la,ma,ga⟩ ⟨cb,lb,mb,gb⟩
    exact ⟨ca.add cb, fun x y h=>congrArg₂ (· + ·) (la x y h) (lb x y h),
      fun x=>(ma x).add (mb x), fun g x=>by simp only [Pi.add_apply,ga,gb,map_add]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl, fun _ => Fine.empty _, fun _ _ => (map_zero _).symm⟩
  one_mem' := ⟨continuous_const, fun _ _ _ => rfl, fun _ => Fine.one, fun _ _ => (map_one _).symm⟩
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]; exact ⟨(continuous_const (y:=c • (1:FC (Single N)))), fun _ _ _=>rfl,
      fun _=>Fine.one.scale _, fun g x=>by simp only [Pi.smul_apply,Pi.one_apply,twist_scalar,map_one]⟩

section
variable {N : Side} {G G' : Finset (Tenant.Edges (More N))} {M M' : Finset (Site N)}

abbrev allObs (N : Side) := localObs N univ univ

lemma mem_localObs (Q : Evaluation N) : Q ∈ localObs N G M ↔ Continuous Q ∧
    (∀ x y, (∀ i ∈ G, x i=y i) → Q x=Q y) ∧
    (∀ x, Fine (Tset N) (matterSet N M) false (Q x)) ∧
    ∀ (g : Site (More N)→E) x, Q (gauge g x)=twist (quantU (tradew N g)) (Q x) := Iff.rfl

lemma localObs_enlarge (p : G ⊆ G') (q : M ⊆ M') : localObs N G M ≤ localObs N G' M' := by
  intro A h; obtain ⟨c,l,m,g⟩ := mem_localObs A|>.mp h; refine ⟨c, fun x y h=>?_, fun i=>?_,g⟩
  · exact l x y fun i u=>h i (p u)
  exact fine_enlarge (fun x u => (mem_matterSet ..).mpr (q ((mem_matterSet ..).mp u))) (m i)

lemma fits_all : localObs N G M ≤ allObs N := localObs_enlarge (subset_univ _) (subset_univ _)

lemma mem_allObs (Q : Evaluation N) : Q ∈ allObs N ↔ Continuous Q ∧
    (∀ x, Fine (Tset N) univ false (Q x)) ∧
    ∀ (g : Site (More N)→E) x, Q (gauge g x)=twist (quantU (tradew N g)) (Q x) := by
  rw [allObs,mem_localObs, show matterSet N univ=univ by ext; simp [matterSet]]
  constructor; exact fun ⟨c,_,h⟩=>⟨c,h⟩
  exact fun ⟨c,p⟩=>⟨c, fun x y h=>congrArg Q (funext fun i=>h i (mem_univ _)),p⟩

lemma product_region {A B : Evaluation N} (hA : A ∈ localObs N G M) (hB : B ∈ localObs N G' M') :
    A*B ∈ localObs N (G∪G') (M∪M') := Subalgebra.mul_mem _
      (localObs_enlarge (subset_union_left ..) (subset_union_left ..) hA)
      (localObs_enlarge (subset_union_right ..) (subset_union_right ..) hB)

lemma readable_commute {A B : Evaluation N} (p : A ∈ allObs N) (q : B ∈ allObs N) : A*B=B*A := by
  funext x; change A x * B x=B x * A x; simpa only [Sector.grainB,Bool.false_and, Bool.false_eq_true, ite_false,one_smul] using
    (((mem_allObs ..).mp p).2.1 x|>.sign_com (((mem_allObs ..).mp q).2.1 x))

end

section
variable {m B : Side} {M : Finset (Site (CSide m B))} {G : Finset (Tenant.Edges (Domain m B))} (i : Axis)
local notation "Λ" => CSide m B
local notation "O" => Evaluation (CSide m B)

def flipTime (m B : Side) (i : Axis) (F : Evaluation (CSide m B)) : Evaluation (CSide m B) :=
  fun x => Fock.theta (fullTurn m B i) (F (mirrorPane m B i x))

def dagger (N : Side) (i : Axis) (F : Evaluation N) : Evaluation N :=
  fun x => Fock.theta (onsite N i) (F x)

theorem dagger_local {Q : Evaluation (CSide m B)} (q : Q ∈ localObs Λ G M) :
    dagger Λ i Q ∈ localObs Λ G M := by
  obtain ⟨c,l,p,g⟩ := mem_localObs Q|>.mp q
  exact ⟨(theta_cont _).comp c, fun x y u=>congrArg (theta (onsite Λ i)) (l x y u),
    fun j=>Fine.arrive (onsite_sites M i) (onsite_swaps i) (p j),
    fun t x=>by rw [dagger, dagger, g]; exact theta_twist_right _ _ _ (commuteGaugeLocal i t) (p x).sector⟩

theorem flipTime_local {Q : Evaluation (CSide m B)} (q : Q ∈ localObs Λ G M) :
    flipTime m B i Q ∈ localObs Λ (G.image (rayE m B i)) (M.image (matterPoint m B i)) := by
  obtain ⟨c,l,p,g⟩ := mem_localObs Q|>.mp q
  have hc : Continuous (mirrorPane m B i) := by rw [mirrorPane_eq]; exact Wilson.continuous_pull ..
  refine ⟨(theta_cont _).comp (c.comp hc),fun x y p=>?_,
    fun j=> Fine.arrive (mirror_sites i M) (fullTurn_swaps i) (p _),?_⟩
  · apply congrArg (Fock.theta _); apply l; intro j u; unfold mirrorPane; rw [reflect_E,reflect_E,p (rayE ..) (mem_image_of_mem _ u)]
  intro t x; rw [flipTime,flipTime, mirror_gauge, g]; exact theta_twist_right _ _ _ (commuteGaugeMirror i t) (p _).sector

/-- Gauge coefficients may use the face data. -/
abbrev nonnegativeTime (m B : Side) (i : Axis) := localObs (CSide m B) (E₁ m B i) (posY m B i)
abbrev nonpositiveTime (m B : Side) (i : Axis) := localObs (CSide m B) (E₂ m B i) (posY m B i)ᶜ

lemma flipTime_positive {Q : Evaluation (CSide m B)} (q : Q ∈ nonnegativeTime m B i) :
    flipTime m B i Q ∈ nonpositiveTime m B i := by
  apply localObs_enlarge _ _ (flipTime_local i q)
  · intro j p; obtain ⟨x,h,rfl⟩ := mem_image.mp p; exact (flipQ ..).2 h
  intro j p; obtain ⟨x,h,rfl⟩ := mem_image.mp p
  exact mem_compl.mpr fun p=> ((tiltSide ..).mp p) h

lemma flipTime_all {Q : O} (p : Q ∈ allObs Λ) : flipTime m B i Q ∈ allObs Λ :=
  fits_all (flipTime_local i p)

lemma flipTime_invol {Q : O} (p : Q ∈ allObs Λ) : flipTime m B i (flipTime m B i Q)=Q := by
  funext x; unfold flipTime; rw [mirror_invol i]; exact theta_twice _ (fullTurn_square i) (((mem_allObs ..).mp p).2.1 _).sector

lemma dagger_invol {Q : O} (p : Q ∈ allObs Λ) : dagger Λ i (dagger Λ i Q)=Q := by
  funext x; exact theta_twice _ (onsite_square i) (((mem_allObs ..).mp p).2.1 _).sector

lemma flipTime_times (A C : O) : flipTime m B i (A*C)=flipTime m B i A*flipTime m B i C :=
  funext fun _=> theta_mul (fullTurn m B i) _ _
lemma flipTime_order {A C : O} (p : A ∈ allObs Λ) (q : C ∈ allObs Λ) :
    flipTime m B i (A*C)=flipTime m B i C * flipTime m B i A := by
  rw [readable_commute p q]; exact flipTime_times ..
lemma dagger_order {A C : O} (p : A ∈ allObs Λ) (q : C ∈ allObs Λ) :
    dagger Λ i (A*C)=dagger Λ i C * dagger Λ i A := by
  rw [readable_commute p q]; exact funext fun _=>theta_mul _ _ _
lemma dagger_plus {N : Side} (A C : Evaluation N) : dagger N i (A+C)=dagger N i A+dagger N i C :=
  funext fun _=>theta_add _ _ _
lemma dagger_smul {N : Side} (c : ℂ) (A : Evaluation N) : dagger N i (c•A)=star c • dagger N i A :=
  funext fun _=>theta_smul _ _ _
lemma flipTime_plus (A C : O) : flipTime m B i (A+C)=flipTime m B i A+flipTime m B i C :=
  funext fun _=>theta_add _ _ _
lemma flipTime_smul (c : ℂ) (A : O) : flipTime m B i (c•A)=star c • flipTime m B i A :=
  funext fun _=>theta_smul _ _ _
lemma dagger_one {N : Side} : dagger N i 1=1 := funext fun _=> theta_one _
lemma flipTime_one : flipTime m B i 1=1 := funext fun _=> theta_one _
lemma flipTime_adjoint {Q : O} (p : Q ∈ allObs Λ) :
    flipTime m B i (dagger Λ i Q) = dagger Λ i (flipTime m B i Q) := by
  funext x; exact theta_comp_comm _ _ (commuteMirror i).symm (((mem_allObs ..).mp p).2.1 _).sector

end
end YM.CF.Window
