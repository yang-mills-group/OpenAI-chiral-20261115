import YM.SU5.Relativistic.MultiMark

/-! Noncontact physical multiplication. For readers in disjoint physical
regions (note they have ALL points of shields in those regions, there's
no translation into overlapping cells after refining) the ordinary product
of observables identified at the physical cutoff indeed realizes the
correlated-polynomial product, along the same histories in both factors. No
such assumption for coincident/possibly interacting juxtaposition! There the
`tidalDressing` always specifies what each test is at the cutoff, with no claim
that `liftD` or breathing on a joint mark is the product of the separate ones.
-/
set_option autoImplicit false
set_option maxHeartbeats 370000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable (i k s:ℕ)
local notation "N" i:max n:max=>side Y i n
local notation "breath" n:max x:max=> breathing Y H n i k x
local notation "D"=> tidalDressing Y H i k

variable (S T : BillOfWork) (x : Employee S) (y : Employee T)
local notation "B" n:max S:max => frameBudget S Λ l n
local notation "r" => 2 * (Advance.nearZero (aliasLaw Λ) + distanceLaw l)
-- true Mark equality on each horizon, use monomial PPE.
private lemma employee_product
    (v : Tapestry.Pay Y s i k)
    (w : ∀ j, j < s → ∀ z ∈ Satin.region (frameBudget S Λ l j) (N i j),
                      ∀ x ∈ Satin.region (frameBudget T Λ l j) (N i j),
                        2 * (Advance.nearZero (aliasLaw Λ) + distanceLaw l)<separation z x):
    (D).finish s (employ K S x * employ K T y) =
      (D).finish s (employ K S x) * (D).finish s (employ K T y):= by
  let f:= employ K S x; let g:= employ K T y
  induction s with
  | zero=> change roving Y H 0 i (f 0 * g 0) = _; rw [map_mul]; rfl
  | succ n ih=>
    have hp:Pay Y n i k:=⟨v.1,Nat.le_of_lt v.2⟩
    let X:= (D).finish n f; let W:= (D).finish n g
    have hx: AtSupport false (Satin.region (B n S) (N i n)) (attire X):= wearSupport Y H i k n S x hp
    have hz: AtSupport false (Satin.region (B n T) (N i n)) (attire W):= wearSupport Y H i k n T y hp
    have h : Tapestry.music Y n i k (X * W) = music Y n i k X * music Y n i k W := by
       apply attireL_inj
       unfold music; rw [attire_mul,flowing,flowing,flowing,attire_mul]
       exact ascendSep Y n i k v hx hz (w n (by omega))
    rw [Decking.finish, ih hp (fun j t=>w j (by omega))]
    change music Y n i k (X*W) * roving Y H (n+1) i (f (n+1)*g (n+1)) = (music Y n i k X * roving Y H (n+1) i (f (n+1)))* (music Y n i k W*roving Y H (n+1) i (g (n+1)))
    rw [h,map_mul]; ac_rfl

lemma finish_pair
    {x y : Altitude.Cloud (Dome K)} (p:x∈ fountainHeads K S s) (q:y∈ fountainHeads K T s)
    (v : Tapestry.Pay Y s i k)
    (w : ∀ j, j < s → ∀ z ∈ Satin.region (frameBudget S Λ l j) (N i j),
                      ∀ x ∈ Satin.region (frameBudget T Λ l j) (N i j),
                        2 * (Advance.nearZero (aliasLaw Λ) + distanceLaw l)<separation z x) :
    breathing Y H s i k (x*y) = breathing Y H s i k x* breathing Y H s i k y:=by
  apply boarded (P:={f|Officer (Set.Iic s) (fun i=>bay K (S i) true) f}) (M:=fun x=>breath s (x*y)=breath s x * breath s y) ?_ ?_ ?_ ?_ p
  · intro f (p : Officer _ _ f)
    obtain ⟨z,rfl⟩:= motif_represents K S f p.observes
    apply boarded (P:={f|Officer (Set.Iic s) (fun i=>bay K (T i) true) f}) (M:=fun y=>breath s (motif K S z*y)=breath s (motif K S z) * breath s y) ?_ ?_ ?_ ?_ q
    · intro g (q : Officer _ _ g)
      obtain ⟨z',rfl⟩:= motif_represents K T g q.observes
      have h:= Officer.visible _ _ p (Set.Subset.refl _)
      have ht:= Officer.visible _ _ q (Set.Subset.refl _)
      unfold motif pureShot breathing
      rw [PiTensorProduct.tprod_mul_tprod,Decking.reckon_paid _ _ _ h,Decking.reckon_paid _ _ _ ht,Decking.reckon_paid _ _ _ (h.together ht)]
      exact employee_product Y H i k s S T z z' v w
    · simp
    · intro x y _ _ p q; rw [mul_add,map_add,p,q,map_add,mul_add]
    intro r' x _ p; rw [Algebra.mul_smul_comm,map_smul,p,map_smul,Algebra.mul_smul_comm]
  · simp
  · intro x y _ _ p q; rw [add_mul,map_add,p,q,map_add,add_mul]
  intro z x _ u; rw [Algebra.smul_mul_assoc,map_smul,u,map_smul,Algebra.smul_mul_assoc]

-- Simultaneous period threshold and then valid on ENTIRE paid UV tail, not merely common subsequence.
lemma separated_pocket {U V : Set RSpace} (u:Disjoint U V)
    (p:∀ j, j ≤ s → SupportedPhysically Λ l j (S j) U)
    (q:∀ j, j ≤ s → SupportedPhysically Λ l j (T j) V) :
    ∀ᶠ i in atTop, ∀ {x y : Altitude.Cloud (Dome (tent Y H))}, x∈ fountainHeads K S s → y∈fountainHeads K T s →
     ∀ k n:ℕ,Tapestry.Pay Y (s+n) i k →
      attire (breathing Y H (s+n) i k (x*y))= attire (breathing Y H (s+n) i k x) * attire (breathing Y H (s+n) i k y) := by
  have h'(j:ℕ)(t:j ≤ s) : Detached Λ l (frameBudget S Λ l j) (frameBudget T Λ l j):=
    separatedPhys (frame_lines S j Λ l (V:=handstamp U) (fun i h=>p i (le_trans h t))) (frame_lines T j Λ l (V:=handstamp V) (fun i h=>q i (le_trans h t))) (Disjoint.preimage _ u)
  filter_upwards [(Finset.eventually_all (Finset.Iic s)).mpr (fun j _=> eventually_host Y H j (frameBudget S Λ l j∪frameBudget T Λ l j))] with i hl x y hx hy k n g
  obtain ⟨z,a⟩:= Tapestry.issued.mp hx
  obtain ⟨z',b⟩:= Tapestry.issued.mp hy
  induction n with
  | zero=>
    change attire (breathing Y H s i k _) = _; rw [finish_pair Y H i k s S T hx hy g ?host]
    · exact attire_mul _ _
    intro j h; exact Host.far Y H (h' j h.le) (hl j (Finset.mem_Iic.mpr h.le)) 0
  | succ n ih=>
    have h:Tapestry.Pay Y (s+n+1) i k:= (Nat.add_assoc ..).symm ▸ g
    have ht:Tapestry.Pay Y (s+n) i k:=⟨h.1,Nat.le_of_lt h.2⟩
    have h₁:= climbs (Dome K) (by omega : s ≤ s+n) a.funded
    have h₂:= climbs (Dome K) (by omega : s ≤ s+n) b.funded
    rw [← Nat.add_assoc,ascent_actual Y H (s+n) i k ((shorter (Dome K) (s+n)).mul_mem h₁ h₂),
      ascent_actual Y H (s+n) i k h₁,ascent_actual Y H (s+n) i k h₂,ih ht]
    exact ascendSep Y _ i k h (multi_extent Y H s i k a n ht) (multi_extent Y H s i k b n ht) (Host.far Y H (h' s le_rfl) (hl s (Finset.mem_Iic.mpr (le_refl s))) n)

lemma computes_disjoint {U V : Set RSpace} {a b : Set ℕ} (u:Disjoint U V)
    {x y:Altitude.Cloud (Dome (tent Y H))} {wide w':Bool}
    (p:x∈ jetty Λ l K wide (handstamp U) (a∩ Set.Iic s))
    (q:y∈ jetty Λ l K w' (handstamp V) (b∩ Set.Iic s)) :
    ∀ᶠ i in atTop, ∀ k n, Tapestry.Pay Y (s+n) i k →
      attire (breathing Y H (s+n) i k (x*y))= attire (breathing Y H (s+n) i k x) * attire (breathing Y H (s+n) i k y) :=by
  obtain ⟨S,C,h,t⟩:=pocketEvery Y H s p; obtain ⟨T,C',h',t'⟩:=pocketEvery Y H s q
  filter_upwards [separated_pocket Y H s S T u t t'] with i z k n g
  exact z h.populated h'.populated k n g
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.computes_disjoint
