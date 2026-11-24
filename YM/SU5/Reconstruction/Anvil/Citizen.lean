import YM.SU5.Reconstruction.Anvil.Hold
import YM.SU5.Reconstruction.Anvil.Cubicle
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
variable (j:Axis) (Δ:Finset Axis) (p:j∉Δ) (F:BoostBacking Y H V G C a χ)
variable {A B:(fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op}
variable {X W: ℕ → (indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op}
variable {x y:ℕ→Sky (tent Y H)} {u v:ℕ→marks (timeMesh Λ)}
variable (X₀: Slip Y H V G C a χ j x u X A) (Y₀: Slip Y H V G C a χ j y v W B)
-- all observers in lens must pay their own norm rent, self.
variable (d e f g:↥Δ→ marks (timeMesh Λ)) (q:↥Δ→ Bool) (b:ℝ)(t:Anvil.Meter)(h:t j=0)
variable {X' Y': (k:↥Δ) → ℕ →(indoor Y H V G.history G.clipped k.val false (C k.val) (displacement Y H V G.history G.clipped a false (C a) χ k.val (C k.val))).Op}
variable (Z:∀ k:↥Δ, Perpendicular Y H V G k.val (C k.val) (displacement Y H V G.history G.clipped a false (C a) χ k.val (C k.val)) (e k) (d k) x (X' k))
  (Z':∀ k:↥Δ,Perpendicular Y H V G k.val (C k.val) (displacement Y H V G.history G.clipped a false (C a) χ k.val (C k.val)) (g k) (f k) y (Y' k))
local notation "T'"=> taxableLens j Δ p d e f g q
local notation "Q" i:max=>opCarries Y H V G i (C i) (w i)
local notation "Φ"=> sunny (S₀ j) t b
local notation "Dj"=> Domain Y H G false (flank j 0)
-- prepares both in all budgets, Lens extended appropriately.
include X₀ Y₀ p Z Z' h F
lemma heartwood (z:b^2<∑ i:↥Δ,(T').gap t i^2) (v':∀ i:↥Δ, 0< (T').gap t i) : Commute A (sunny (S₀ j) t b B):= by
   obtain ⟨R,Hr⟩:= X₀.short.bddAbove_range; obtain ⟨R',Hr'⟩:=Y₀.short.bddAbove_range; let r:ℝ:=max 0 (max R R'); have hq : 0≤r:= le_max_left ..; have hv(i:ℕ):(u i:ℝ)≤r:= le_trans (Hr (Set.mem_range_self i)) (le_trans (le_max_left ..) (le_max_right ..)); have hz(i:ℕ):(v i:ℝ)≤r:= le_trans (Hr' (Set.mem_range_self i)) (le_trans (le_max_right ..) (le_max_right ..))
   obtain ⟨k1,l⟩:= eventually_atTop.mp (Anvil.envelope t b (T') h z v' r hq); obtain ⟨T,pT⟩:= Schedule.very_late (daylight (timeMesh Λ)) (a:=k1); obtain ⟨s,c,Kx⟩:= l _ pT.le
   let S:= (S₀ j); let E':=S.E (ℜ (T:ℝ))
   let M(b':Bool)(i:ℝ):= E' '' (padFar Y H V G j (C j) (w j) i b' Δ:Set (G₀ j)); have he (b:Bool)(i:ℝ): Dense (M b i):= (S.whole _).dense_image E'.continuous (lands_dense Y H V G j (C j) (w j) (F.present j) (F.forward j) i b Δ p)
   change A*(sunny (S₀ j) t b B)=sunny (S₀ j) t b B *A; ext1 v0; refine closure_minimal ?_ (isClosed_eq (ContinuousLinearMap.continuous (A* Φ B)) (ContinuousLinearMap.continuous (Φ B*A))) (he true (T:ℝ) v0)
   rintro _ ⟨v,g',rfl⟩; obtain ⟨z,rfl⟩:= LinearMap.mem_range.mp g'; apply Dense.eq_of_inner_right ℂ (he false (-(T:ℝ))); rintro _ ⟨v,q',rfl⟩; obtain ⟨w1,rfl⟩:=LinearMap.mem_range.mp q';
   let δ:= -(T:ℝ); let p1: Domain Y H G false (flank j 0):= ⟨w1.val,domain_loose Y H G _ (domain_mono Y H G inter_subset_left w1.property)⟩; let p2: Domain Y H G false (flank j 0):= ⟨z.val,domain_loose Y H G _ (domain_mono Y H G inter_subset_left z.property)⟩
   exact crevice Y H V G C a χ j Δ p F X₀ Y₀ d e f g q b t h Z Z' r s c hq hv hz T Kx.some p1 p2 (fun i=> domain_loose Y H G _ (domain_mono Y H G (show venueR j δ false Δ ⊆ _ from fun x p=>(p.2 i i.property)) w1.property)) (fun i=> domain_loose Y H G _ (domain_mono Y H G (show venueR j (T:ℝ) true Δ ⊆ _ from fun x p=>(p.2 i i.property)) z.property)) -- Kx Nonempty some syntax? ok

omit Z Z'
open Anvil.DisjointPay
-- permit using only positivity of θ/zero width.Rectangle package on all spacelike for any monitored Δ. Translating even at real nongrid latter. Need actual bounded price on k slit operator sequence at all those widths.Slice imposes cloud-positive time.
lemma real_rectangles (xA xB yA yB:Axis→marks (timeMesh Λ))
   (p' :∀ k:↥Δ,∃ (S:ℕ→ (indoor Y H V G.history G.clipped k.val false (C k.val) (w k.val)).Op), Perpendicular Y H V G k.val (C k.val) (w k.val) (xB k.val) (xA k.val) x S)
   (q':∀ k:↥Δ,∃ (S:ℕ→ (indoor Y H V G.history G.clipped k.val false (C k.val) (w k.val)).Op), Perpendicular Y H V G k.val (C k.val) (w k.val) (yB k.val) (yA k.val) y S)
   (O:Anvil.DisjointPay j Δ (fun i=>xA i) (fun i=>xB i) (fun i=>yA i) (fun i=>yB i) t b) : Commute A (sunny (S₀ j) t b B) := by
 let d(i:Axis):ℝ:= xA i; let u(i:Axis):ℝ:=xB i; let f(i:Axis):ℝ:= yA i; let v(i:Axis):ℝ:= yB i
 let F0 i:= f i+t i
 let D':= activeFee Δ d u f v t
 let ℓ(i):= Anvil.DisjointPay.gap (d i) (u i) (F0 i) (v i)
 let Q'(i:Axis): Price:= horizonPrice (0:Gt) (xA i) (xB i) (yA i) (yB i)
 have e : b^2 < ∑ i∈ D',(ℓ i)^2:=O.exact_toll j Δ p _ _ _ _ t b -- order
 have pos(k:↥D'):0<ℓ k.val:= (Finset.mem_filter.mp k.property).2; have hw:D'⊆ Δ:=Finset.filter_subset ..; have ha:j∉D':= fun v=>p (hw v)
 have C1 (k:↥D') (y:Bool): aft (d k) (u k) (F0 k) (v k) y= (Q' k).compares y (t k):=by obtain ⟨k,c⟩:=k; change aft (d k) (u k) (F0 k) (v k) y= Price.compares (⟨0,d k,u k,f k,v k⟩:Price) y (t k); unfold F0; cases y <;> simp [aft,Anvil.Price.compares] <;> ring
 have hv : ∀ k:↥D',∃ y:Bool, ℓ k= (Q' k).compares y (t k):=by
    intro k; let a := aft (d k) (u k) (F0 k) (v k); have h: ℓ k=max (a true) (a false):= max_eq_right (by by_contra! g; exact lt_irrefl 0 ((pos k).trans_eq (max_eq_left (a:=0) (b:=max (a true) (a false)) g.le)))
    cases le_total (a true) (a false)
    case inl t=> exact ⟨false,h.trans ((max_eq_right t).trans (C1 k _))⟩ -- False
    case inr t=> exact ⟨true,h.trans ((max_eq_left t).trans (C1 k _))⟩
 choose o vo using hv; let fT:= taxableLens j D' ha (fun i=> xA i) (fun i=>xB i) (fun i=>yA i) (fun i=>yB i) o
 have v(k):fT.gap t k= ℓ k:= (vo k).symm;
 choose S hS using fun k:D'=> p' ⟨k.val,hw k.property⟩; choose T hT using fun k:D'=> q' ⟨k.val,hw k.property⟩
 refine heartwood Y H V G C a χ j D' ha F X₀ Y₀ _ _ _ _ o b t h hS hT ?_ (fun i=>(v i).symm ▸ pos i)
 change b^2 < ∑ i:↥D',(fT.gap t i)^2
 simp_rw [v]; rw [← show ∑ i∈ D',ℓ i^2= ∑ i:↥D',ℓ i.val^2 from (D'.sum_attach (fun i=> ℓ i^2)).symm]; exact e
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
