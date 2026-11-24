import YM.SU5.FiniteGaugeData.Dally.Portent
import YM.SU5.FiniteGaugeData.Seld.Kron
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
set_option linter.unusedSectionVars false
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T₁: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace Seld.Leal
open Celeritas Land
open KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)
local notation "Λ₀"=> (A a)
namespace Breve.Price
open Mist Dover
variable (X:Engine Y h W' R a H)(q:Carousel Λ.R.L)(b:Axis)(B:List Axis)
variable (V:∀ a:Axis,Harbor Y h W' R Φ a)(T:∀ a:Axis,Engine Y h W' R a (V a))
open Mist Dover Leda
open scoped NNReal ENNReal Classical
variable (J': Cask Y h)
local notation "Θ"=> leafP Y h W' R A S' V T
local notation "ℰ"=> Osc Y h W' R A S' V T
local notation "J0"=> Φω Y h W' R V T
local notation "Q"=> Anteroom (T a).val
local notation "Y'"=> Wave Y h W' R V T
local notation "Ω"=> J0 a
local notation "P₀"=> Pond Y h W' R A S' V T
namespace VertexF
-- physical widths & support even after elevators (requires true W-local intersection).
lemma doorway (K:Calibration)(z : W K) (x y : Axis → ℤ) (r : ℕ) (h : ∀ a : Axis,∃ S, Studio a (x a) (y a) r S ∧ Locator K z S) :
    ∃ S, Locator K z S ∧ ∀ a, Studio a (x a) (y a) r S := by
  suffices H : ∀ p : List Axis, ∃ S, Locator K z S∧ ∀ a∈ p, Studio a (x a) (y a) r S by
    obtain ⟨S,d,h⟩:= H Terrace.scheduleL; exact ⟨S,d,fun i=> h i (Terrace.scheduleV i)⟩
  intro p; induction p with
  | nil => obtain ⟨S,e⟩:= testimony K z; exact ⟨S,e,by simp⟩
  | cons a p ih =>
    obtain ⟨S,s,h⟩:= h a; obtain ⟨T,u,t⟩:= ih
    have μ (i : Axis) (P V : Finset Cover) (p : P ⊆ V) (k : Studio i (x i) (y i) r V) : Studio i (x i) (y i) r P :=
      ⟨fun z t => k.behind z (p t), fun z t=> k.ahead z (p t)⟩
    exact ⟨S∩T,Portent.Lands K S T z h u, fun i v=> (List.mem_cons.mp v).elim
      (fun e => e ▸ μ a _ S inter_subset_left s) (fun b => μ i _ T inter_subset_right (t i b))⟩
lemma womb : ∃ S, Locator Kₜ J'.m S∧ ∀ a,Studio a 0 (yard Kₜ (J'.d a)) (reserve Λ l) S :=
  doorway Kₜ J'.m 0 (fun a => (yard Kₜ (J'.d a))) (reserve Λ l) J'.w
/- explicit spatial clock translation of region receipt, generalized from Azure WP31 helper. -/
lemma vax (K:Calibration)(U:W K)(p:Cover)(g:Locator K U S) :
    Locator K (Mist.orbitW K p U) (Chrono.temple ((tic K:ℤ) • p) S) := by
  let t (i : Axis) : Cover := ((tic K:ℤ)*p i) • step i
  have D(u v:Cover)(S:Finset Cover) : temple u (temple v S)=temple (v+u) S := by unfold temple; rw [image_image]; apply congrArg (fun f: Cover → Cover=> S.image f); funext i; exact add_assoc ..
  have he (B: List Axis) : Locator K (hourS K p U B) (temple ((B.map t).sum) S) := by
    induction B with
    | nil=> simpa [hourS,temple] using! g
    | cons i B ih=> rw [hourS.eq_2,List.map_cons,List.sum_cons,add_comm,← D]; exact loc_tic _ _ _ _ ih
  have T : (Terrace.scheduleL.map t).sum=(tic K:ℤ) • p := by funext i; fin_cases i<;> simp [t,Terrace.scheduleL]
  rw [← T]; exact he _
lemma usurp (K:Calibration) (p:Cover) {x y:ℤ} (n:ℕ) (g:Studio a x y n S) :
    Studio a (x+gaugeW K (p a)) (y + gaugeW K (p a)) n (temple ((tic K:ℤ) • p) S):=by
  constructor<;> intro i h <;> obtain ⟨k,l,rfl⟩:= mem_image.mp h
  · have v:=g.behind k l; change k a+((tic K:ℤ)*p a)+(n:ℤ) ≤ _; unfold gaugeW; omega
  have V:=g.ahead k l; change _ ≤ k a+((tic K:ℤ)*p a); unfold gaugeW; omega
abbrev years (i:Axis) := energyS Λ (J'.d i) (s-J'.s)
abbrev gravity := ascended Y h J'.s W' R (s-J'.s) J'.m
variable (p : Cover)
def portF (p : Cover) := Mist.orbitW Kₜ p (gravity Y h s W' R J')
abbrev lowQ (i : Axis) := gaugeW Kₜ (p i)
abbrev topQ (i : Axis) := (yard Kₜ (years Y h s J' i) : ℤ) + lowQ Y h p i
-- same footprint all axes. `s≥J'.s` usually.
lemma vowel : ∃ S, Locator Kₜ (portF Y h s W' R J' p) S∧ ∀ i, Studio i (lowQ Y h p i)
    (topQ Y h s J' p i) (reserve Λ l) S := by
  obtain ⟨S,u,hx⟩ := womb Y h J'
  let Z := seriesQ Λ l S (s-J'.s)
  have H (a : Axis) : Studio a 0 (yard Kₜ (years Y h s J' a)) (reserve Λ l) Z :=
    series_geo Y h S (J'.d a) (s-J'.s) a (hx a)
  refine ⟨_,vax _ Kₜ _ p (ascend_loc Y h S J'.s (s-J'.s) J'.m u W' R),fun i=> ?_⟩
  simpa only [zero_add] using usurp Z i Kₜ p (reserve Λ l) (H i)
-- coordinate conversion proven from WP10
abbrev fineX (p : Cover) := WithLp.toLp 2 fun i:Axis=> spinT Λ.R.L s (p i)/(tic Kₜ:ℝ)
lemma transferQ (n:ℤ) : spinT Λ.R.L s ((tic Kₜ:ℤ)*n)/(tic Kₜ:ℝ) = spinT Λ.R.L s n := by
  have H : 0<(tic Kₜ:ℝ) := by exact_mod_cast tic_pos Kₜ
  unfold spinT; push_cast; field_simp
lemma relativeQ : spinT Λ.R.L s (lowQ Y h p a)/(tic Kₜ:ℝ) = Leda.pixels L₁ (fun _ : Unit => reportQ s p) () a :=
  transferQ Y h s _
lemma ampleQ (hs:J'.s ≤ s): spinT Λ.R.L s (topQ Y h s J' p a)/(tic Kₜ:ℝ) =
    spinT Λ.R.L s (p a) + spinT Λ.R.L J'.s (J'.d a) := by
  obtain ⟨n,v⟩:= Nat.exists_eq_add_of_le hs; subst s; unfold topQ lowQ gaugeW years
  rw [slot_add,add_div, ← yard_le, transferQ Y h, transferQ Y h]
  rw [Nat.add_sub_cancel_left,timeTour,add_comm]
lemma roofE (g : Studio a (lowQ Y h p a) (topQ Y h s J' p a) (reserve Λ l) S) (i : Cover) (gi : i∈ S) (hs:J'.s ≤ s) :
    spinT Λ.R.L s (p a) ≤ fineX Y h s i a ∧ fineX Y h s i a ≤ spinT Λ.R.L s (p a) + spinT Λ.R.L J'.s (J'.d a) := by
  let f (n:ℤ) := spinT L₁ s n/(tic Kₜ:ℝ)
  change _≤f _ ∧ f _≤_
  have H : Monotone f:=fun i j h=> div_le_div_of_nonneg_right ((slot_le ..).mpr h) (by positivity)
  constructor
  · refine le_trans (le_of_eq (transferQ Y h s (p a)).symm) (H ?_)
    have v:=g.ahead i gi; unfold lowQ gaugeW at v; omega
  refine le_trans (H ?_) (le_of_eq (ampleQ Y h s a J' p hs))
  have v:=g.behind i gi; omega
#print axioms womb
#print axioms vowel
#print axioms roofE
end VertexF
end Breve.Price
end Seld.Leal
end YM.CF.Buffered.Afterglow.Hierarchy
