import YM.SU5.Reconstruction.Brazier.Tender
import YM.SU5.Reconstruction.Brazier.Gaps
/-! Separate booths progressive through THIS sharp cone with those uniform Civic bills even varying the observation from era to era. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
open Fervor Tarmac
namespace Hearth
variable (r:Hearth Y H G j)
local notation "gg"=>r.token
local notation "π"=>pinhole (Dome (tent Y H)) (r.roof)
local notation "y'₀"=> aureole (tent Y H) j 0 r.token
local notation "Sp"=> r.spanMark Y H G j
local notation "T₁"=> r.roof
local notation "N"=> flank j (r.height:ℝ)
local notation "Wn"=> mirrorE j 0 '' N
noncomputable def outsideA : Finset Cover:= ((mem_insideAt ..).1 r.prepared).1.choose
lemma outsideAH : InTest K true (r.outsideA Y H G j) false r.token.val ∧ PhaseChoice.SupportedPhysically Λ l r.roof (r.outsideA Y H G j) (flank j (r.height:ℝ)):= ((mem_insideAt ..).1 r.prepared).1.choose_spec
noncomputable def outsideB : Finset Cover:= ((mem_insideAt ..).1 (mirror_inside Y H j r.token r.roof r.prepared)).1.choose
lemma outsideBH : InTest K true (r.outsideB Y H G j) false (aureole (tent Y H) j 0 r.token).val ∧ PhaseChoice.SupportedPhysically Λ l r.roof (r.outsideB Y H G j) (mirrorE j 0 '' flank j (r.height:ℝ)):= ((mem_insideAt ..).1 (mirror_inside Y H j r.token r.roof r.prepared)).1.choose_spec
local notation "AA"=> r.outsideA Y H G j
local notation "BB"=> r.outsideB Y H G j
abbrev facePlate (r:Hearth Y H G j) : Finset Cover:= r.outsideA Y H G j ∪ r.outsideB Y H G j
local notation "AB"=> r.facePlate Y H G j
lemma faceBudget : InTest K true (r.facePlate Y H G j) false (r.gate Y H G j).val :=
 InTest.mul ((r.outsideAH Y H G j).1.mono Finset.subset_union_left) ((r.outsideBH Y H G j).1.mono Finset.subset_union_right)
lemma faceHere : PhaseChoice.SupportedPhysically Λ l r.roof (r.facePlate Y H G j) (flank j (r.height:ℝ)∪ mirrorE j 0 '' flank j (r.height:ℝ)):=
 Tapestry.unionPrinted Λ l r.roof _ _ _ (fun x hx y hy=> Or.inl ((r.outsideAH Y H G j).2 x hx hy)) (fun x hx y hy=> Or.inr ((r.outsideBH Y H G j).2 x hx hy)) -- tune
noncomputable def centralT (a:Tarmac): Finset Cover:= volumeAround Λ l (r.roof-a.roof) (frameBudget a.book Λ l a.roof)
variable (a:Tarmac)
local notation "F"=>r.centralT Y H G j a
lemma centralHere (p:a.roof≤r.roof): PhaseChoice.SupportedPhysically Λ l r.roof (r.centralT Y H G j a) (a.land Λ l):=by
 have hm:a.roof+(r.roof-a.roof)= r.roof:=by omega
 exact hm ▸ (show PhaseChoice.SupportedPhysically Λ l (a.roof+(r.roof-a.roof)) F (a.land Λ l) from a.pays.persists _)
local notation "bT" i:max=> volumeAround Λ l i
local notation "box0"=>r.facePlate Y H G j
local notation "ζ" z:max => volumeAround Λ l z (r.facePlate Y H G j)
abbrev LongReach (a:Tarmac)(m:ℕ) := ∀ n:ℕ, PhaseChoice.FullDistances (volumeAround Λ l n (r.facePlate Y H G j∪ r.centralT Y H G j a)) (Journey.side Y m (r.roof+n))
variable (m u:ℕ) {d:ℝ} (p: Sightline Y H G j r d a) (q:LongReach Y H G j r a m)
local notation "Lm" i:max=>Journey.side Y m i
lemma centralRecord (t:Tapestry.Pay Y r.roof m u)
 {x:Cloud (Dome (tent Y H))}{C:ℝ}(g:Pocket (tent Y H) a.book a.roof C x)(v:a.roof ≤ r.roof):
 AtSupport false (Satin.region (r.centralT Y H G j a) (Journey.side Y m r.roof)) (faceOf Y H m u r.roof x):= by
 let T:= r.roof-a.roof; have h:a.roof+T=r.roof:=Nat.add_sub_of_le v -- tune simp
 unfold centralT; change AtSupport false _ _
 have ht:Tapestry.Pay Y a.roof m u:=⟨t.1,v.trans t.2⟩
 have hv:= source Y H m u a.roof x g.funded (textureBudget Y H a.book a.roof m u ht x g) T (h.symm ▸ t); rw [h] at hv; exact hv
lemma ExactSpan {n:ℕ} (t:Tapestry.Pay Y (r.roof+n) m u)
    (q₀:∀ i:ℕ, PhaseChoice.FullDistances (volumeAround Λ l i (r.facePlate Y H G j)) (Journey.side Y m (r.roof+i))) :
    faceOf Y H m u (r.roof+n) (r.spanMark Y H G j) = faceOf Y H m u (r.roof+n) (r.upper Y H G j)*faceOf Y H m u (r.roof+n) (r.lower Y H G j):=by
 apply factor_native Y H m u r.roof (PhaseChoice.separatedPhys (p:=(r.outsideAH Y H G j).2) (q:=(r.outsideBH Y H G j).2) (Disjoint.preimage (fun x:RSpace=>toMatterUnits x) (r.disjointness Y H G j))) _ _ (short_pinhole (T₁) r.token) (short_pinhole (T₁) (y'₀)) (singleCover Y H m u (x:=r.token) (r.outsideAH Y H G j).1) (singleCover Y H m u (x:=y'₀) (r.outsideBH Y H G j).1) ?_ (fun i=> dist_mono_here (Finset.union_subset (origin_mono Finset.subset_union_left _) (origin_mono Finset.subset_union_right _)) (q₀ i)) t
 change faceOf Y H m u r.roof (π r.token * π y'₀)=_ -- add π not.
 rw [← map_mul (pinhole (Dome K) r.roof) r.token y'₀]; exact singleFactor .. -- tune defeq upper
lemma face_geometry (q:LongReach Y H G j r a m) (t:ℕ):
 PhaseChoice.FullDistances (volumeAround Λ l t (r.facePlate Y H G j)) (Journey.side Y m (r.roof+t)) :=
 dist_mono_here (origin_mono Finset.subset_union_left _) (q _)
lemma ExactRead {n:ℕ} (t:Tapestry.Pay Y (r.roof+n) m u) (q:LongReach Y H G j r a m)
 {x:Cloud (Dome (tent Y H))}{g:ℝ}(h:Pocket (tent Y H) a.book a.roof g x)(p: Sightline Y H G j r d a) :
 faceOf Y H m u (r.roof+n) (x*r.spanMark Y H G j) = faceOf Y H m u (r.roof+n) x * faceOf Y H m u (r.roof+n) (r.spanMark Y H G j):=by
 have ha:= p.later
 apply factor_native Y H m u r.roof (PhaseChoice.separatedPhys (r.centralHere Y H G j _ ha.le) (r.faceHere Y H G j) (Disjoint.preimage _ p.future)) x (Sp) (climbs _ ha.le h.funded) ((r.gratuity Y H G j) ▸ short_pinhole r.roof (r.gate Y H G j))
   (r.centralRecord Y H G j a m u ⟨t.1,(by have u:=t.2; omega)⟩ h ha.le) ?_ ?_ (fun i=> dist_mono_here (Finset.union_subset (origin_mono Finset.subset_union_right _) (origin_mono Finset.subset_union_left _)) (q i)) t
 · rw [←r.gratuity]; exact singleCover Y H m u (x:=r.gate Y H G j) (r.faceBudget Y H G j)
 rw [←r.gratuity]; exact laterRead Y H m u ha h.funded _
include V in
lemma spare : ∀ᶠ n:ℕ in atTop, LongReach Y H G j r a (i (G.rows n)):= ((V.pick.grow_i.comp G.history.growsA).tendsto_atTop).eventually (unwrapped Y H r.roof _)
end Hearth
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
