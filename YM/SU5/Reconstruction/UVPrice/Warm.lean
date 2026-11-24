import YM.SU5.Reconstruction.Trap.Castle
import YM.SU5.Reconstruction.UVPrice.AtZero
/-!
# Optional soft stamp prices in the actual physical law. Build helpers.
-/
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
open Roy
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
local notation "F₀"=> osValue Y H V G a (C a) χ
variable (j j' : Axis) (hv:j'≠j)
local notation "N" i:max => flank i 0
local notation "L" i:max=> lowland i 0
local notation "Φ"=> move (tent Y H)
variable (p : ∀ j, saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤)
lemma towards (Λ: Preparation): ∃ y : ℕ→ marks (timeMesh Λ), (∀ i, 0< (y i:ℝ)) ∧ Tendsto (fun i=> (y i:ℝ)) atTop atTop:= by
 choose y h using fun i:ℕ=> Schedule.very_late (a:= ((i:ℕ):ℝ)) (daylight (timeMesh Λ))
 exact ⟨y,fun i=>lt_of_le_of_lt (Nat.cast_nonneg i) (h i),tendsto_atTop_mono (fun i=> (h i).le) tendsto_natCast_atTop_atTop⟩
include V in
noncomputable def crawl (z: placement Λ)(u:0≤coordinates Λ z j)(f:Ds (N j)) : Ds (N j):=⟨Φ z f.val,budget_base Y H V G j 0 f.val z f.property u⟩ -- include V implicit? it's Prop proofs into structure.Main
include p
lemma crawls (z: placement Λ)(u:0≤coordinates Λ z j)(f:Ds (N j)) : (Os j) (crawl Y H V G j z u f)=(Pr j) z ((Os j) f):=by
 let x:= Submodule.inclusion (domain_loose Y H G (N j)) f; exact voice_move Y H V G j (C j) (w j) (p j) z x u (domain_loose Y H G _ (crawl Y H V G j z u f).property)
lemma comeBy (f g : Ds (N j)) (z: placement Λ)(u:0≤coordinates Λ z j): ∃ b: (θ j) f.val * Φ z g.val∈D univ,
          inner ℂ ((Os j) f) ((Pr j) z ((Os j) g))= F₀ ⟨(θ j) f.val*Φ z g.val,b⟩:=by
 have hp:=mirror_twice j f.val; let y:= crawl Y H V G j z u g; let h: (θ j) ((θ j) f.val)∈ Ds (N j):=hp.symm ▸ f.property
 obtain ⟨b,k⟩:= across_charge Y H V G C a χ j ((θ j) f.val) h y.val y.property (p j); unfold y at *; rw [← crawls Y H V G C a χ j p z u]
 rw [show (⟨_,h⟩:Ds (N j))=f from Subtype.ext hp] at k; exact ⟨b,k⟩
omit p in
lemma castSpend (_f: Ds (N j))(z:Gt)(y:j'≠ j) : (Pr j) (eject j' z)= (S₀ j).U ((z:ℝ) • Picket.cross j j' y) := (castSpace Y H V G C a χ j y z).trans (Picket.trans_space j' _ _ (h:=y)) -- f unused
include hv p
-- cross equality for movement along right half stamp axes
lemma skyPair (l r : Ds (N j))(l' r' : Ds (N j')) (hx : (θ j) l.val= (θ j') l'.val)(hy:r.val=r'.val) (s q:Gt)(e:0≤ (s:ℝ))(d:0≤(q:ℝ)) :
    inner ℂ ((Os j) l) ( (S₀ j).U ((q:ℝ) • Picket.cross j j' hv) ((S₀ j).E (ℜ s) ((Os j) r)))= inner ℂ ((Os j') l') ((S₀ j').E (ℜ q) ((S₀ j').U ((s:ℝ) • Picket.cross j' j hv.symm) ((Os j') r'))) := by
 let z:= eject j s+eject j' q; obtain ⟨b,k⟩:= comeBy Y H V G C a χ j p l r z (by simp [z,hv.symm,e])
 obtain ⟨t,d⟩:= comeBy Y H V G C a χ j' p l' r' z (by simp [z,hv,d])
 let χ1: (θ j) l.val * Φ z r.val=(θ j') l'.val*Φ z r'.val:=congrArg₂ (·*·) hx (congrArg _ hy)
 have χ2:(Pr j) z = _:= across_time Y H V G j (C j) (w j) j' s q hv
 have χ3:(Pr j') z=((S₀ j').E (ℜ q)).comp ((S₀ j').U ((s:ℝ) • Picket.cross j' j hv.symm)):=by unfold z; rw [add_comm (eject j s), across_time Y H V G j' (C j') (w j') j q s hv.symm,← (S₀ j').independent]; rfl
 rw [χ2] at k; rw [χ3] at d
 -- maintain z (so unchanged on RHS from unfolding budget in transports)
 refine Eq.trans k (Eq.trans (congrArg F₀ (Subtype.ext χ1)) d.symm)
-- eliminating the frame-shear zero-ground discrepancy
local notation "Nf" i:max=> (Ds (N i))
omit p in
include V in
lemma fence (f:Ds (N j)):
    ∃ s:Gt, Φ (eject j' s) f.val∈ Ds (N j') ∧ Φ (eject j' (-s)) f.val∈ Ds (L j'):=by
 obtain ⟨U,c,r,e⟩:= (compact_domain Y H G).1 f.property
 obtain ⟨x,y,h,t⟩:= Schedule.shutters (daylight (timeMesh Λ)) j' c
 obtain ⟨s,rq⟩:= Schedule.very_late (a:=max (-(x:ℝ)) (y:ℝ)) (daylight (timeMesh Λ))
 refine ⟨s,?_,?_⟩
 · apply domain_mono Y H G _ (moving Y H V G _ _ e); rintro z ⟨z,h,rfl⟩; change 0≤ z j'+coordinates Λ _ _; rw [coordinates_eject,eject_at]; linarith [(le_max_left (-(x:ℝ)) (y:ℝ)),(t z h).1]
 apply domain_mono Y H G _ (moving Y H V G _ _ e); rintro z ⟨z,h,rfl⟩; change z j'+coordinates Λ _ _ ≤ 0; rw [coordinates_eject,eject_at,AddSubgroup.coe_neg]; linarith [(le_max_right (-(x:ℝ)) (y:ℝ)), (t z h).2]
lemma timely_occupancy (v : IsCompact (Beneath (S₀ j) 0))(f : Ds (N j))(y:ℝ) : (S₀ j).U (y • Picket.cross j j' hv) (cue (S₀ j) ((Os j) f)) = cue (S₀ j) ((Os j) f):=by
 obtain ⟨z,h₁,h₂⟩:= fence Y H V G j j' hv f
 have hp (z:Gt):0 ≤ coordinates Λ (eject j' z) j:= by simp [hv.symm];
 let W(i:Gt):=crawl Y H V G j _ (hp i) f; let r:Ds (N j'):= ⟨_,h₁⟩; let u':= (θ j) (W (-z)).val
 have ku:u' ∈ Ds (L j'):=domain_mono Y H G ?_ (mirror_support Y H G j (W (-z)).val h₂)
 swap; · rintro z ⟨z,h,rfl⟩; change mirrorE j 0 z _ ≤ 0; rw [mirrorE,if_neg hv]; exact h
 have kh : mirrorE j' 0 '' L j' ⊆ N j':=by
    rintro v ⟨v,h,rfl⟩; change 0≤ mirrorE j' 0 v _; rw [mirrorE,if_pos rfl]; linarith [ (show v j'≤ 0 from h)]
 let T: Ds (N j') := ⟨(θ j') u', domain_mono Y H G kh (mirror_support Y H G j' u' ku)⟩
 obtain ⟨s,k,b⟩:= towards Λ
  
 apply frostBill (S₀ j) (S₀ j') hv ((Os j) f) v (daylight (timeMesh Λ)) (z:ℝ) (fun i=> (ℜ (s i:ℝ))) _ ((Os j') T) ((Os j') r)
 swap; · refine NNReal.tendsto_coe_atTop.mp (b.congr ?_); intro i; rw [Real.coe_toNNReal _ (k i).le]
 intro n i hi h; let q:Gt:= ⟨i,hi⟩; have hu:= skyPair Y H V G C a χ j j' hv p (W (-z)) (W z) T r (mirror_twice ..|>.symm) rfl (s n) q (k n).le h.le
 unfold W at hu; rw [crawls Y H V G C a χ j p, crawls Y H V G C a χ j p, castSpend Y H V G C a χ j j' f (-z) hv,castSpend Y H V G C a χ j j' f z hv, AddSubgroup.coe_neg] at hu
 rw [Real.coe_toNNReal _ (k n).le]; exact hu
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
