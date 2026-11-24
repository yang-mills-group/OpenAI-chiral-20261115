import YM.SU5.Relativistic.Grades
import YM.SU5.Relativistic.Filling
import YM.SU5.Relativistic.CarChain
/-!
# Geometry registration of local physical polynomials.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5500
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter MeasureTheory Metric
open Lattice Wilson RG SU Lat Mir RP Reflect Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Py Py.Rate LocalLimit PhaseChoice Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy MeshClock Selected
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L:Rack Λ l}{B:Clay Λ l}(D : Exhibition Y H a b I E L B)(G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (j:Axis) (J: Arena Y H G.history.circuit j 0 false)
local notation "M"=> timeMesh Λ
local notation "N" i:max z:max=> notch M i z
local notation "D₀"=> Dome (tent Y H)
local notation "Τ"=> Cloud (Dome (tent Y H))
local notation "P₀" n:max=> vistaFinish Y H n D
local notation "d★" => vistaDressing Y H D
local notation "B₀" => driveAlgebra Y H D.univ_ G.history G.clipped j false J
local notation "Rg" t:max => Docked Y H D.univ_ t G.history G.clipped j J

local notation "ρ"=> D.univ_
local notation "reach" n:max f:max => reachMark (tent Y H) ((P₀ n) f)
section meters
variable (s : ℕ) (F : Cloud (Dome (tent Y H)))
structure Carries (j:Axis) (W : Slab (timeMesh Λ)) : Prop where
  regionHere : ∃ U:Set RSpace, IsCompact U ∧ F∈ poet Y H s U ∧ U⊆ {v:RSpace | (W.lower:ℝ) ≤ v j ∧ v j ≤ (W.upper:ℝ)}
  permits : W.lines s

variable (W:Slab (timeMesh Λ))
lemma docketFound (c:Carries Y H s F j W): ∃ B' : B₀, (Rg s) W (reach s F) B':= by obtain ⟨U,p,q,t⟩:= c.regionHere; exact precise_tile Y H D G j J F W q t c.permits
noncomputable def docket : B₀:= if h:Carries Y H s F j W then (docketFound Y H D G j J s F W h).choose else 0
lemma docket_bound (W:Slab (timeMesh Λ))(c:Carries Y H s F j W) : (Rg s) W (reach s F) (docket Y H D G j J s F W):=by unfold docket; rw [dif_pos c]; exact (docketFound Y H D G j J s F W c).choose_spec
lemma cabin_cut (U:Set RSpace) (h:F∈ poet Y H s U): F∈shorter (Dome (tent Y H)) s:= gateIssued Λ K l true (handstamp U) (Set.Iic s) s (by rw [inter_self]; exact h)
lemma Carries.shortCut (h:Carries Y H s F j W) : F∈shorter (Dome (tent Y H)) s:= by obtain ⟨U,_,a,_⟩:= h.regionHere; exact cabin_cut Y H s F U a -- j include?
lemma Carries.further (h:Carries Y H s F j W)(t:ℕ)(p:s≤t) : Carries Y H t F j W:= by
  obtain ⟨U,e,a,w⟩:= h.regionHere; refine ⟨⟨U,e,?_,w⟩,W.lines_above p h.permits⟩
  exact circum_widens Y H Subset.rfl (Set.Iic_subset_Iic.mpr p) a
lemma docket_above (c:Carries Y H s F j W)(t:ℕ)(p:s≤t): (Rg t) W (reach t F) (docket Y H D G j J s F W) := by
  rw [priceClimb Y H D G s (c.shortCut Y H j s F W) t p]; exact (docket_bound Y H D G j J s F W c).elevated Y H D.univ_ s G.history G.clipped j J t p
lemma same_docket (c:Carries Y H s F j W)(t:ℕ)(p:s≤t): docket Y H D G j J s F W=docket Y H D G j J t F W := Docked.uniqueB Y H D.univ_ t G.history G.clipped j J (docket_above Y H D G j J s F W c t p) (docket_bound Y H D G j J t F W (c.further Y H j s F W t p))
end meters

-- translating multi-resolution FiniteGaugeData test. P0 (contact!) first, cad after.
def migrate (s:ℕ)(z:Cover)(x:Cloud (Dome (tent Y H))) : Marks (tent Y H) false := relocateWorld Y H false z (reach s x)
def signOver (s:ℕ)(z:Cover)(x:Cloud (Dome (tent Y H))) : Cloud (Dome (tent Y H)):= pinhole (Dome (tent Y H)) s (packMark _ (migrate Y H D s z x))
section scene
variable (d:Axis)(T:∀ j:Axis, Arena Y H G.history.circuit j 0 false)(c:displayAlgebra Y H D.univ_ G.history G.clipped d false (T d) →⋆ₐ[ℂ] ℂ)
local notation "χ"=> SameCharacter.resident Y H D.univ_ G d false (T d) c
local notation "Φ"=> onDrawing Y H D.univ_ G D d T χ
local notation "χ̂" j:max => displacement Y H D.univ_ G.history G.clipped d false (T d) c j (T j)
local notation "σ" n:max=> response Y H D.univ_ n G.history G.clipped j false (T j) (χ̂ j)
local notation "μ" t:max z:max x:max=> migrate Y H D t z x
local notation "π" t:max z:max x:max=> signOver Y H D t z x
variable {Z:Type*}(f : Z → Cloud (Dome (tent Y H)))
lemma priceTogether (n:ℕ)(v:Z→ Cover) (l₁:List Z): Φ (l₁.map (fun i=> π n (v i) (f i))|>.prod)= (σ n) (l₁.map (fun i=> μ n (v i) (f i))|>.prod):=by
 let p:=l₁.map fun i : Z=> μ n (v i) (f i)
 have he : pinhole (Dome (tent Y H)) n (packMark _ p.prod)= _ := (show pinhole (Dome (tent Y H)) n (packMark _ p.prod)= (l₁.map (fun i=> π n (v i) (f i))|>.prod) from by rw [map_list_prod,map_list_prod]; simp only [p,List.map_map]; rfl)
 exact he ▸ costs_basis Y H D G d j T c n p.prod (packMark _ p.prod) rfl
variable (l₁:List Z) (b':Stamp (timeMesh Λ)) (g:Z→ Slab (timeMesh Λ))
local notation "Π" x:max => procession Y H D.univ_ G.history G.clipped j false (T j) (χ̂ j) x
local notation "Ω"=> doorstep Y H D.univ_ G.history G.clipped j false (T j) (χ̂ j)
local notation "A"=> (ride Y H D.univ_ G.history G.clipped j false (T j) (χ̂ j)).E
local notation "E□"=> encase Y H D.univ_ G.history G.clipped j (T j) (χ̂ j)
local notation "B□"=> docket Y H D G j (T j)
variable (t : Z→ℕ) (W: Z → Slab (timeMesh Λ))
noncomputable def rawRoom (v:Z→Axis→ Stamp (timeMesh Λ)): ℂ:= inner ℂ Ω ((bracing A g (fun i=> E□ (W i) (g i) (B□ (t i) (f i) (W i)) (v i)) b' l₁) Ω)

lemma brace_match {I α:Type*} [Monoid α] {M₁:Mesh}(A₀:ℝ≥0→α)(g':I→Slab M₁)(f h:I→ α)(l:List I)(b:Stamp M₁)(ht:∀ i∈ l,f i=h i):
    bracing A₀ g' f b l=bracing A₀ g' h b l:= by
 induction l generalizing b with
 | nil=>rfl
 | cons i l ih=>rw [bracing,bracing,ht i List.mem_cons_self,ih _ (fun j k=> ht j (List.Mem.tail _ k))]

lemma priceEncase (v:Z→ Cover)(q:∀ i∈ l₁,Carries Y H (t i) (f i) j (W i)) (p:inRow g b' l₁)(n:ℕ)(h:Precise n b')
  (k:∀ i∈ l₁,t i≤n ∧ (g i).lines n ∧ fitsMesh j (W i) (g i) (fun j=> notch (timeMesh Λ) n (v i j))) :
    Φ ((l₁.map (fun i=> signOver Y H D n (v i) (f i))).prod) = rawRoom Y H D G j d T c f l₁ b' g t W (fun i j=> notch (timeMesh Λ) n (v i j)):=by
   let X(i:Z):= μ n (v i) (f i)
   choose! c' t' using (show ∀ i∈ l₁,∃ B : driveAlgebra Y H D.univ_ G.history G.clipped j false (T j), Docked Y H ρ n G.history G.clipped j (T j) (g i) (X i) B∧ Π B= E□ (W i) (g i) (B□ (t i) (f i) (W i)) (fun j' : Axis=> notch M n (v i j')) from fun i z=> by
      exact Docked.pokes Y H D.univ_ n G.history G.clipped j (T j) (χ̂ j) (W i) (g i) (reach n (f i)) _ (docket_above Y H D G j (T j) (t i) (f i) (W i) (q i z) n (k i z).1) (v i) (k i z).2.1 (k i z).2.2)
   unfold rawRoom; rw [priceTogether Y H D G j d T c]; rw [← calendarPrice Y H D.univ_ n G.history G.clipped j (T j) (χ̂ j) g X c' l₁ (fun i z=> (t' i z).1) b' h p]
   rw [brace_match A g (fun i=> Π (c' i)) (fun i=> E□ (W i) (g i) (B□ (t i) (f i) (W i)) (fun j:Axis=>N n (v i j))) l₁ b' ?_] -- implicit metas
   exact fun i z=> (t' i z).2
end scene
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.priceEncase
