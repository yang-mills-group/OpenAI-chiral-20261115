import YM.SU5.Relativistic.RawEase
import YM.SU5.Relativistic.TileMove
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
section billing
variable (d:Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)(χ : displayAlgebra Y H D.univ_ G.history G.clipped d false (c d) →⋆ₐ[ℂ] ℂ)
local notation "χ̂" j:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) χ j (c j)
local notation "Χ"=> SameCharacter.resident Y H D.univ_ G d false (c d) χ
local notation "Ψ"=> onDrawing Y H D.univ_ G D d c Χ
local notation "Θ"=> procession Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ρ"=>indoor Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "V"=>fort Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "p★"=>saunters Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "ω"=> vocation Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ω"=> doorstep Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "A"=>ride Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ξ"=> peninsula Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "E□"=> encase Y H D.univ_ G.history G.clipped j (c j) (χ̂ j)
local notation "P□"=> mainsea Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "e□"=> follows_road Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "B□"=> docket Y H D G j (c j)
local notation "Φ"=> driveAlgebra Y H D.univ_ G.history G.clipped j false (c j)
local notation "dock" n:max => Docked Y H D.univ_ n G.history G.clipped j (c j)
local notation "Zg" t:max => (Axis→Fin ((timeMesh Λ).L^t))

variable {I':Type*}(f:I'→ Cloud (Dome (tent Y H)))
variable (t:I'→ℕ)(S T:I'→ Slab (timeMesh Λ)) (l':List I')(b₁: Stamp (timeMesh Λ))
local notation "EE" i:max z:max => envelope (P□) (A) (e□) (Θ (B□ (t i) (f i) (S i))) (S i) (T i) z
local notation "Q₀" g:max=> packetEnvelope Y H D G j d c χ f t S T g l' b₁
local notation "ϕ" v:max=> integerRead v
local notation "GΛ"=> Axis → Stamp (timeMesh Λ)
local notation "R★" q:max=> rawRoom Y H D G j d c χ f l' b₁ T t S q
variable (u:I'→Axis→ℝ)
local notation "cm" t:max S:max T:max l:max b:max u:max=> Corridor Y H j f t S T l b u
section lease
variable (q:I'→Axis→ℝ)
lemma Corridor.translated (p:cm t S T l' b₁ u)(v:Axis→ℝ)(x:Stamp (timeMesh Λ))(h: x.val=v j) : Corridor Y H j f t S (fun i=> (T i).byStamp x) l' (b₁+x) (fun i=> u i+v):=by
 refine ⟨Slab.linesExtent x _ _ p.vault,p.issued,?_⟩
 intro i r
 have g:=p.assured i r; obtain ⟨z,w⟩:=g
 change ((T i).lower:ℝ)+x.val < ((S i).lower:ℝ)+(u i j+v j) ∧ ((S i).upper:ℝ)+(u i j+v j) < ((T i).upper:ℝ)+x.val
 rw [h,←add_assoc,←add_assoc]; exact ⟨add_lt_add_left z _,add_lt_add_left w _⟩

-- vacuum is invariant spatial
local notation "Mu" v:max=> (Ξ).U (_root_.YM.SelectionAnalysis.diameter (a:=j) v)
lemma holdsStill (v:Axis→ℝ): ((Mu v) ω)=ω:=by
  let u:= SelectionAnalysis.diameter (a:=j) v
  have ht:= compass_origin Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j) u.val
  change (Ξ).edge (u.val j) ((Ξ).U (OS.Semigroup.SEP j u.val) (ω))= _ at ht
  have hu:u.val j=0:= u.property
  have hp:OS.Semigroup.SEP j u.val=u:=by apply Subtype.ext; change u.val-(u.val j) • basis j=u.val; rw [hu,zero_smul,sub_zero]
  rwa [hp,hu,(Ξ).birth] at ht
local notation "Δ" j:max b:max l:max v:max=> windowPrice Y H D G j d c χ f t S T l b v
lemma Corridor.axisMark_price (x:Stamp (timeMesh Λ))(v:Axis→ℝ)(h:x.val=v j):
    windowPrice Y H D G j d c χ f t S T l' b₁ u = windowPrice Y H D G j d c χ f t S (fun i=> (T i).byStamp x) l' (b₁+x) (fun i=> u i+v):=by
  let B' i:= Θ (B□ (t i) (f i) (S i)); have he: (Mu v) ω =ω:=holdsStill Y H D G j d c χ v
  let x':= bracing (Ξ).E T (fun i=> EE i (u i)) b₁ l' ω
  change inner ℂ ω x'= _
  rw [← u_shift_cost (Ξ) (SelectionAnalysis.diameter v) ω x']; apply congrArg₂ (inner ℂ) he
  apply Eq.symm
  exact congrArg (fun f: V =>f) (by -- tune
    rw [←he]; apply arc_shift P□ A e□ b₁ l' S T B' x u ω v h)

/-- Domain of separated, ordered SPACETIME questions. Union of open charts. -/
def journeying : Set (I'→Axis→ℝ):= {u| ∃ (j:Axis)(l₁:List I'), l'.Perm l₁ ∧ ∃ (t:I'→ℕ)(S T:I'→ Slab (timeMesh Λ))(b: Stamp (timeMesh Λ)), Corridor Y H j f t S T l₁ b u}
noncomputable def panorama : (I'→Axis→ℝ)→ ℂ:= fun u=> if h:u∈ journeying Y H f l' then by
  let j:=Classical.choose (p:=fun (j:Axis)=> ∃ i, l'.Perm i ∧∃ (t:I'→ℕ)(S T:I'→ Slab (timeMesh Λ))(b:Stamp (timeMesh Λ)), Corridor Y H j f t S T i b u) h
  let v := h -- simplify by defines?
  let ℓ := h.choose_spec.choose -- membership Set implicit proj? tune
  let x := h.choose_spec.choose_spec.2
  exact windowPrice Y H D G j d c χ f x.choose x.choose_spec.choose x.choose_spec.choose_spec.choose ℓ x.choose_spec.choose_spec.choose_spec.choose u
 else 0

lemma panorama_price (w:List I')(l₁ : l'.Perm w)(p:Corridor Y H j f t S T w b₁ u):
    panorama Y H D G d c χ f l' u= windowPrice Y H D G j d c χ f t S T w b₁ u:=by
 have ht:u∈journeying Y H f l':=⟨j,w,l₁,t,S,T,b₁,p⟩
 unfold panorama; rw [dif_pos ht]
 exact p.interchange Y H D G j d c χ f t S T w b₁ u _ _ _ _ _ _ ht.choose_spec.choose_spec.2.choose_spec.choose_spec.choose_spec.choose_spec (l₁.symm.trans ht.choose_spec.choose_spec.1)|>.symm -- check last height projection
lemma journeyOpen : IsOpen (journeying Y H f l'):=isOpen_iff_mem_nhds.mpr fun u p=> by
 obtain ⟨i,w,x,t,S,T,b,h⟩:=p -- unfolding
 exact (h.openAt Y H i f t S T w b u).mono fun i a=> ⟨_,_,x,_,_,_,_,a⟩
lemma journeySmooth (u:I'→Axis→ℝ)(p:u∈ journeying Y H f l'): ContinuousAt (panorama Y H D G d c χ f l') u:= by
 obtain ⟨i,w,x,t,S,T,b,h⟩:=p
 refine ContinuousAt.congr (contour_cont Y H D G i d c χ f t S T w b).continuousAt ?_
 filter_upwards [h.openAt Y H i f t S T w b u] with y hy; exact (panorama_price Y H D G i d c χ f t S T l' b y _ x hy).symm
lemma panorama_perm (p : u∈journeying Y H f l') (w:List I')(g:l'.Perm w): panorama Y H D G d c χ f l' u= panorama Y H D G d c χ f w u := by
 obtain ⟨i,v,x,t,S,T,b,h⟩:=p; exact (panorama_price Y H D G i d c χ f t S T l' b u _ x h).trans (panorama_price Y H D G i d c χ f t S T w b u _ (g.symm.trans x) h|>.symm)

noncomputable def tourShift (u:I'→Axis→ℝ) (v:Axis→ℝ) : I'→Axis→ℝ:=fun i=> u i+v
lemma availableShift (p : u∈ journeying Y H f l')(v:Axis→ℝ) : tourShift u v∈ journeying Y H f l':=by
 obtain ⟨i,w,x,t,S,T,b,h⟩:=p
 obtain ⟨g,v'⟩:= converge_approach M v
 let V'(n:ℕ):Axis→ℝ:= fun i=> (g n i).val
 have hp:Tendsto (fun n=>tourShift u (v - V' n)) atTop (𝓝 u):=by
   apply tendsto_pi_nhds.mpr; intro i
   simpa only [tourShift,sub_self,add_zero] using (tendsto_const_nhds (x:=u i)).add (show Tendsto (fun n=> v-V' n) atTop (𝓝 (v-v)) from tendsto_const_nhds.sub v') -- tune
 obtain ⟨n,F0⟩:= (hp.eventually (h.openAt Y H i _ _ _ _ _ _ u)).exists
 refine ⟨i,w,x,t,S,(fun j=> (T j).byStamp (g n i)),b+g n i,?_⟩
 have ht:=Corridor.translated Y H i _ _ _ _ _ _ _ F0 (V' n) (g n i) rfl; exact ht_cast (show (fun j'=> tourShift u (v - V' n) j'+ V' n)=tourShift u v from funext fun j' => by unfold tourShift; rw [add_assoc,sub_add_cancel]) ht -- tune
where ht_cast {g₀ h₀:I'→ Axis→ℝ}{w:List I'}{S T}{b t j}(p : g₀=h₀)(q: Corridor Y H j f t S T w b g₀):Corridor Y H j f t S T w b h₀:= p ▸ q

lemma flight_homogeneous (p: u∈ journeying Y H f l') (v:Axis→ℝ):
  panorama Y H D G d c χ f l' (tourShift u v)= panorama Y H D G d c χ f l' u:=by
  let F:= panorama Y H D G d c χ f l'
  have ht:= journeySmooth Y H D G d c χ f l' (tourShift u v) (availableShift Y H f l' u p v)
  obtain ⟨i,w,x,t,S,T,b,h⟩:=p
  obtain ⟨g,v'⟩:= converge_approach M v
  let V'(n:ℕ):Axis→ℝ:= fun i=> (g n i).val
  have hx:Tendsto (fun n=>tourShift u (V' n)) atTop (𝓝 (tourShift u v)):=by apply tendsto_pi_nhds.mpr; intro i; exact tendsto_const_nhds.add v'
  apply tendsto_nhds_unique (f:=fun i:ℕ=> F (tourShift u (V' i))) (ht.tendsto.comp hx)
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards with n
  change panorama Y H D G d c χ f l' u=panorama Y H D G d c χ f l' (tourShift u (V' n))
  rw [panorama_price Y H D G i d c χ f t S T l' b u _ x h, panorama_price Y H D G i d c χ f _ _ _ l' _ (tourShift u (V' n)) w x (h.translated Y H i f t S T w b u (V' n) (g n i) rfl)]
  exact Corridor.axisMark_price Y H D G i d c χ f t S T w b u (g n i) (V' n) rfl
end lease
end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.flight_homogeneous
