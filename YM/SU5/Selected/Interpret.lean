import YM.SU5.Selected.Bank
import YM.SU5.Selected.LocalWard
import YM.SU5.Selected.Render

/-!
# Component moments of the Satin resolution hierarchy on this course
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Set Theory
local notation "A₀"=>catalog Y H V G j strict C
local notation "S"=>stationC Y H V G j strict C
variable (d : Axis) (C' : Arena Y H G.history.circuit d 0 strict)
local notation "α"=>catalog Y H V G d strict C'
local notation "φ"=>earlyMap Y H V G j strict C d C'
local notation "𝒯"=> bank Y H V G j strict C d C'
local notation "μ"=>residents Y H V G strict d C'
local notation "ϵ" s:max u:max f:max p:max=>boxElement Y H V G j strict C s u f p

noncomputable def seal₀ (s:ℕ)(f:observable K strict) : A₀ := ⟨(P s) f,included Y H V G j strict C (s,f)⟩
local notation "mk₀"=>seal₀ Y H V G d strict C'

/-- Every presentation into a box (axis, rise, width) corresponds to THIS element of the common source spectrum algebra. -/
lemma corner (s:ℕ) (f: observable K strict) : (𝒯).corner (mk₀ s f) = (P s) f :=
  (matches_map Y H V G j strict C d C' (mk₀ s f)).trans (intertwines Y H V G d strict C' j C (s,f))
lemma seal_found (s:ℕ) {f:observable K strict} (h:Veranda Y H s j strict f) :
    (𝒯).mark (ϵ s h.span h.fwd h.pos)=mk₀ s f:= by
  exact (𝒯).mono_ ((Transaction.match_P (𝒯) (ϵ s h.span h.fwd h.pos)).trans ((onAny Y H V s G.history G.clipped j strict C h).symm.trans (corner Y H V G j strict C d C' s f).symm))

variable (x:Resident (catalog Y H V G d strict C'))
noncomputable def markE (s:ℕ)(f:observable K strict):= eye x (mk₀ s f)
local notation "Eχ"=>markE Y H V G strict d C'
local notation "L"=> (𝒯).selected x
-- Pack Hilbert data of the selected component. (Also does not expand
-- all normed structures with ground-dependent proofs at every use.)
noncomputable def fiberH : Hilbert := (𝒯).representation x
local notation "Δ" => fiberH Y H V G j strict C d C' x
noncomputable def fiberOp : S →⋆ₐ[ℂ] ((Δ).Op) := (𝒯).showOp x
local notation "πχ" => fiberOp Y H V G j strict C d C' x
noncomputable def fiberVec : (Δ).space := (𝒯).showVec x
local notation "ωχ" => fiberVec Y H V G j strict C d C' x
noncomputable def fiberState : S →ₚ[ℂ] ℂ := (𝒯).selected x
local notation "χs" => fiberState Y H V G j strict C d C' x
lemma fiber_look (a:S) : χs a = eye x ((𝒯).mark a):=rfl
lemma fiber_mean (a:S) : inner ℂ ωχ (πχ a ωχ) = χs a := (𝒯).show_mean x a
lemma fiber_square (a b:S) : inner ℂ (πχ a ωχ) (πχ b ωχ) = χs (star a*b) := (𝒯).show_square x a b

section
variable (s : ℕ)
lemma normalizedAt {f:observable K strict}(h:f.val=1): Eχ x s f = 1:=by
  have he : mk₀ s f=1:=Subtype.ext (cap_unit Y H V G d strict C' s f h)
  rw [markE,he,map_one]
lemma addAt {f g h:observable K strict}(p:h.val=f.val+g.val): Eχ x s h= Eχ x s f+ Eχ x s g:=by
  have e: mk₀ s h=mk₀ s f+mk₀ s g:=Subtype.ext (cap_add Y H V G d strict C' s h f g p)
  unfold markE; rw [e,map_add]
lemma scaleAt {f g:observable K strict} (a:ℂ)(p:f.val=a • g.val): Eχ x s f=a • Eχ x s g := by
  have e: mk₀ s f=a • mk₀ s g:=Subtype.ext (cap_scale Y H V G d strict C' s f g a p)
  unfold markE; rw [e,map_smul]
lemma at_mirror {a : Axis}(Yq:Arena Y H G.history.circuit a 0 strict) (f:observable K strict) :
    Eχ x s (dual Y H a strict f)=star (Eχ x s f):=by
  have e: mk₀ s (dual Y H a strict f)=star (mk₀ s f):=Subtype.ext
    ((oppositeStar Y H V G d strict C' a Yq s f).trans
      (mirror_cap (F:=f) Y H V s G.history G.clipped d strict C').symm)
  unfold markE; rw [e,map_star]
lemma at_lattice {f g: observable K strict} (j:Axis) (t:ℤ) (p:f.val=relocate K j t g.val) : Eχ x s f= Eχ x s g:=
  congrArg (fun a:α=> eye x a) (Subtype.ext (cap_lattice Y H V G d strict C' j f g s t p) : mk₀ s f=mk₀ s g)
lemma at_refine (f:observable K strict) (n:ℕ) :
    Eχ x (s+n) (upward Y H G.history strict f s n)= Eχ x s f:= by
  have h:= cap_level (F:=f) Y H V s G.history G.clipped d strict C' (s+n) (by omega)
  rw [Nat.add_sub_cancel_left] at h
  exact congrArg (fun a:α=> eye x a) (Subtype.ext h : mk₀ (s+n) (upward Y H G.history strict f s n) = mk₀ s f)
lemma placed_sampling (f:observable K strict) (p:Veranda Y H s j strict f):
    inner ℂ ωχ ((πχ (boxElement Y H V G j strict C s p.span p.fwd p.pos)) ωχ)= Eχ x s f:= by
  exact (fiber_mean Y H V G j strict C d C' x _).trans (congrArg (fun a:α=> eye x a) (seal_found Y H V G j strict C d C' s p))
lemma entry_sampling {u w} (a : Entry Y H s j strict u)(p:0<u)(b:Entry Y H s j strict w)(q:0<w)
    (f:observable (tent Y H) strict)(h:f.val=mirror K j 0 a.val.val * b.val.val) :
    inner ℂ ((πχ (ϵ s u a p)) ωχ) ((πχ (ϵ s w b q)) ωχ)= Eχ x s f := by
  let g:=ϵ s u a p; let g':=ϵ s w b q
  have hh:(𝒯).mark (star g*g')=mk₀ s f:=
    (𝒯).mono_ ((Transaction.match_P (𝒯) (star g*g')).trans ((rectangle Y H V G j strict C s f a p b q h).symm.trans
      (corner Y H V G j strict C d C' s f).symm))
  exact (fiber_square Y H V G j strict C d C' x g g').trans (congrArg (fun a:α => eye x a) hh)
lemma residents_read (t: S) : (∫ x, (𝒯).selected x t ∂μ) = inner ℂ (ω) (t.val ω) := by
  simp_rw [Transaction.selected_look]; rw [(all_residents Y H V G j strict C d C').use_char,Transaction.matchVal,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]; rfl
lemma resident_mark (t:α) : (∫ x, eye x t ∂μ)=inner ℂ Ω (( (𝒯).corner t ) Ω):= (all_residents Y H V G j strict C d C').use_char t
lemma residents_mean (f:observable (tent Y H) strict) : (∫ x,Eχ x s f ∂μ)= E s f.val := by
  unfold markE; rw [resident_mark Y H V G d strict C' d C',corner,Vacancy.inspected]
lemma mean_admit (f: observable K strict) : Continuous (fun x=> Eχ x s f) := eyeline _
lemma residents_caps (l : List (Beacon (tent Y H) strict)) :
    (∫ x,(l.map fun f=> Eχ x f.1 f.2).prod ∂μ)= inner ℂ Ω (((l.map (disc Y H V G j strict C)).prod) Ω) := by
  let a(u:Beacon K strict):= mk₀ u.1 u.2
  let F := (l.map a).prod
  have hx(x: Resident (α)) : (l.map (fun f=> Eχ x f.1 f.2)).prod=eye x F:=by
    unfold F; rw [map_list_prod,List.map_map]; rfl -- maybe order Fun.comp list_map
  have hb : (l.map (disc Y H V G j strict C)).prod= (𝒯).corner F:=by
    unfold F; rw [map_list_prod,List.map_map]
    congr 2; funext u; exact (corner Y H V G j strict C d C' u.1 u.2).symm
  simp_rw [hx,hb]; exact resident_mark Y H V G j strict C d C' _ -- binder
end
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.entry_sampling
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.residents_caps
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.residents_mean
