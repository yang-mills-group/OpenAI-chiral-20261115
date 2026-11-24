import VerifiedSatinGroundInteraction
import YM.SU5.Selected.Equator
import YM.SU5.Selected.Homeland
/-!
# Pangea. Glued continuum interpolation loci and functions for every ordered group of thick
 test stencils (subnet on REAL E⁴-relative-position domain). These are **Euclidean points**.
 Any charts, any common grade. nil and empty costs also work. No claim that this
 is all configurations or that UNSMEARED χ is replaced. CP5. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 340000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
open TopologicalSpace OS.Ground YM.SelectionAnalysis Vacancy
variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "ℛ" => Aurora Y H V Q j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "Ω₀" => seat0 Y H V Q j strict C
local notation "ω₀" => floorV Y H Q.circuit j 0 strict C
local notation "E₀" t:max x:max p:max => entrance Y H V t Q Qt j strict C x p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
local notation "Φ" => atCharacter Y H V Q Qt j strict C f
local notation "Λ₀" => traveller Y H V Q Qt j strict C
local notation "Ε" t:max => response Y H V t Q Qt j strict C f
local notation "Π" B:max => procession Y H V Q Qt j strict C f B
local notation "Υ" u:max => moveMark Y H u strict
local notation "Θ" => mirrorInMarks Y H j strict
local notation "Τ" => Marks (tent Y H) strict
local notation "Μ" => timeMesh Λ
local notation "ψ" t:max n:max => heatStamp Y H V t Q Qt j strict C n
local notation "Σ₁" u:max d:max => shiftStamp Y H V Q Qt j strict C u d
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "Ρ" => indoor Y H V Q Qt j strict C f
local notation "Ω" => doorstep Y H V Q Qt j strict C f
local notation "Oa" => arrive Y H V Q Qt j strict C f
local notation "a₀" t:max x:max => bud Y H V t Q Qt j strict C f x
local notation "M₁" t:max => futureMark Y H t j strict
local notation "S"=> turnstile Y H V Q Qt j strict C f
local notation "R" => ride Y H V Q Qt j strict C f
local notation "P" k:max => (S).crew k
local notation "T" => look j
open Germ SelectionAnalysis Sunbelt
local notation "Ξ"=> mainsea Y H V Q Qt j strict C f
local notation "δ"=> daylight Μ
open Repertoire
set_option maxHeartbeats 500000
variable {J : Type*} [Fintype J]
-- literal readers, not requiring equality of operators for different verandae; all labels multiple use possible
variable (X:J→ Marks (tent Y H) strict) (P' : ∀ i, Veranda Y H s j strict (X i))
lemma upward_levels (t r:ℕ)(p:s ≤ t)(v: t ≤ r) : newLevel Y H t Q strict (newLevel Y H s Q strict X t) r=newLevel Y H s Q strict X r:=by
 funext i; apply Subtype.ext; have ht:= joined Y H (D:=D) s (t-s) (r-t) (X i).val; rw [show s+(t-s)=t by omega,show t-s+(r-t)=r-s by omega] at ht; exact ht.symm
lemma startLevel: newLevel Y H s Q strict X s=X:=by funext i; apply Subtype.ext; change stream Y H D s (s-s) _=_; rw [Nat.sub_self]; rfl

variable (C' : ∀ j, Arena Y H Q.circuit j 0 strict)(c:∀ j,(displayAlgebra Y H V Q Qt j strict (C' j)) →⋆ₐ[ℂ]ℂ)(hi:∀ j k s x,response Y H V s Q Qt j strict (C' j) (c j) x=response Y H V s Q Qt k strict (C' k) (c k) x)
variable (p:List J)
local notation "B" n:max=> newLevel Y H s Q strict X n
local notation "Z" j:max=> Arena Y H Q.circuit j 0 strict
local notation "V₀" n:max j:max b:max=> bandstand Y H V n Q Qt j strict (C' j) (c j) (B n) b
local notation "Q₀" t:max k:max=> ∀ i:J, Veranda Y H t k strict ((B t) i)
local notation "fΛ"=> J→Axis→ℝ
structure Request (j:Axis) where
  grade : ℕ
  good : s≤grade
  ringT : ∀ i:J, Veranda Y H grade j strict (newLevel Y H s Q strict X grade i)
  year : List J
  check : p.Perm year
-- avoid equality of Request references via existence specifying bandstand and separate `t ≥...` not needing casts. stored @ grade without requirement least so widen. companion opens.
local notation "L" k:max=> Request Y H s Q strict X p k
variable (r: Request Y H s Q strict X p j)
lemma larger(t:ℕ)(v:r.grade ≤ t): ∃ w:Q₀ t j,(V₀ t j w) = V₀ r.grade j r.ringT:=by
 have he:= upward_levels Y H s Q strict X _ t r.good v; suffices p:∃ w:∀ i,Veranda Y H t j strict (newLevel Y H r.grade Q strict (newLevel Y H s Q strict X r.grade) t i), bandstand Y H V t Q Qt j strict (C' j) (c j) (newLevel Y H r.grade Q strict (B r.grade) t) w = V₀ r.grade j r.ringT by rwa [he] at p
 exact ⟨porchUp Y H V r.grade Q j strict (B r.grade) r.ringT t v, (trans_music ..).symm⟩
noncomputable def HAI (j:Axis):Set (J→Axis→ℝ):=⋃ r:L j,(V₀ r.grade j r.ringT).planeOK r.year
noncomputable def Globe := ⋃ j:Axis, HAI Y H V s Q Qt strict X C' c p j
local notation "pV"=> Globe Y H V s Q Qt strict X C' c p
local notation "HA" j:max=> HAI Y H V s Q Qt strict X C' c p j
local notation "T₀" u:max j:max=> V₀ (u).grade j (u).ringT
local notation "U" u:max=> T₀ u j
variable [DecidableEq J] -- only for chart continuity stuff; density over arbitrary labels I maybe anyway
lemma inner_open : ∃ t: Request Y H s Q strict X p j, (U r).planeOK r.year⊆ (U t).highway t.year:=by
 let t:=risingGrade Λ r.grade; have he:= rising_le Λ r.grade
 obtain ⟨g,hg⟩:= easement Y H V _ Q Qt j strict (C' j) (c j) (B r.grade) r.ringT
 have hz:=upward_levels Y H s Q strict X r.grade t r.good he
 suffices p':∃ w:Q₀ t j,(U r).planeOK r.year ⊆ (V₀ t j w).highway r.year by
    obtain ⟨w,pw⟩:=p'; exact ⟨⟨t,le_trans r.good he,w,r.year,r.check⟩,pw⟩
 rw [← hz]; exact ⟨g,hg r.year⟩ -- tune
lemma HAI_open : IsOpen (HA j):=by
 rw [show HA j = ⋃ u:L j,(U u).highway u.year from ?_]; swap
 · ext x; unfold HAI; constructor
   · intro t; obtain ⟨u,g⟩:= Set.mem_iUnion.mp t; obtain ⟨v,h⟩:= inner_open Y H V s Q Qt j strict X C' c p u; exact mem_iUnion.mpr ⟨v,h g⟩
   intro t; obtain ⟨u,p⟩:= Set.mem_iUnion.mp t; exact mem_iUnion.mpr ⟨u, (U u).plane_enough u.year p⟩
 exact isOpen_iUnion (fun u=>(U u).smooth_highway u.year)
lemma globe_open : IsOpen (pV) := isOpen_iUnion (fun j=> HAI_open Y H V s Q Qt j strict X C' c p)
variable (hn:p.Nodup)
include hi hn
lemma compatible (k:Axis) (y:L k)(w:fΛ) (v:w∈(U r).planeOK r.year)(g:w∈(T₀ y k).planeOK y.year) : (U r).reading r.year w=(T₀ y k).reading y.year w:=by
 let t:= max r.grade y.grade; obtain ⟨w',ht⟩:= larger Y H V s Q Qt j strict X C' c p r t (le_max_left ..)
 obtain ⟨u,h⟩:=larger Y H V s Q Qt k strict X C' c p y t (le_max_right ..); rw [← h] at g ⊢; rw [← ht] at v ⊢
 obtain ⟨q,r,x,hp,v,_⟩ := multi_open_chart Y H V t Q Qt j strict (C' j) (c j) (B t) w' r.year y.year u (C':=C' k) (f':=c k) (hi j k) (r.check.nodup_iff.mp hn) (r.check.symm.trans y.check) w v g
 exact v
omit hi hn
noncomputable def unify (u:fΛ) : ℂ:= if h:u∈pV then ((V₀ ((mem_iUnion.mp (mem_iUnion.mp h).choose_spec).choose.grade) (mem_iUnion.mp h).choose ((mem_iUnion.mp (mem_iUnion.mp h).choose_spec).choose.ringT))).reading ((mem_iUnion.mp (mem_iUnion.mp h).choose_spec).choose.year) u else 0 -- implicit index issue HAI def reductions
local notation "Ξ₀"=> unify Y H V s Q Qt strict X C' c p
include hi hn
lemma unified (u:fΛ)(g:u∈(U r).planeOK r.year) : Ξ₀ u=(U r).reading r.year u:=by
 have t:u∈ pV:= Set.mem_iUnion.mpr (show (∃ j:Axis,u∈ HA j) from ⟨j, mem_iUnion.mpr ⟨r,g⟩⟩); unfold unify; rw [dif_pos t]; exact (compatible Y H V s Q Qt j strict X C' c hi p r hn _ (mem_iUnion.mp (mem_iUnion.mp t).choose_spec).choose u g (mem_iUnion.mp (mem_iUnion.mp t).choose_spec).choose_spec).symm
lemma living_globe (x:fΛ)(h:x∈pV): ContinuousAt (Ξ₀) x:=by
 obtain ⟨k,h⟩:= Set.mem_iUnion.mp h; obtain ⟨v,h⟩:= Set.mem_iUnion.mp h
 obtain ⟨u,i⟩:= inner_open Y H V s Q Qt k strict X C' c p v; let X':= T₀ u k
 refine (X'.repertoire_cont u.year).continuousAt.congr ?_; filter_upwards [(X'.smooth_highway u.year).mem_nhds (show x∈ X'.highway u.year from i h)] with x g; exact (unified Y H V s Q Qt k strict X C' c hi p u hn x (X'.plane_enough u.year g)).symm
lemma globe_shift (u:fΛ) (t:Axis→ℝ)(h:u∈pV) : (fun i=> u i+t)∈ pV ∧ Ξ₀ (fun i=>u i+t)=Ξ₀ u:=by
 obtain ⟨k,h⟩:= Set.mem_iUnion.mp h; obtain ⟨v,g⟩:= Set.mem_iUnion.mp h; let B':= T₀ v k
 have he:= (B'.room_add v.year u t).mpr g
 refine ⟨Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨v,he⟩⟩,?_⟩; rw [unified Y H V s Q Qt k strict X C' c hi p v hn _ he,unified Y H V s Q Qt k strict X C' c hi p v hn u g]
 let L':=B'.sky; apply Repertoire.homogeneous B'; -- tune
 intro v
 let R':=peninsula Y H V Q Qt k strict (C' k) (c k); let V':= vocation Y H V Q Qt k strict (C' k) (c k)
 have he:v.val k=0:=v.property; have ht := compass_origin Y H V Q Qt k strict (C' k) (c k) v.val
 change R'.edge (v.val k) (R'.U (OS.Semigroup.SEP k v.val) V')=V' at ht; rw [he,R'.birth, show OS.Semigroup.SEP k v.val=v from ?_] at ht; swap;
 · apply Subtype.ext; change v.val-(v.val k) • basis k = _ -- syntax
   rw [he,zero_smul,sub_zero]
 change R'.U _ _ = _; rw [show B'.origin=(V':fort Y H V Q Qt k strict (C' k) (c k)) from Subtype.ext (vocate ..).symm]; exact ht
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.living_globe
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.globe_shift
