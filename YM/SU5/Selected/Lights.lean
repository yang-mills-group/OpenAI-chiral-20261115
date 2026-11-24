import VerifiedSatinGroundInteraction
import YM.SU5.Selected.Pangea
/-!
# Ring reserve applications: exact prices, every axes when in Pavilion
of all order proposals. Relate **the interaction in the phase** to the bought reading,
on all seats where data prove true physical applicability. (Still in CP4-5 Euclidean scheme.) -/
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
variable (C' : ∀ j, Arena Y H Q.circuit j 0 strict)(c:∀ j,(displayAlgebra Y H V Q Qt j strict (C' j)) →⋆ₐ[ℂ]ℂ)(hi:∀ j k s x,response Y H V s Q Qt j strict (C' j) (c j) x=response Y H V s Q Qt k strict (C' k) (c k) x)
variable (p:List J)
local notation "B" n:max=> newLevel Y H s Q strict X n
local notation "Z" j:max=> Arena Y H Q.circuit j 0 strict
local notation "V₀" n:max j:max b:max=> bandstand Y H V n Q Qt j strict (C' j) (c j) (B n) b
local notation "Q₀" t:max k:max=> ∀ i:J, Veranda Y H t k strict ((B t) i)
local notation "fΛ"=> J→Axis→ℝ
local notation "L" k:max=> Request Y H s Q strict X p k
variable (r: Request Y H s Q strict X p j)
local notation "pV"=> Globe Y H V s Q Qt strict X C' c p
local notation "HA" j:max=> HAI Y H V s Q Qt strict X C' c p j
local notation "T₀" u:max j:max=> V₀ (u).grade j (u).ringT
local notation "U" u:max=> T₀ u j
variable [DecidableEq J] -- only for chart continuity stuff; density over arbitrary labels I maybe anyway
noncomputable def pavilion := ⋂ i:Axis, HAI Y H V s Q Qt strict X C' c p i
local notation "P₀"=> pavilion Y H V s Q Qt strict X C' c p
local notation "Ξ₀"=> unify Y H V s Q Qt strict X C' c p
lemma cover_p (u:fΛ) (w:∀ j, u∈ HA j) : u∈ P₀∧ u∈pV:=⟨Set.mem_iInter.mpr w,Set.mem_iUnion.mpr ⟨(0:Axis),w 0⟩⟩
lemma pavilion_open : IsOpen (P₀):= isOpen_iInter_of_finite fun i=> HAI_open Y H V s Q Qt i strict X C' c p
include hi
variable (hn:p.Nodup)
include hn
-- compare after raising so we can use same underlying X and ALL its true evaluations
lemma pays_at (q:J→Axis→marks (timeMesh Λ)) (h : clearAbove q∈ P₀) (v:clearAbove q ∈ (U r).planeOK r.year) :
    Ξ₀ (clearAbove q)=(U r).ranking r.year q []:=by
 let V':= clearAbove q; choose K' hp using (fun j: Trans j=> Set.mem_iUnion.mp (Set.mem_iInter.mp h j.val))
 let p':=Finset.univ.sup (fun i:Trans j=> (K' i).grade); let n:= max p' r.grade
 obtain ⟨V₁,h₁⟩:= larger Y H V s Q Qt j strict X C' c p r n (le_max_right ..); have hu:clearAbove q∈ (V₀ n j V₁).planeOK r.year:=h₁.symm ▸ v
 rw [unified Y H V s Q Qt j strict X C' c hi p r hn _ v,← h₁]
 refine exact_multi_read Y H V n Q Qt j strict (C' j) (c j) (B n) V₁ r.year q (r.check.nodup_iff.mp hn) hu ?_
 intro i; obtain ⟨k,H'⟩:= larger Y H V s Q Qt i.val strict X C' c p (K' i) n ((Finset.le_sup (f:=fun i:Trans j=> (K' i).grade) (Finset.mem_univ i)).trans (le_max_left ..))
 exact ⟨C' i.val,c i.val,k,(K' i).year, hi j i.val, r.check.symm.trans (K' i).check, H'.symm ▸ hp i⟩

-- source-introduce
local notation "K'" k:max p:max=> bandstand Y H V s Q Qt k strict (C' k) (c k) X p
lemma pays_here (q : J→Axis→marks (timeMesh Λ))(l:List J)(g:p.Perm l)(v:clearAbove q ∈ (K' j P').planeOK l) : clearAbove q∈HA j ∧ (Ξ₀ (clearAbove q)=(K' j P').reading l (clearAbove q)) ∧
    (clearAbove q∈ P₀ → Ξ₀ (clearAbove q)= (K' j P').ranking l q []) :=by
  have h : ∃ X:Q₀ s j, (V₀ s j X)=(K' j P') :=by rw [startLevel Y H s Q strict X]; exact ⟨P',rfl⟩ -- possible issue pattern X binder
  obtain ⟨X₁,h⟩:=h; let W:Request Y H s Q strict X p j:= ⟨s,le_rfl,X₁,l,g⟩
  rw [←h] at v ⊢; exact ⟨Set.mem_iUnion.mpr ⟨W,v⟩, unified Y H V s Q Qt j strict X C' c hi p W hn _ v,fun q'=>pays_at Y H V s Q Qt j strict X C' c hi p W hn q q' v⟩

omit hi hn
section duals
-- explicit dyad. Left from mirror x, right future
noncomputable def dyad (x y:Marks (tent Y H) strict) : Bool→ Marks K strict:= Bool.rec (motive:=fun _=>_) x y
local notation "Δ" x:max y:max=> dyad Y H strict x y
local notation "OF" x:max=> futureMark Y H s j strict x
lemma duetPorch (x y:Tower.Field Y H s j 0 strict) :
    let l:= Δ ((Θ) (OF x)) (OF y)
    ∃ p:∀ i:Bool, Veranda Y H s j strict (l i), (0:Bool→Axis→ℝ) ∈ (bandstand Y H V s Q Qt j strict C f l p).planeOK [false,true]:=by
 intro l; obtain ⟨w,h,V',hx⟩:= artist_fits_slab Y H s j strict x; obtain ⟨u,d,t,hy⟩:= artist_fits_slab Y H s j strict y
 subst x y
 let v:Veranda Y H s j strict (OF V'.val):= ⟨0,_,h,V',(relocate_zero K j (marksSpec strict (OF V'.val)).1).symm⟩
 let p:Veranda Y H s j strict (l false):= verandStar Y H s j strict v
 let q:Veranda Y H s j strict (l true):= ⟨0,_,d,t,(relocate_zero K j (marksSpec strict (OF t.val)).1).symm⟩
 let X':= Bool.rec (motive:=fun i=>Veranda Y H s j strict (l i)) p q; refine ⟨X',by
   change Repertoire.Correct _ [false,true] (Pages false) _ _ -- argument l? tune order
   refine ⟨nofun,⟨fun i h'=>?_, trivial⟩⟩
   rw [← Option.some.inj h']; change 0-bell Μ s (w-0:ℤ)+bell Μ s (w:ℤ)≤0-bell Μ s 0; rw [sub_zero]; simp [bell]⟩
lemma zero_pay (x y:Marks (tent Y H) strict) : answersAt Y H strict (Δ x y) [false,true] 0=x*y:=by
 change (relocateWorld Y H strict 0 x)*(relocateWorld Y H strict 0 y*1) = _; rw [world_seed,world_seed,mul_one]
end duals

section cover
variable (Vc : ∀ j, Arena Y H Q.circuit j 0 false)(m:∀ j,(displayAlgebra Y H V Q Qt j false (Vc j)) →⋆ₐ[ℂ]ℂ)(hw:∀ j k s x,response Y H V s Q Qt j false (Vc j) (m j) x=response Y H V s Q Qt k false (Vc k) (m k) x)
open Spectral
local notation "VV"=>moveMark
variable (s0: ℝ)
variable (F:Marks (tent Y H) true)(z:SU.Slot)(S':Finset Cover)(o p₁ p₂:Cover)(u d:ℕ)
local notation "K₁" p:max=> relocateWorld Y H true p F
local notation "S₀" p:max => show Marks K false from bosonLabel K p
-- gauge-neutral dyad interpreted on resolving coordinates as both chart points
noncomputable def linkedPair := dyad Y H false (show Marks K false from bosonLabel K (mirrorInMarks Y H j true (relocateWorld Y H true p₁ F))) (show Marks K false from bosonLabel K (K₁ p₂))
local notation "P₀₀"=> linkedPair Y H j F p₁ p₂
local notation "K₀"=> (show List Bool from [false,true])
local notation "T'"=> pavilion Y H V s Q Qt false P₀₀ Vc m K₀
local notation "U₀"=> unify Y H V s Q Qt false P₀₀ Vc m K₀
local notation "Υ₀"=> response Y H V s Q Qt j false (Vc j) (m j) (S₀ ((mirrorInMarks Y H j true (relocateWorld Y H true p₁ F)) * (relocateWorld Y H true p₂ F)))
include hw
lemma foyer_price (v: Exceeds Y H V s Q Qt j (Vc j) (m j) s0 F z S' o u d p₁ p₂) :
    ((0:Bool→Axis→ℝ)∈ T') ∧ U₀ 0 = response Y H V s Q Qt j false (Vc j) (m j) (S₀ ((mirrorInMarks Y H j true (relocateWorld Y H true p₁ F)) * (relocateWorld Y H true p₂ F))) ∧
    (∀ᶠ v in 𝓝 (0:Bool→Axis→ℝ),v∈ T' ∧ (1/33:ℝ) ≤ ‖U₀ v‖):=by
 let W:= K₀; let y':=K₁ p₂; let x':= (mirrorInMarks Y H j true (relocateWorld Y H true p₁ F)); let R':=P₀₀
 let u':Bool→Axis→marks (timeMesh Λ):=draft Λ s (0:Bool→ Cover); have h0 : Repertoire.clearAbove u'=0:= by
    funext i v; change bell Μ s 0=0; simp [bell]
 have hp:=v.shelf
 let C₀:=response Y H V s Q Qt j false (Vc j) (m j); obtain ⟨x,y,f',g,_,hb⟩:= hp.zones
 have he:R'= dyad Y H false (mirrorInMarks Y H j false (futureMark Y H s j false x)) (futureMark Y H s j false y):= congrArg₂ (dyad Y H false) (Subtype.ext ((congrArg (mirror K j 0) f').symm)) (Subtype.ext g.symm)
 have hz(i:Axis) : ∃ p:∀ j':Bool,Veranda Y H s i false (R' j'), (clearAbove u') ∈ (bandstand Y H V s Q Qt i false (Vc i) (m i) R' p).planeOK [false,true]:=by
    by_cases h:i=j; · subst i; rw [he,h0]; apply duetPorch ..
    obtain ⟨a,b,hm,hZ,hy⟩:= hb i (Vc i) h
    rw [he,h0,show mirrorInMarks Y H j false (futureMark Y H s j false x)=mirrorInMarks Y H i false (futureMark Y H s i false a) from Subtype.ext hZ, show futureMark Y H s j false y=futureMark Y H s i false b from Subtype.ext hy]
    apply duetPorch ..
 choose X₁ HX using hz
 have h(i):= pays_here Y H V s Q Qt i false R' (X₁ i) Vc m hw W (by change List.Nodup [false,true]; decide) u' [false,true] (List.Perm.refl _) (HX i) -- include hw binder
 obtain ⟨g,i₁⟩ := cover_p Y H V s Q Qt false R' Vc m W (clearAbove u') (fun i=> (h i).1);
 have ht : U₀ 0=C₀ (S₀ (x'*y')):= by
    rw [← h0,(h j).2.2 g,lilt_free Y H V s Q Qt j false (Vc j) (m j) R' (X₁ j) (0:Bool→ Cover) [false,true] (HX j)] -- defeq u' maybe rw
    unfold R'; rw [linkedPair,zero_pay]; rfl
 rw [h0] at g i₁; refine ⟨g,ht,?_⟩; let H':=pavilion_open Y H V s Q Qt false R' Vc m W
 have h' : ContinuousAt (U₀) (0:Bool→Axis→ℝ):= living_globe Y H V s Q Qt false R' Vc m hw W (by change List.Nodup [false,true]; decide) _ i₁
 have hz:1/33 < ‖U₀ 0‖:= lt_of_lt_of_le (show (1/33:ℝ)<1/32 by norm_num) (ht.symm ▸ v.shelf.consumption)
 filter_upwards [H'.mem_nhds g,(h'.norm.tendsto.eventually (lt_mem_nhds hz))] with i u w; exact ⟨u,w.le⟩
end cover
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.pays_at
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.foyer_price
