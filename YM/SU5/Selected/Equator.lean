import VerifiedSatinGroundInteraction
import YM.SU5.Selected.Music
import YM.SU5.Selected.Trestle
import YM.SU5.Selected.Epoch
/-!
# CP5. Euclidean multi-chart comparison

Includes all weak-boundary points of these charts. Presupposes genuine common underlying χ across axes and
SAME named marks of this resolution. No rotation symmetry used or concluded. On single chart, comparisons on CHAR family still including that UP grade.
-/
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
local notation "A₁" n:max p:max t:max => bandstand Y H V n Q Qt j strict C f p t
local notation "P₂" => A₁ s X P'
local notation "E'" b:max=> response Y H V b Q Qt j strict C f
local notation "θ" b:max x:max => show ℝ from ((notch Μ b x) : ℝ)
local notation "θₙ" n:max p:max=> show ℝ from ((notch (timeMesh Λ) n p):ℝ)
local notation "n₀"=> risingGrade Λ s
local notation "N₀"=> newLevel Y H s Q strict X n₀
local notation "K₀"=> porchUp Y H V s Q j strict X P' n₀ (rising_le Λ s)
local notation "L₀" p:max=> bandstand Y H V (risingGrade Λ s) Q Qt j strict C f N₀ p
-- naming CV
variable [DecidableEq J]
/-- Tight chart guarantee. Corresponding Repertoire may use *other* operators on full H,
so prove evaluation comparisons separately. -/
lemma easement : ∃ z : ∀ i, Veranda Y H (risingGrade Λ s) j strict ((N₀) i), ∀ l:List J,(P₂).planeOK l ⊆ (L₀ z).highway l:=by
  choose q h v using fun i:J=> (glissade Y H V s Q j strict (F:=X i) (P' i))
  refine ⟨q,fun l=>?_⟩; rw [trans_music Y H V s Q Qt j strict C f X P' n₀ (rising_le Λ s)]; apply Repertoire.encloses
  · intro i u; specialize h i; specialize v i; change (q i).rise+1=((K₀) i).rise at h; change (q i).span+1=((K₀) i).span at v
    change u j-bell Μ n₀ (((K₀) i).rise)+ bell Μ n₀ (((K₀) i).span) = u j-bell Μ n₀ ((q i).rise)+bell Μ n₀ ((q i).span)
    rw [←h,←v,Nat.cast_add_one,bell_add,bell_add]; ring
  intro i u; specialize h i; change (q i).rise+1=((K₀) i).rise at h; change u j-bell Μ n₀ (((K₀) i).rise) < u j-bell Μ n₀ ((q i).rise); rw [←h,bell_add]; exact (sub_lt_sub_iff_left _).2 (lt_add_of_pos_right _ (show 0<bell Μ n₀ 1 from (by unfold bell; rw [Int.cast_one,one_mul]; exact mill_pos ..))) -- variable L notation conflit

lemma compose_common (u:J→Axis→marks (timeMesh Λ)) : ∃ (t:ℕ)(f:J→ Cover), s ≤ t ∧ draft Λ t f=u:=by
  choose a p v using fun i: J×Axis=> (notch_exists Μ (u i.1 i.2))
  let t:=max s (Finset.univ.sup a)
  refine ⟨t,fun i k=>castor Μ (a (i,k)) t (p (i,k)), le_max_left .., funext fun i=>funext fun k=>?_⟩; change notch Μ t (castor Μ _ _ _)=_; rw [notch_up Μ _, v]; exact (Finset.le_sup (f:=a) (Finset.mem_univ _)).trans (le_max_right ..) -- tune M greek
local notation "B" n:max => (Ε n)
variable (p q: List J)
variable {j' : Axis}{C':Arena Y H Q.circuit j' 0 strict}{f' : (displayAlgebra Y H V Q Qt j' strict C')→⋆ₐ[ℂ]ℂ}
local notation "B'" n:max=> response Y H V n Q Qt j' strict C' f'
local notation "W₁" n:max x:max p:max=> bandstand Y H V n Q Qt j' strict C' f' x p
local notation "Ω₀'"=> (P₂).highway p
variable (K' : ∀ i, Veranda Y H s j' strict (X i))
local notation "P₃" => W₁ s X K'
lemma mixed_scores_cohere (h:∀ s F, (B s) F=(B' s) F)(v0:p.Perm q)(u:J→Axis→marks (timeMesh Λ)) (x: clearAbove u∈ (P₂).planeOK p) (y: clearAbove u∈(P₃).planeOK q) : (P₂).ranking p u []=(P₃).ranking q u []:=by
 obtain ⟨t,z,v,r⟩:= compose_common s u
 rw [played Y H V s Q Qt j strict C f X P' z p x t v r,played Y H V s Q Qt j' strict C' f' X K' z q y t v r,answer_perm Y H strict (newLevel Y H s Q strict X t) p q z v0,h]
lemma extension_pair (h:∀ s F,(B s) F=(B' s) F)(hp:p.Nodup)(w:p.Perm q) (t:Set (J→Axis→ℝ))(v:IsOpen t)(x:t⊆ (P₂).planeOK p)(y:t⊆ (P₃).planeOK q) : EqOn ((P₂).reading p) ((P₃).reading q) (closure t) := by
  exact Repertoire.Sharing.smooth P₂ P₃ p q hp (w.nodup_iff.mp hp) t v (fun i a=>mixed_scores_cohere Y H V s Q Qt j strict C f X P' p q K' h w i (x a) (y a))
lemma connection_left (hp:p.Nodup) (p' : ∀ i, Veranda Y H (risingGrade Λ s) j strict ((N₀) i)) (x: (P₂).planeOK p⊆ (L₀ p').highway p): EqOn ((P₂).reading p) ((L₀ p').reading p) ((P₂).planeOK p):=by
  let X':= L₀ p'; have he :(P₂)= (L₀ K₀):= trans_music ..
  rw [he] at x ⊢; exact (extension_pair Y H V n₀ Q Qt j strict C f N₀ K₀ p p p' («C'»:=C) (f':=f) (fun _ _=>rfl) hp (List.Perm.refl _) _ ((L₀ K₀).smooth_highway p) ((L₀ K₀).plane_enough p) (((L₀ K₀).plane_enough p).trans (x.trans ((L₀ p').plane_enough p)))).mono ((L₀ K₀).gap_area p hp)
theorem multi_open_chart (h:∀ s F,(B s) F=(B' s) F)(hp:p.Nodup)(w:p.Perm q) (u:J→Axis→ℝ) (x:u∈(P₂).planeOK p) (y:u∈(P₃).planeOK q) :
     ∃ (A':∀ i, Veranda Y H (risingGrade Λ s) j strict (newLevel Y H s Q strict X (risingGrade Λ s) i)) (C'':∀ i, Veranda Y H (risingGrade Λ s) j' strict (newLevel Y H s Q strict X (risingGrade Λ s) i)),
       ((P₂).planeOK p ⊆ (L₀ A').highway p) ∧ ((P₃).planeOK q⊆ (W₁ n₀ N₀ C'').highway q) ∧
         ((P₂).reading p u=(P₃).reading q u) ∧ EqOn ((L₀ A').reading p) ((W₁ n₀ N₀ C'').reading q)
           (closure ((L₀ A').highway p ∩ (W₁ n₀ N₀ C'').highway q)) ∧
         IsOpen ((L₀ A').highway p ∩ (W₁ n₀ N₀ C'').highway q) ∧ u ∈ ((L₀ A').highway p ∩ (W₁ n₀ N₀ C'').highway q):=by
   obtain ⟨a,r⟩:= easement Y H V s Q Qt j strict C f X P'; obtain ⟨b,uV⟩:= easement Y H V s Q Qt j' strict C' f' X K'
   have ht : IsOpen ( (L₀ a).highway p ∩ (W₁ n₀ N₀ b).highway q):= ((L₀ a).smooth_highway p).inter ((W₁ n₀ N₀ b).smooth_highway q)
   let V₀:= (L₀ a).highway p ∩ (W₁ n₀ N₀ b).highway q; have hp0:u∈V₀:=⟨r p x,uV q y⟩
   have hv:= extension_pair Y H V n₀ Q Qt j strict C f N₀ a p q b (C':=C') (f':=f') h hp w V₀ ht (Set.Subset.trans (Set.inter_subset_left ..) ((L₀ a).plane_enough p)) ((Set.inter_subset_right ..).trans ((W₁ n₀ N₀ b).plane_enough q))
   exact ⟨a,b,r p,uV q,(connection_left Y H V s Q Qt j strict C f X P' p hp a (r p) x).trans ((hv (subset_closure hp0)).trans (connection_left Y H V s Q Qt j' strict C' f' X K' q (w.nodup_iff.mp hp) b (uV q) y).symm), hv,ht,hp0⟩

/- Full affordance in ANY order (per-axis, potentially different order), even including
 Euclidean boundary points: exact raw survival after projecting for such a set of placements. -/
abbrev chartCover (u:J→Axis→ℝ) :Prop:=∀ k: Trans j, ∃ (C' : Arena Y H Q.circuit k.val 0 strict) (U: (displayAlgebra Y H V Q Qt k.val strict C') →⋆ₐ[ℂ]ℂ) (Z:∀ i,Veranda Y H s k.val strict (X i)) (r:List J), (∀ s x, (B s) x=response Y H V s Q Qt k.val strict C' U x) ∧ p.Perm r ∧ u ∈ (bandstand Y H V s Q Qt k.val strict C' U X Z).planeOK r

lemma exact_multi_read (q : J→ Axis→marks (timeMesh Λ)) (hp:p.Nodup) (hu: clearAbove q ∈ (P₂).planeOK p) (s':chartCover Y H V s Q Qt j strict C f X p (clearAbove q)) :
     (P₂).reading p (clearAbove q)=(P₂).ranking p q []:=by
 choose C₁ U V' r e t k using s'
 let N(k:Trans j)(b:∀ i,Veranda Y H n₀ k.val strict ((N₀) i)):= bandstand Y H V n₀ Q Qt k.val strict (C₁ k) (U k) N₀ b
 choose Pp b using fun i:Trans j => easement Y H V s Q Qt i.val strict (C₁ i) (U i) X (V' i)
 obtain ⟨a,u⟩:= easement Y H V s Q Qt j strict C f X P'
 let Bq:= (L₀ a).highway p; let G(i:Trans j):= (N i (Pp i)).highway (r i); let D:=Bq ∩ ⋂ i:Trans j,G i
 have he:IsOpen D:= (Repertoire.smooth_highway ..).inter (isOpen_iInter_of_finite (fun i:Trans j=> Repertoire.smooth_highway ..))
 have hd:clearAbove q∈D:=⟨u p hu, mem_iInter.mpr (fun i=>b i (r i) (k i))⟩
 rw [connection_left Y H V s Q Qt j strict C f X P' p hp a (u p) hu, reading_exact];
 have hg:= family_sync (L₀ a) p hp D he (fun i=>?_); swap; · exact ⟨_,N i (Pp i),r i,fun v w=> mixed_scores_cohere Y H V n₀ Q Qt j strict C f N₀ a p (r i) (Pp i) («C'»:=_) (f':=U i) (e i) (t i) v ((L₀ a).plane_enough p w.1) ((N i (Pp i)).plane_enough (r i) (Set.mem_iInter.mp w.2 i))⟩
 refine Eq.trans (hg _ q hd) ?_
 have ht:(P₂)=(L₀ K₀):= trans_music ..; rw [ht]; rw [ht] at hu -- also hidden K old at lhs? need
 exact mixed_scores_cohere Y H V n₀ Q Qt j strict C f N₀ a p p K₀ (f':=f) (fun _ _=>rfl) (List.Perm.refl _) q ((L₀ a).plane_enough p hd.1) hu
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.easement
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.multi_open_chart
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.exact_multi_read
