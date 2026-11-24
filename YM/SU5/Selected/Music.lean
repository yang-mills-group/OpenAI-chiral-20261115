import VerifiedSatinGroundInteraction
import YM.SU5.Selected.GlassLaw
import YM.SU5.Selected.Itinerary
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
local notation "L₀" => Λ.R.L.val
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
noncomputable def bandstand : Repertoire J j (timeMesh Λ) (indoor Y H V Q Qt j strict C f) := {
  sky:= mainsea Y H V Q Qt j strict C f
  sea:=ride Y H V Q Qt j strict C f
  match_time:=rfl
  glides:= follows_road Y H V Q Qt j strict C f
  op i:= Π (E₀ s (P' i).fwd (P' i).pos)
  light:=Ω
  grounded:= occupant_compass Y H V Q Qt j strict C f
  rise i := notch Μ s (P' i).rise
  width i:= notch Μ s (P' i).span
  bar i:= by change 0 < bell Μ s (P' i).span; rw [natural_time]; exact when_pos Μ _ _ (P' i).pos }
local notation "A₁" n:max p:max t:max => bandstand Y H V n Q Qt j strict C f p t
local notation "P₂" => A₁ s X P'
local notation "E'" b:max=> response Y H V b Q Qt j strict C f
local notation "θ" b:max x:max => show ℝ from ((notch Μ b x) : ℝ)
noncomputable def draft (Λ : Preparation) (s:ℕ) (f:J→ Cover) : J→ Axis→marks (timeMesh Λ) := fun i b=> notch (timeMesh Λ) s (f i b)
noncomputable def answersAt (l:List J) (f:J→ Cover) : Marks (tent Y H) strict:= (l.map (fun i=> relocateWorld Y H strict (f i) (X i))).prod
lemma answer_perm (l l':List J)(f':J→ Cover)(h:l.Perm l') : answersAt Y H strict X l f'= answersAt Y H strict X l' f':=by
 -- includes? uses V C intentionally if choose include; easier commutation direct
 unfold answersAt
 have he: ∀ v w : Marks (tent Y H) strict,v*w=w*v:= fun v w=> Subtype.ext (SlabMark.even_tests K (marksSpec strict v).1 (marksSpec strict w).1)
 -- choose induction
 let v:=fun i=> relocateWorld Y H strict (f' i) (X i)
 induction h with
 | nil=> rfl
 | cons i _ ih=> simp_rw [List.map_cons,List.prod_cons]; rw [ih]
 | swap a b l=> simp only [List.map_cons,List.prod_cons]; change v b * (v a* _)= v a* (v b *_); rw [←mul_assoc,←mul_assoc,he (v b)] -- potential rewrites others
 | trans _ _ i j=> rw [i,j]
local notation "D₀" l:max u:max=> answersAt Y H strict X l u
local notation "Q'" i:max=> P' i
local notation "u₀" u:max=> draft Λ s u
local notation "u₁" u:max=> Repertoire.clearAbove (draft Λ s u)
local notation "T₀" u:max x:max=> Vacancy.transport Y H s j strict T u x
variable (u':J→ Cover)(l':List J)
lemma enterfront (i:J): (P₂).frontend ((u₁ u') i) i= θ s (u' i j - (Q' i).rise):=by change bell Μ s (u' i j)-bell Μ s _= bell Μ s _; simp [bell]; ring
lemma enterend (i:J): (P₂).endline ((u₁ u') i) i= θ s (u' i j-(Q' i).rise+(Q' i).span):=by rw [endline,enterfront]; exact (bell_add ..).symm
lemma lilt (h : ℤ)(p:Repertoire.Correct (P₂) l' (Repertoire.Pages false) (u₁ u') (some (θ s h))) : ∃ i:𝔙 s,
    (P₂).stageList l' (u₀ u') [] (some (θ s h))= a₀ s i ∧ (D₀ l' u')=moveMark Y H j strict h ((M₁ s) i):=by
 induction l' generalizing h with
 | nil=> refine ⟨unity Y H j 0 strict s,by exact (root Y H V s Q Qt j strict C f).symm,Subtype.ext (relocate_unit ..).symm⟩ -- defeq eq membership
 | cons i l ih=>
    let n:= u' i j-(Q' i).rise; let G:= n+(Q' i).span
    have he : (P₂).frontend ((u₁ u') i) i= θ s n:= enterfront ..
    have hp : (P₂).endline ((u₁ u') i) i= θ s G:= enterend ..
    obtain ⟨x,r,v⟩ := ih G (hp ▸ p.2)
    let g:= (n-h).toNat
    have hw: h≤n:=by
       refine (bell_le Μ s ..).mp ?_; change (θ s h) ≤ θ s n; rw [←he]; exact p.1 _ rfl
    have hb: h+(g:ℤ)=n:=by unfold g; omega
    let q(k:Trans j):= u' i k.val; let V':= T₀ q (slabT Y H s j strict _ (Q' i).fwd (T₀ (-q) x))
    let y:= tick Y H s j 0 strict (2*g) V'; refine ⟨y,?_,?_⟩
    · have hg : (P₂).sep (some (θ s h)) i ((u₁ u') i)= θt s g:=by
         unfold sep; rw [he, ←hb]; change (bell Μ s (h+g)-bell Μ s h).toNNReal=_; rw [bell_add,natural_time,add_sub_cancel_left]; exact Real.toNNReal_coe
      have hv : ∀ k:Trans j, (- ((u₀ u') i) : placement Λ) k.val= notch Μ s (-q k) := fun i=> Subtype.ext (by change -bell Μ s (q i) = bell Μ s (-q i); rw [bell,bell]; simp)
      have hu (v0:𝔙 s) (q : Trans j→ℤ) (p0:placement Λ) (hp:∀ i:Trans j, p0 i.val = notch Μ s (q i)) : (P₂).forward p0 (a₀ s v0)= a₀ s (T₀ q v0):=by
         change (S).raw (look j) (fun i:Trans j=> p0 i.val) _= _; rw [funext hp]; exact roving Y H V s Q Qt j strict C f T v0 q
      rw [stageList]; -- reduce mark defeq
      change (R).E ((P₂).sep (some (θ s h)) i ((u₁ u') i)) ((P₂).forward _ ((Π (E₀ s (Q' i).fwd (Q' i).pos)) ((P₂).forward _ ((P₂).stageList l (u₀ u') [] (some ((P₂).endline ((u₁ u') i) i))))))=_
 -- blank
      rw [hp,hg,r,hu _ (-q) _ hv,slotted, hu _ q _ (fun _=>rfl),ride_ticks]
    apply Subtype.ext
    rw [answersAt, List.map_cons,List.prod_cons]; change (relocateWorld Y H strict _ _).val * (D₀ l u').val= relocate _ _ _ y.val; rw [v,world_val]
    unfold y V'; rw [paint Y H V s Q Qt j strict C X P' (u' i), hb, show n+(Q' i).rise-u' i j=0 by unfold n; omega]
    exact congrArg (fun t: Family K=> t*relocate K j G x.val) (relocate_zero K j (cad_paid K _ (marksSpec strict (X i)).1 (u' i))).symm

lemma lilt_free (p:(u₁ u') ∈ (P₂).planeOK l') : (P₂).ranking l' (u₀ u') []=(Ε s) (D₀ l' u'):=by
 -- choose artificial first b = front. p as above.
 suffices h:∃ h:ℤ,(P₂).stageList l' (u₀ u') [] none=(P₂).stageList l' (u₀ u') [] (some (θ s h))∧(P₂).Correct l' (Pages false) (u₁ u') (some (θ s h)) by
    obtain ⟨h,t,v⟩:=h; obtain ⟨i,m,g⟩:= lilt Y H V s Q Qt j strict C f X P' u' l' h v; rw [ranking,t,m,g,waiting]; exact call ..
 cases l' with
 | nil=>exact ⟨0,rfl,trivial⟩
 | cons i l=>
    let n:=u' i j-(P' i).rise; have he : (P₂).frontend ((u₁ u') i) i= θ s n:= enterfront ..
    refine ⟨n,?_,?_⟩; swap
    · refine ⟨fun x h=>?_,(show (P₂).Correct (i::l) (Pages false) (u₁ u') none from p).2⟩; rw [← Option.some.inj h]; exact he.ge
    rw [stageList,stageList]; congr 1
    have hp:(P₂).sep (some (θ s n)) i ((u₁ u') i)=(P₂).sep none i ((u₁ u') i):=by change ((P₂).frontend _ i-(θ s n)).toNNReal=0; rw [he,sub_self, Real.toNNReal_zero]
    exact congrArg (fun q:ℝ≥0=> (S).stackS [] ∘L ((R).E q) ∘L ((P₂).visiting ((P₂).op i) ((u₀ u') i))) hp.symm
section grade
variable (t : ℕ) (g:s≤ t)
noncomputable def newLevel (i:J) := upGrade Y H s Q strict (X i) t
local notation "B₀" => newLevel Y H s Q strict X t
noncomputable def porchUp (i:J) : Veranda Y H t j strict (newLevel Y H s Q strict X t i) := addLevel Y H V s Q j strict (P' i) t g
local notation "K₀"=> porchUp Y H V s Q j strict X P' t g
set_option maxHeartbeats 800000 in
lemma trans_music : (A₁ s X P')= (A₁ t B₀ K₀):=by
  have he(i:J): E₀ s (P' i).fwd (P' i).pos= E₀ t ((K₀) i).fwd ((K₀) i).pos:= Subtype.ext (allLevels Y H V s Q Qt j strict C _ t g)
  unfold bandstand; congr 1 -- order check
  all_goals first | rfl | (exact funext (fun i=> (notch_up Μ s t g (P' i).rise).symm)) | (exact funext (fun i=> congrArg (procession Y H V Q Qt j strict C f) (he i))) | skip
  funext i; change notch Μ s _= notch Μ t ((L₀^(t-s)*(P' i).span:ℕ):ℤ); push_cast; exact (notch_up Μ s t g _).symm
end grade
lemma played {u:J→Axis→marks Μ}(p: clearAbove u∈ (P₂).planeOK l')(t:ℕ)(g:s≤t)(h:draft Λ t u'=u): (P₂).ranking l' u [] = (Ε t) (answersAt Y H strict (newLevel Y H s Q strict X t) l' u') :=by
  subst u; rw [trans_music Y H V s Q Qt j strict C f X P' t g] at p ⊢
  exact lilt_free Y H V t Q Qt j strict C f _ _ u' l' p
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.played
