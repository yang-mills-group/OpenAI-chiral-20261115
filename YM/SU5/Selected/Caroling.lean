import YM.SU5.Selected.Itinerary
/-!
# CP5. Average independently per position, to implant a common-axis projector
*in every gap*. Order can be arbitrary using this technique. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric NormedSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy ContinuousLinearMap
open scoped Topology InnerProductSpace NNReal ENNReal
variable {I : Type*}{a:Axis}{M:Mesh}{H:Hilbert} (X: Repertoire I a M H)
namespace Repertoire
local notation "V"=> Axis → ℝ
local notation "P"=> X.sky.track
local notation "Ω" => X.light
local notation "E" i:max=> X.sea.E i
local notation "B"=> {b:Axis//b ≠ a}
local notation "A" i:max => X.op i
local notation "U" i:max v:max=> (X.sky.track.crew i).play v
local notation "Γ"=> marks M
local notation "K"=> X.sky.list
local notation "π" i:max=> ((P).stackS i)
local notation "Λ"=> (Axis→ Γ)
local notation "ρ" x:max=> ((x:marks M):ℝ)
local notation "ι" t:max=> show Axis→ℝ from fun i=> ρ (t i)
open Filming
local notation "Γ'"=> marks M
local notation "Ω'"=> X.light
local notation "W" x:max p:max j:max=> Function.update x (p:B).val (j+x (p:B).val)
lemma front_shift (u:Λ)(p:B)(t:Γ) : X.forward (W u p t)=(U p t).comp (X.forward u) :=by
  have he : (fun i:B=> (W u p t) i.val)= Function.update (0:B→Γ) p t+(fun i:B=>u i.val) := by
     funext i; by_cases h:i=p; · subst i; rw [Function.update_self,Pi.add_apply,Function.update_self]
     rw [Function.update_of_ne (show i.val≠ p.val from fun e=>h (Subtype.ext e)),Pi.add_apply,Function.update_of_ne h,Pi.zero_apply,zero_add]
  unfold forward; rw [he, Alliance.travelR,spotlight (P) (K) X.sky.unique_list (X.sky.traverses _)]
lemma visiting_side (l:List B)(x:Option ℝ)(i:I)(u:Λ)(p:B)(t:Γ): X.striding l x i (W u p t)=(U p t) ∘L X.striding l x i u ∘L (U p (-t)):=by
  have hv : -(W u p t : Λ)=W (-u) p (-t):=funext (fun j:Axis=>by by_cases v:j=p.val <;> simp [Function.update,v] <;> try abel)
  unfold striding visiting
  have hx: X.sep x i (ι (W u p t))= X.sep x i (ι u):=by rcases x with _|x; rfl; simp [sep,frontend,Function.update_of_ne p.property.symm] -- tune
  let z:= X.sep x i (ι u)
  rw [hx,hv,X.front_shift,X.front_shift]
  have he: (U p (-t)).comp (X.forward (-u))=(X.forward (-u)).comp (U p (-t)):= (Alliance.hard _ _ _ (fun j _ p'=> (P).cCom j p p' _) _).symm
  have hp: (U p t).comp ((π l).comp (E z))=((π l).comp (E z)).comp (U p t):= (Alliance.slide _ _ _ ((P).ground l (U p t) (fun j _ t'=> (P).cCom ..)).symm (X.glides p t z).symm).symm
  rw [he]; ext1 y; change (π l) ((E z) ((U p t) _))=(U p t) ((π l) ((E z) _)); exact congrArg (fun f:H.Op=>f ((X.forward u) ((A i) ((X.forward (-u)) ((U p (-t)) y))))) hp.symm
lemma forward_line (u:Λ)(p:B)(t:Γ)(i:I): X.endline (ι (W u p t)) i= X.endline (ι u) i:= by dsimp [endline,frontend]; rw [Function.update_of_ne p.property.symm]
lemma stages_abide {u v:I→Λ}(l:List I)(p:∀ i∈l,u i=v i)(t:List B)(b:Option ℝ) : X.stageList l u t b=X.stageList l v t b:=by induction l generalizing b with
 | nil=> rfl
 | cons i l ih=> rw [stageList,stageList, p i (List.Mem.head ..), ih (fun i v=>p i (List.Mem.tail _ v))]
lemma stage_keeper (u:I→Λ)(l:List I)(k:B)(t:List B)(b:Option ℝ) : X.stageList l u (k::t) b∈ (X.sky.track.crew k).lives H:=by
 cases l with
 | nil=> exact (Alliance.assembled ..).mp X.grounded k (X.sky.traverses _)
 | cons i l=> exact (Alliance.assembled ..).mp ((X.sky.track).planted (k::t) _) _ (List.Mem.head ..)
variable [Fintype I][DecidableEq I]
local notation "V'" n:max=> Filming.Cell M n
local notation "S" s:max q:max => fun i:I=> pebbles M s (q i)
local notation "Y" u:max p:max n:max q:max=> swipe I u (p:B).val (S n q)
noncomputable def posters (l: List I)(u:I→Λ)(t:List B)(b:Option ℝ)(k:B)(n:ℕ×ℕ) : H:= Average.center (fun i : I→ Cell M n => X.stageList l (Y u k n i) t b)
lemma cups (l:List I)(i:I)(h:i∉l)(u:I→Λ)(t:List B)(b:Option ℝ)(k:B)(n:ℕ×ℕ) : X.posters (i::l) u t b k n=
    displaced M ((P).crew k) (X.striding t b i (u i)) n (X.posters l u t (some (X.endline (ι (u i)) i)) k n):=by
  -- average along chosen stamp and all others; use Axis-like splitting. Fintype instance caveat
  haveI := avg_lives M n.2; let v := Classical.choice (avg_lives M n.2); let p:=(V' n × (Average.Other I i → V' n)); let P':= (P).crew k -- notation V'.
  let Z(z: Filming.Cell M n) (b: Average.Other I i → Filming.Cell M n) := (Equiv.funSplitAt i _).symm (z,b)
  let b':= some (X.endline (ι (u i)) i); let T(q:I→ Filming.Cell M n):= X.stageList l (Y u k n q) t b'
  have he (z:Filming.Cell M n)(q: Average.Other I i→ Filming.Cell M n): T (Z z q)= T (Z v q):=by
     apply X.stages_abide; intro j hj; have h' : j≠i:=fun h' => h (h' ▸ hj)
     dsimp only [swipe]; unfold Z; simp [h']
  have point (T:(I→Cell M n)→H) : Average.center T=Average.center (fun x:Cell M n=>Average.center (fun y:Average.Other I i→Cell M n=> T (Z x y))):=by unfold Z; rw [← Average.trade (Equiv.funSplitAt i (Filming.Cell M n)).symm T, Average.domino] -- rw changes T under lambda? 
  have hp : X.posters l u t b' k n= Average.center (fun i:Average.Other I i → Filming.Cell M n=> T (Z v i)):=by
  -- blank 
     change Average.center T=_; rw [point]; simp_rw [he,Average.constant]
  let F(z: Filming.Cell M n):= P'.play (pebbles M n z) ∘L X.striding t b i (u i) ∘L P'.play (- pebbles M n z)
  have hz(z: Filming.Cell M n) (q : Average.Other I i → Filming.Cell M n): X.stageList (i::l) (Y u k n (Z z q)) t b = F z (T (Z v q)):=by
     rw [stageList,show ((Y u k n (Z z q)) i)= _ from (show (Y u k n (Z z q)) i=W (u i) k (pebbles M n z) from congrArg (fun s:Filming.Cell M n=> W (u i) k (pebbles M n s)) (by simp [Z])),X.forward_line, X.visiting_side]
     rw [← he z q]
  rw [displaces,hp,posters, point]
  refine congrArg Average.center (funext (fun z=>?_)); change Average.center (fun q=> X.stageList (i::l) (Y u k n (Z z q)) t b)=F z _; simp_rw [hz, Average.natural]
lemma reel (u:I→Λ)(l:List I)(p:l.Nodup)(b:Option ℝ)(t:List B)(k:B) : Tendsto (fun i=> X.posters l u t b k i) horizon (𝓝 (X.stageList l u (k::t) b)):=by
 induction l generalizing b with
 | nil=> exact tendsto_const_nhds.congr (fun i=> by haveI:= avg_lives M i.2; apply Eq.symm (Average.constant _))
 | cons i l ih=>
    obtain ⟨p,h⟩:= List.nodup_cons.mp p
    have hp: X.striding (k::t) b i (u i)= ((P).crew k).pi_c ∘L X.striding t b i (u i):=by unfold striding; rw [Alliance.shel_step]; rfl
    simp_rw [cups _ l i p]; rw [stageList,hp]; exact transports M ((P).crew k) (X.striding t b i (u i)) _ _ (ih h _) (X.stage_keeper ..)
lemma screening (u:I→Λ)(l:List I)(p:l.Nodup)(t:List B)(k:B) : Tendsto (fun s=> Average.center (fun i : I→ Cell M s=> X.ranking l (Y u k s i) t)) horizon (𝓝 (X.ranking l u (k::t))) :=by
  unfold ranking; have he(s:ℕ×ℕ): Average.center (fun i:I→Cell M s=> inner ℂ Ω (X.stageList l (Y u k s i) t none))=inner ℂ Ω (X.posters l u t none k s):= Average.natural _ (innerSL ℂ Ω); simp_rw [he]
  exact tendsto_const_nhds.inner (X.reel u l p none t k)
lemma filmed (u:I→Λ)(l:List I)(p:l.Nodup)(t:List B)(k:B)(e:ContinuousAt (fun r:I→Γ=> X.ranking l (swipe I u k.val r) t) 0): X.ranking l u (k::t)= X.ranking l u t:=by
  have h:= tendsto_nhds_unique (X.screening u l p t k) (crumbs_limit M (fun r:I→Γ=> X.ranking l (swipe I u k.val r) t) e)
  rw [swipe_birth] at h; exact h
end Repertoire
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Repertoire.screening
#print axioms YM.SelectionAnalysis.Repertoire.filmed
