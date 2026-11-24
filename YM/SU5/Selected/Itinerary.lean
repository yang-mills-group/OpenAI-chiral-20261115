import YM.SU5.Selected.Mingle
import YM.SU5.Selected.Filming
/-!
# Chart itineraries

Thick storage supports (& *actual* costs) vs open configuration continuations. Does
not make the order global. No duplicate-free required on physical observables; identifiers
should be fresh **per occurrence**. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric NormedSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy ContinuousLinearMap
open scoped Topology InnerProductSpace NNReal ENNReal
structure Repertoire (I : Type*) (a : Axis) (M:Mesh) (H:Hilbert) where
  sky : Sunbelt a (marks M) H
  sea : OS.Semigroup H a
  match_time : sky.heat=sea.E
  glides : ∀ (k:{b:Axis//b≠a}) (v:marks M)(t:ℝ≥0), ((sky.track.crew k).play v).comp (sea.E t)=(sea.E t).comp ((sky.track.crew k).play v)
  rise : I→ marks M
  width : I→ marks M
  bar i : 0 < (width i : ℝ)
  op : I → H.Op
  light : H
  grounded : light ∈ sky.track.aviator sky.list
  -- will ↑ ground and time invariant needed elsewhere
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
abbrev frontend (w:V)(i:I) :ℝ:= w a-(X.rise i:ℝ)
abbrev endline(w:V)(i:I):ℝ:= X.frontend w i+(X.width i :ℝ)
def Correct (l:List I) (S : Set (ℝ×ℝ))(q:I→ V)(t:Option ℝ) : Prop:= match l with
 | []=> True
 | i::l=> (∀ x:ℝ, t=some x → (x,X.frontend (q i) i)∈S) ∧ Correct l S q (some (X.endline (q i) i))
def Pages (v:Bool) : Set (ℝ×ℝ):= if v then {x|x.1<x.2} else {x|x.1≤x.2}
noncomputable def highway (t:List I) := {q : I → V | X.Correct t (Pages true) q none}
noncomputable def planeOK (t:List I) := {q : I → V | X.Correct t (Pages false) q none}
lemma smooth_highway (l : List I) : IsOpen (X.highway l):=by
 have h0(z:Option ((I→V) → ℝ)) (pz:∀ g,z=some g→ Continuous g) : IsOpen {q:I→V | X.Correct l (Pages true) q (z.map fun f=> f q)}:=by
    induction l generalizing z with
    | nil=> simp [Correct]
    | cons i t ih=>
       let f(u:I→V):= X.frontend (u i) i; let g(u:I→V):= X.endline (u i) i
       have hf:Continuous f:=by unfold f frontend; fun_prop
       have hg:Continuous g:=hf.add continuous_const
       have ht: IsOpen {q:I→V| X.Correct t (Pages true) q (some (g q))}:=ih (some g) (by simpa using hg)
       rcases z with _|p; · simpa [Correct,g] using ht
       simp only [Option.map_some]; rw [show {q:I→V | X.Correct (i::t) (Pages true) q (some (p q))} = {q:I→V|p q<f q} ∩ {q:I→V|X.Correct t (Pages true) q (some (g q))} from ?_]; swap; · ext i; simp [Correct,f,g,Pages,eq_comm]
       exact (isOpen_lt (pz p rfl) hf).inter ht
 exact h0 none (by simp)
lemma plane_enough (l : List I) : X.highway l ⊆ X.planeOK l:=by
  have he(q:I→V)(t:Option ℝ): X.Correct l (Pages true) q t→ X.Correct l (Pages false) q t:=by
     induction l generalizing t with
     | nil=>exact _root_.id
     | cons i l ih=> exact fun v=> ⟨fun x h=> le_of_lt (show x<X.frontend (q i) i from v.1 x h),ih _ v.2⟩
  exact fun q h=> he q none h
lemma insensitive (t:List I)(u v:I→ V)(h:∀ i,u i a=v i a)(b:Bool): u∈(if b then X.highway t else X.planeOK t) ↔ v∈(if b then X.highway t else X.planeOK t):= by
  suffices p : ∀ w s, X.Correct t s u w= X.Correct t s v w by cases b; all_goals simpa [highway,planeOK,p]
  intro w s; induction t generalizing w with
  | nil=>rfl
  | cons i t ih=> simp only [Correct,ih,endline,frontend,h]

abbrev sep (t : Option ℝ)(i:I)(u:V) : ℝ≥0:= match t with
 | none=>0
 | some r=> (X.frontend u i-r).toNNReal
noncomputable def forward (u:Λ):H.Op:= (P).raw X.sky.list (fun i=> u i.val)
noncomputable def visiting (f : H.Op)(u:Λ) : H.Op := X.forward u ∘L f ∘L X.forward (-u)
local notation "Ξ" l:max b:max i:max u:max=> (π l) ∘L (E (X.sep b i (ι u))) ∘L X.visiting (X.op i) u
noncomputable def striding (l: List B)(b:Option ℝ)(i:I)(u:Λ) : H.Op:= Ξ l b i u
noncomputable def stageList (l:List I)(u:I→Λ)(t:List B)(b:Option ℝ): H := match l with
 | []=>X.light
 | i::w=> X.striding t b i (u i) (stageList w u t (some (X.endline (ι (u i)) i)))
noncomputable def ranking (l:List I)(u:I→Λ)(t:List B) : ℂ:= inner ℂ Ω (X.stageList l u t none)
lemma step_permutation (l v:List B)(h:l.Perm v)(t:List I)(x:I→Λ) : X.ranking t x l=X.ranking t x v:=by
 suffices p: ∀ b:Option ℝ, X.stageList t x l b=X.stageList t x v b by
   change inner ℂ _ _ = _; rw [p]; rfl
 intro b; induction t generalizing b with
 | nil=>rfl
 | cons i t ih=>rw [stageList,stageList,ih]; unfold striding; rw [overlay_all (P) l v h]
noncomputable def clearAbove (x : I→Λ) : I→V := fun i=> (ι (x i))
-- time continuity, uses t clipping so doesn't even require ordering here
lemma heat_cont {D : Hilbert} {a:Axis} (S : OS.Semigroup D a) {T:Type*} [TopologicalSpace T] (q:T→ℝ≥0)(f:T→ D)(t:Continuous q)(h:Continuous f) : Continuous (fun i=> S.E (q i) (f i)):=by
  apply continuous_iff_continuousAt.mpr; intro i
  let g(j:T):= S.E (q j) (f i); have hg : Continuous g:= (S.continuousE _).comp t
  apply tendsto_of_tendsto_of_dist (hg.continuousAt (x:=i)).tendsto
  refine squeeze_zero' (g:=fun s=> ‖f i-f s‖) (Eventually.of_forall fun _=> dist_nonneg) (Eventually.of_forall fun u:T=> ?_) ?_
  · rw [dist_eq_norm]; unfold g; rw [←map_sub]; exact ((S.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg (f i-f u)) (S.shrinks _)) -- norm → squeeze force
  simpa using tendsto_const_nhds (x:=f i)|>.sub ((h.tendsto i))|>.norm
abbrev swipe (I:Type*) {M:Mesh} (x:I→Axis→marks M)(j:Axis)(p:I→marks M) : I→Axis→marks M :=fun i=> Function.update (x i) j (p i+x i j)
lemma swipe_birth (x:I→Λ)(j:Axis) : swipe I x j 0=x:=by funext i; change Function.update (x i) j (0+x i j)= _; rw [zero_add,Function.update_eq_self]
attribute [local simp] swipe_birth
lemma forward_time (u:Λ)(p:Γ) : X.forward (Function.update u a p)=X.forward u:= congrArg ((P).raw X.sky.list) (funext fun i:B=> Function.update_of_ne i.property ..)
lemma motionless (u:Λ)(p:Γ)(f:H.Op): X.visiting f (Function.update u a p)=X.visiting f u:=by
 unfold visiting; rw [X.forward_time]; rw [show -(Function.update u a p : Λ)= Function.update (-u) a (-p) from funext (fun i:Axis=> by by_cases v:i=a <;> simp [Function.update,v]),X.forward_time]
lemma smooth_temporal {D:Type*}[TopologicalSpace D](u:D→V)(p:D→ℝ)(t:Continuous (fun i:D=>u i a))(h:Continuous p)(i:I) : Continuous (fun x:D=> X.sep (some (p x)) i (u x)):= continuous_real_toNNReal.comp ((t.sub continuous_const).sub h)
lemma temporal (l:List I)(u:I→Λ)(t:List B) : Continuous (fun v:I→Γ=> X.ranking l (swipe I u a v) t):=by
  let P'(v:I→Γ):= swipe I u a v; let S:= X.sea
  have p(i:I) : Continuous (fun v:I→Γ=> (P' v i a).val):=by
     unfold P' swipe; simp_rw [Function.update_self]; exact continuous_subtype_val.comp ((continuous_apply _).add continuous_const)
  suffices h : ∀ b:Option ((I→Γ)→ℝ),(∀f,b=some f→Continuous f)→ Continuous (fun v:I→Γ=> X.stageList l (P' v) t (b.map fun f=> f v)) by exact continuous_const.inner (h none (by simp))
  intro b c ; induction l generalizing b with
  | nil=> exact continuous_const
  | cons i l ih=>
     let F(v:I→Γ):= X.endline (ι (P' v i)) i
     have hv:Continuous F:= ((p i).sub continuous_const).add continuous_const; let f(v:I→Γ):= X.stageList l (P' v) t (some (F v)); let q(v:I→Γ):= X.sep (b.map fun g=> g v) i (ι (P' v i))
     have hx:Continuous f:= ih (some F) (by simpa using hv)
     have hg:Continuous q:=by rcases b with _|g; exact continuous_const; exact X.smooth_temporal _ g (p i) (c g rfl) i
     have he(v:I→Γ): X.stageList (i::l) (P' v) t (b.map fun f=> f v)=(π t) (S.E (q v) (X.visiting (X.op i) (u i) (f v))):=by
        rw [stageList]; unfold striding; rw [show X.visiting (X.op i) (P' v i)=X.visiting (X.op i) (u i) from X.motionless _ _ (X.op i)]; rfl
     simp_rw [he]; exact (π t).continuous.comp (heat_cont S q _ hg ((X.visiting _ _).continuous.comp hx))
end Repertoire
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Repertoire.highway
#print axioms YM.SelectionAnalysis.Repertoire.temporal
