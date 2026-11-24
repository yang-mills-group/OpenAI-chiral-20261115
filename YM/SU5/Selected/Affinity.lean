import YM.SU5.Selected.Caroling
/-! # Multi-compare regardless of order and viewpoints. Includes proof of real-locale readings
 on APPLICABLE chart points, not continuation outside of windows. -/
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

local notation "P₀" => ((P).aviator K).orthogonalProjectionOnto
local notation "L" => (P).Realm K
local notation "Ξ"=> glass X.sky (daylight M) X.sea X.glides
/-- true striding on the restricted continuous sector. Epoch coordinates and the requested
  Mink motion structure Ξ. -/
noncomputable def rack (i:I) : (L).Op:= (P₀).comp ((X.op i).comp ((P).aviator K).subtypeL)
noncomputable def gliding (b:Option ℝ)(i:I)(u:V) : (L).Op := (Ξ).E (X.sep b i u) ∘L (Ξ).U (diameter u) ∘L X.rack i ∘L (Ξ).U (diameter (-u))
abbrev origin : (P).Realm K := ⟨X.light,X.grounded⟩
noncomputable def roadList (l:List I)(u:I→V)(b:Option ℝ): (P).Realm K:=match l with
 | [] => X.origin
 | i::l=> X.gliding b i (u i) (roadList l u (some (X.endline (u i) i)))
noncomputable def reading (l:List I)(u:I→V): ℂ:= inner ℂ (X.origin) (X.roadList l u none)
lemma glide_exact (b:Option ℝ)(i:I)(u:Λ)(x:L) : (X.gliding b i (ι u) x).val=X.striding K b i u x.val:=by
 let V₀:= (X.sky.track).aviator K
 let v:= ι u; let t:= X.sep b i v
 let f: L→H:= fun x=> x.val
 let y:L:= (Ξ).U (diameter (-v)) x; let Z:H:= X.forward (-u) x.val; let v':= -u
 have hy : f y=Z:= show _ from (show f y=X.forward v' x.val from by
    unfold y; have he: -v = ι v':=rfl; rw [he]; exact glass_move X.sky _ X.sea X.glides x v')
 change f ((Ξ).E t ((Ξ).U (diameter v) (X.rack i y)))=(π K) ((E t) ((X.forward u) ((A i) Z)))
 change X.sea.E t (f _) =_; rw [show f ((Ξ).U _ (X.rack i y))=X.forward u (f (X.rack i y)) from glass_move X.sky _ X.sea X.glides (X.rack i y) u] -- f coe syntax tune
 have ht : f (X.rack i y)=(π K) (X.op i Z):=by rw [←hy,stack_projection]; rfl
 rw [ht, ←ContinuousLinearMap.comp_apply (X.forward u), show (X.forward u).comp (π K)=(π K).comp (X.forward u) from (P).ground K (X.forward u) (fun i _ t=> (Alliance.hard _ _ _ (fun j _ k=> (P).cCom ..) _).symm), ContinuousLinearMap.comp_apply, ←ContinuousLinearMap.comp_apply (X.sea.E t), Alliance.ground _ _ _ (fun i _ t=> X.glides ..)]; rfl
lemma reading_exact (l:List I)(u:I→Λ): X.reading l (clearAbove u)= X.ranking l u K:=by
  have he(b:Option ℝ): (X.roadList l (clearAbove u) b : (P).Realm K).val=X.stageList l u K b:=by
     induction l generalizing b with
     | nil=>rfl
     | cons i l ih=> rw [roadList, (show X.gliding b i (clearAbove u i)=_ from (show X.gliding b i (clearAbove u i)= X.gliding b i (ι (u i)) from rfl)), X.glide_exact,ih, stageList]; rfl
  change inner ℂ (Ω) (X.roadList l (clearAbove u) none).val=_; rw [he]; rfl
lemma glide_cont {T:Type*} [TopologicalSpace T](u:T→ V)(x:T→ L)(b:T→ Option ℝ)(i:I)(p:Continuous u)(q:Continuous x)(g:Continuous (fun v=> X.sep (b v) i (u v))) : Continuous (fun v=> X.gliding (b v) i (u v) (x v)):=by
  let Y:=L; have hc: Continuous (diameter (a:=a)):=by unfold diameter; fun_prop
  exact heat_cont (Ξ) _ _ g ((Ξ).cont_cross _ _ ((X.rack i).continuous.comp ((Ξ).cont_cross _ _ q (hc.comp p.neg))) (hc.comp p)) -- p.neg notation pointwise cmd
lemma repertoire_cont (l:List I): Continuous (X.reading l) :=by
  suffices he : ∀ b:Option ((I→V)→ℝ),(∀f,b=some f→Continuous f) → Continuous (fun v:I→V=> X.roadList l v (b.map fun f=> f v)) by exact continuous_const.inner (he none (by simp))
  intro b t; induction l generalizing b with
  | nil=> exact continuous_const
  | cons i l ih=>
     let f(u:I→V):= u i; let g(u:I→V):= X.endline (f u) i; have hv:Continuous f:=continuous_apply _; let q(u:I→V):= X.roadList l u (some (g u)); simp only [roadList]; refine (glide_cont X f q _ i hv (ih (some g) (by simpa [g,endline,frontend,Function.comp_def,Pi.sub_def,Pi.add_def] using (((continuous_apply a).comp hv).sub (continuous_const (y:=(X.rise i:ℝ))) |>.add (continuous_const (y:=(X.width i:ℝ)))))) ?_)
     rcases b with _|b; exact continuous_const; exact X.smooth_temporal _ b ((continuous_apply a).comp hv) (t b rfl) _
lemma clear_cont(u:I→Λ)(j:Axis) : Continuous (fun v:I→Γ=> clearAbove (swipe I u j v)):=by
 apply continuous_pi; intro i; apply continuous_pi; intro j'; by_cases p:j'=j
 · subst j'; unfold clearAbove swipe; simp only [Function.update_self]; exact continuous_subtype_val.comp ((continuous_apply _).add continuous_const)
 unfold clearAbove swipe; simp only [Function.update_of_ne p]; exact continuous_const
lemma clear_dense : DenseRange (clearAbove : (I→Axis→marks M)→I→Axis→ℝ):=by
 apply DenseRange.piMap (f:=fun _ : I => fun u:Axis→marks M=> ι u)
 intro i; exact DenseRange.piMap (f:=fun i:Axis=> fun v:Γ=>(v:ℝ)) (fun _=> (daylight M).denseRange_val)
lemma locally (u:I→Λ)(j:Axis)(S:Set (I→V))(p: IsOpen S)(t:clearAbove u∈ S): ∀ᶠ v:I→Γ in 𝓝 0, clearAbove (swipe I u j v) ∈ S:= by
 apply (clear_cont u j).continuousAt.tendsto.eventually
 rw [swipe_birth]; exact IsOpen.mem_nhds p t

variable {H' : Hilbert} {a' : Axis} (Y : Repertoire I a' M H')
local notation "B'" => {v:Axis//v≠a'}
variable [Fintype I][DecidableEq I]
-- compare general open sets
variable (l l' : List I) (hl:l.Nodup) (hr:l'.Nodup) (s:Set (I→Axis→ℝ))(p: IsOpen s)
abbrev Sharing (a : List ( {v:Axis//v≠a}))(b:List {v:Axis//v≠a'}) := ∀ (u : I→Axis→marks M), clearAbove u∈s→ X.ranking l u a = Y.ranking l' u b
lemma Sharing.flipped {v:List B}{t:List B'} (h: X.Sharing Y l l' s v t) : Y.Sharing X l' l s t v:= fun u v=> (h u v).symm
local notation "SC" u:max=> X.ranking l u
local notation "SP" v:max t:max => X.Sharing Y l l' s v t
include p hl
lemma Sharing.steers {v:List B}{t:List B'} (h: SP v t) (r:a'≠a) : X.Sharing Y l l' s (⟨a',r⟩::v) t:=by
 intro u i; let k:B:=⟨a',r⟩; refine Eq.trans (X.filmed u l hl v k ?_) (h u i)
 exact ((Y.temporal l' u t).continuousAt).congr ((locally u a' s p i).mono fun v e=> (h _ e).symm)
include hr
lemma Sharing.spans {v:List B}{t:List B'} (h: SP v t) (i:B) (j:B')(q:i.val=j.val) : X.Sharing Y l l' s (i::v) (j::t):=by
 intro u H; refine tendsto_nhds_unique_of_eventuallyEq (X.screening u l hl v i) (Y.screening u l' hr t j) ?_; -- name tune
 apply (crumbs_pi M _ (show _ from locally u i.val s p H)).mono; intro n p
 apply Average.eq_of; intro k; change X.ranking _ (swipe I u i.val _) _ = Y.ranking _ (swipe I u j.val _) _; rw [← q]; exact h _ (p k)
lemma Sharing.roadcase {v:List B}{t:List B'} (h: SP v t) : ∀ (i:List B)(j:List B'), List.Perm (i.map Subtype.val) (j.map Subtype.val)→ X.Sharing Y l l' s (i++v) (j++t):=by
 -- use same append permutation argument as SpatialCard
 intro i j; induction i generalizing j with
 | nil=> intro H; cases j; exact h; simp at H
 | cons i a₁ ih=>
    intro ht; obtain ⟨b,pb,hb⟩:= List.mem_map.mp (ht.subset (by simp : i.val∈ (i::a₁).map Subtype.val))
    obtain ⟨c,d,rfl⟩:= List.append_of_mem pb
    have hm: List.Perm (c ++ b::d) (b::(c++d)):= List.perm_middle
    have hx:=(ih (c++d) (by apply List.Perm.cons_inv (a:=i.val); simpa only [List.map_cons,hb] using (ht.trans (hm.map (fun i=>i.val)))))
    have hh:=Sharing.spans X Y l l' hl hr s p hx i b hb.symm
    intro u v'; exact (hh u v').trans (Y.step_permutation _ _ (hm.symm.append_right t) l' u)
lemma Sharing.completion (H:SP [] []) : X.Sharing Y l l' s X.sky.list Y.sky.list:=by
 by_cases h:a=a'
 · subst a'; simpa only [List.append_nil] using Sharing.roadcase X Y l l' hl hr s p H X.sky.list Y.sky.list (by
     apply List.Perm.map; rw [List.perm_ext_iff_of_nodup X.sky.unique_list Y.sky.unique_list]; exact fun i => iff_of_true (X.sky.traverses _) (Y.sky.traverses _)) -- append_nil definitional? fix
 let i:B:=⟨a',Ne.symm h⟩; let k:B':=⟨a,h⟩; let a₀:= X.sky.list.erase i; let b₀:= Y.sky.list.erase k
 have ht: SP [i] [k]:= ((H.steers X Y l l' hl s p (Ne.symm h)).flipped X Y l l' s|>.steers Y X l' l hr s p h).flipped Y X l' l s
 have hX:X.sky.list.Perm (a₀++[i]):=(List.perm_cons_erase (X.sky.traverses i)).trans (List.perm_append_singleton i a₀).symm
 have hY:Y.sky.list.Perm (b₀++[k]):=(List.perm_cons_erase (Y.sky.traverses k)).trans (List.perm_append_singleton k b₀).symm
 have hp:= Sharing.roadcase X Y l l' hl hr s p ht a₀ b₀ (by
    rw [List.perm_ext_iff_of_nodup ((X.sky.unique_list.erase i).map Subtype.val_injective) ((Y.sky.unique_list.erase k).map Subtype.val_injective)]; intro l; rw [Sunbelt.Links.graduates.otheraxes X.sky i, Sunbelt.Links.graduates.otheraxes Y.sky k]; exact and_comm)
 intro u m; rw [X.step_permutation _ _ hX, Y.step_permutation _ _ hY]; exact hp u m
lemma Sharing.smooth (H:SP [] []) : EqOn (X.reading l) (Y.reading l') (closure s):=by
  have h:= Set.EqOn.closure (s:= clearAbove '' (clearAbove ⁻¹' s:Set (I→Axis→Γ))) (by rintro _ ⟨u,v,rfl⟩; rw [X.reading_exact,Y.reading_exact]; exact (H.completion X Y l l' hl hr s p) u v) (X.repertoire_cont l) (Y.repertoire_cont l')
  apply h.mono; rw [image_preimage_eq_inter_range]; apply closure_minimal _ isClosed_closure; intro x hx
  apply _root_.mem_closure_iff.mpr ?_; intro o q v; obtain ⟨y,u,r⟩:= (clear_dense (M:=M)).exists_mem_open (s:=o∩s) (q.inter p) ⟨x,v,hx⟩ -- proof type tune
  exact ⟨_,u,r,⟨_,rfl⟩⟩

omit hr in
lemma family_sync (h:∀ k:{v:Axis//v≠a},∃ (H':Hilbert)(Y:Repertoire I k.val M H')(l':List I),X.Sharing Y l l' s [] []) : ∀ l₀:List B,X.Sharing X l l s l₀ []:=by
 intro l₀
 induction l₀ with
 | nil=> exact fun u p=>rfl
 | cons k t ih=>
    obtain ⟨H',Y,l',v⟩:= h k
    have he: X.Sharing Y l l' s t []:= fun u p=> (ih u p).trans (v u p)
    exact fun u p'=> ((Sharing.steers X Y l l' hl s p he k.property) u p').trans (v u p').symm

end Repertoire
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Repertoire.Sharing.smooth
#print axioms YM.SelectionAnalysis.Repertoire.reading_exact
