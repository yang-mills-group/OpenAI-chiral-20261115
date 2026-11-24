import YM.SU5.Selected.Seats
/-! # Compare and project in overlapping coordinate half-charts.

Abstract from the bigger RG and C* imports. The BUY is the equality `account` comparing
on pairs X,Y which for the law need the actual chart formulas at any common rung (proved
separately). Here conclude projection identities and most importantly common axis transport
even if other coordinates aren't themselves separated.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric
open CF.Buffered.Afterglow.Tower MeshClock Germ
open scoped Topology InnerProductSpace NNReal ENNReal
variable {H : Hilbert} {Γ : AddSubgroup ℝ} {I : Type*} [DecidableEq I]
local notation "D₀" u:max=>{x:I // x≠u}
structure Sunbelt (j : I) (Γ:AddSubgroup ℝ) (H : Hilbert) where
  track : Alliance {x:I // x≠j} Γ H
  list : List {x:I // x≠j}
  traverses i : i∈ list
  unique_list : list.Nodup
  heat : ℝ≥0→ H.Op
  smooth (x : H): Continuous (fun i:ℝ≥0=>heat i x)
  diffusion (x : H): Continuous (fun i:ℝ≥0=> (heat i).adjoint x) -- adjoint cont for joint-cont

namespace Sunbelt
variable {j j' : I}
variable (X : Sunbelt j Γ H) (d : Dense (Γ:Set ℝ))
local notation "P"=> X.track
local notation "R" u:max=> ((P).crew u).pi_c
local notation "U" u:max x:max=> ((P).crew u).play x
local notation "Φ₁" u:max=> (P).raw X.list (fun i=> u i.val)
local notation "Λ" u:max=>Real.toNNReal ((u j):ℝ)

noncomputable def plane (u : I→Γ) := (X.heat (Real.toNNReal ((u j):ℝ))).comp ((P).raw X.list (fun i=> u i.val))
lemma carries_spot (u:I→Γ) (i:D₀ j) (z:Γ) (z' : Γ) (t : Γ) (h:z'=z+t):
    X.plane (Function.update u i.val z') = (X.plane (Function.update u i.val z)).comp (U i t) := by
  have he (z:Γ): X.plane (Function.update u i.val z)=(X.plane (Function.update u i.val 0)).comp (U i z):=by
    have h1 (z:Γ): (fun a:{x:I//x ≠ j}=> Function.update u i.val z a.val)=(Function.update (fun a:{x:I//x≠ j}=>u a.val) i z) := by
       funext a; by_cases e:a=i
       · subst a; rw [update_self,update_self]
       rw [update_of_ne e,update_of_ne (show a.val≠ i.val from fun q=> e (Subtype.ext q))]
    unfold plane; rw [Function.update_of_ne i.property.symm,Function.update_of_ne i.property.symm,h1 z,h1 0,raw_spot (P) X.list X.unique_list (X.traverses i)]; rfl -- possible `h1 0` rewrites `h1 z`? proof ok
  rw [he z,he z', (show ((P).crew i).play z'= _ from h.symm ▸ (((P).crew i).piles z t).symm)]; rfl
lemma carries_update (u:I→Γ) (i:D₀ j) (z:Γ):
    X.plane (Function.update u i.val z)=(X.plane (Function.update u i.val 0)).comp (U i z):= X.carries_spot u i 0 z z (zero_add z).symm
-- monotone chart even at time0. require only positivity of shown coords. 
def playback (x y:H)(u:I→Γ)(t:List (D₀ j)):= inner ℂ x (X.plane u ((P).stackS t y))
def curtain (x y:H)(u:I→ℝ): ℂ:= inner ℂ x (X.heat (u j).toNNReal ((P).flight d X.list (fun i=> u i.val) y))
lemma playback_empty (x y:H)(u:I→Γ): X.playback x y u []=inner ℂ x (X.plane u y):=rfl
lemma curtain_eq (x y:H)(u:I→Γ): X.playback x y u X.list = X.curtain d x y (fun i=>(u i:ℝ)):= by unfold playback curtain plane; rw [(P).smooth_notch d]; rfl
-- consumption: time continuity with no others' motions (within that chart)
lemma continuity (x y:H)(t:List (D₀ j))(u:I→Γ):Continuous (fun i:Γ=> X.playback x y (Function.update u j i) t):=by
  have he(c:Γ): (fun a:D₀ j=> Function.update u j c a.val) = (fun a=> u a.val):=funext (fun i=> update_of_ne i.property ..)
  unfold playback plane; simp_rw [Function.update_self,he,ContinuousLinearMap.comp_apply]
  exact continuous_const.inner ((X.smooth _).comp (continuous_real_toNNReal.comp continuous_subtype_val)) -- function name tune
lemma curtain_cont (x y:H) : Continuous (X.curtain d x y) := by
  unfold curtain
  have he(u:I→ℝ) : inner ℂ x (X.heat (u j).toNNReal ((P).flight d X.list (fun i=> u i.val) y))=inner ℂ ((X.heat (u j).toNNReal).adjoint x) ((P).flight d X.list (fun i=> u i.val) y):=by rw [ContinuousLinearMap.adjoint_inner_left]
  simp_rw [he]; exact ((X.diffusion _).comp (continuous_real_toNNReal.comp (continuous_apply j))).inner ((P).moves d X.list _ (fun i _=> continuous_apply _) _ continuous_const)

variable (x y : H)
lemma playback_step (u:I→Γ) (i : D₀ j)(l:List (D₀ j))(z:Γ): X.playback x y (Function.update u i.val z) (i::l)=
    inner ℂ x (X.plane (Function.update u i.val 0) ((U i z) ((R i) ((P).stackS l y)))) := by
  unfold playback; rw [(P).shel_step, carries_update]; rfl
lemma playback_zero (u:I→Γ)(i:D₀ j)(l:List (D₀ j))(z:Γ) : X.playback x y (Function.update u i.val z) l = inner ℂ x (X.plane (Function.update u i.val 0) ((U i z) ((P).stackS l y))) := by unfold playback; rw [carries_update]; rfl

def Window (u:I→Γ) (i:D₀ j)(l:List (D₀ j)):= ContinuousOn (fun c:Γ=> X.playback x y (Function.update u i.val c) l) (Set.Ici 0)
include d
lemma public_record (u : I→Γ) (i: D₀ j)(l:List (D₀ j))(p : 0≤ (u i.val:ℝ))(q:X.Window x y u i l) :
    X.playback x y u (i::l) = X.playback x y u l := by
  let w := u i.val
  let E:H→L[ℂ]ℂ:= (innerSL ℂ x).comp (X.plane (Function.update u i.val 0)); let y' := ((P).stackS l y)
  -- use right-only
  have h : update u i.val w=u:= Function.update_eq_self ..
  rw [← h,playback_step,playback_zero] -- care tactic rewrites w hidden
  refine retain_ge ((P).crew i) E d y' ?_ w p
  exact q.congr fun c _=> (playback_zero ..).symm
omit d
lemma updatesafe (u:I→Γ) (i:I)(z:Γ)(j:I) (v:i≠j)(p:0≤ (u j:ℝ)): 0 ≤ (Function.update u i z j : ℝ):=by rw [Function.update_of_ne (Ne.symm v)]; exact p
variable {H' : Hilbert} (Y : Sunbelt j' Γ H') (x' y' : H')
-- connect generic value (at any partial projector)
def Links (p : List (D₀ j))(q : List (D₀ j')) : Prop:= ∀ (u:I→Γ),0 ≤ (u j:ℝ)→0≤ (u j':ℝ)→X.playback x y u p=Y.playback x' y' u q
lemma Links.reverse {p:List (D₀ j)} {q:List (D₀ j')} (h: Links X x y Y x' y' p q): Links Y x' y' X x y q p:=fun u e v=>(h u v e).symm
lemma Links.window {p:List (D₀ j)}{q:List (D₀ j')} (h: Links X x y Y x' y' p q)(i:j'≠j)(u:I→Γ)(v:0≤(u j:ℝ)) : X.Window x y u ⟨j',i⟩ p:= by
  refine (continuity Y x' y' q u).continuousOn.congr ?_
  intro l s; refine h (Function.update u j' l) (updatesafe _ _ _ _ i v) ?_
  rw [Function.update_self]; exact s
include d
lemma Links.projectroat {p:List (D₀ j)}{q:List (D₀ j')} (h: Links X x y Y x' y' p q)(i:j'≠j) : Links X x y Y x' y' (⟨j',i⟩::p) q :=fun u e v=> by rw [public_record X d x y u ⟨j',i⟩ p v (h.window X x y Y x' y' i u e)]; exact h u e v
omit d
lemma Links.twinroad {p:List (D₀ j)}{q:List (D₀ j')} (h: Links X x y Y x' y' p q)(i:D₀ j)(k:D₀ j')(e:i.val=k.val) (t:i.val≠j'):
     Links X x y Y x' y' (i::p) (k::q):=by
 intro u xu yu; let v:= Function.update u i.val 0; let w:= u i.val
 let a := X.track.stackS p y; let b:=Y.track.stackS q y'
 let G := Function.update u i.val w; have he : G=u:= Function.update_eq_self ..
 have hel(l:Γ): Function.update u i.val l= Function.update u k.val l:=by rw [e]
 let f := (innerSL ℂ x).comp (X.plane v); let g := (innerSL ℂ x').comp (Y.plane (Function.update u k.val 0)); let U' := (Y.track.crew k)
 have ht(l:Γ): f ((U i l) a)=g (U'.play l b):= by
    have gY:= h (Function.update u i.val l) (updatesafe _ _ _ _ i.property xu) (updatesafe _ _ _ _ t yu)
    rw [X.playback_zero,hel l,Y.playback_zero] at gY -- hel may rewrite wrong (v easier). ensure `nth_rw`
    exact gY
 rw [← he]; dsimp only [G]; rw [X.playback_step,hel w,Y.playback_step] -- hel affects update u of term with eq incl inserted 0? w not 0
 change f ((U i w) ((R i) a))= g (U'.play w (U'.pi_c b))
 let F:=f.comp (U i w); let S:=g.comp (U'.play w)
 apply tandem ((P).crew i) U' F S a b
 apply Eventually.of_forall; intro l; change f ((U i w) ((U i l) a))=g (U'.play w (U'.play l b)); rw [Players.paved, U'.paved, ht]
lemma Links.concom {p:List (D₀ j)}{q:List (D₀ j')} (h: Links X x y Y x' y' p q)(a:List (D₀ j))(b:List (D₀ j'))(e:a.map Subtype.val=b.map Subtype.val) : Links X x y Y x' y' (a++p) (b++q):=by
 induction a generalizing b with
 | nil=> cases b; exact h; simp at e
 | cons i l ih=> cases b with
   | nil=>simp at e
   | cons k t=>
     obtain ⟨r,v⟩:= List.cons.inj e
     exact Links.twinroad X x y Y x' y' (ih t v) i k r (r.symm ▸ k.property)
lemma Links.completes_aux {p:List (D₀ j)}{q:List (D₀ j')} (h: Links X x y Y x' y' p q)(a:List (D₀ j))(b:List (D₀ j'))(e:a.map Subtype.val |>.Perm (b.map Subtype.val)) : Links X x y Y x' y' (a++p) (b++q):=by
 -- reorder right map; choose h match via perm cons extraction
 induction a generalizing b with
 | nil=> cases b; exact h; simp at e
 | cons i a ih=>
    have ht : i.val∈b.map (fun k=>k.val):= e.subset (by simp)
    obtain ⟨k,hk,r⟩:= List.mem_map.mp ht
    obtain ⟨c,l,hl⟩:= List.append_of_mem hk
    -- b=c++k::l. perm k::c++l
    subst b; have hp : List.Perm (c ++ k::l) (k::(c++l)):=by exact List.perm_middle -- tune
    have he:= e.trans (hp.map (fun k=>k.val))
    apply swapLinks _ (ih:=Links.twinroad X x y Y x' y' (ih (c++l) (by apply List.Perm.cons_inv (a:=i.val); simpa only [List.map_cons,r] using he)) i k r.symm (r ▸ k.property)) ((hp.symm).append_right q)
where
  swapLinks {p q'} (l': List (D₀ j'))(ih:Links X x y Y x' y' p q') (hp: q'.Perm l') : Links X x y Y x' y' p l':=fun u a b=>by rw [ih u a b]; unfold playback; rw [overlay_all Y.track q' l' hp]
include d
lemma Links.graduates (p:j≠ j') (h: Links X x y Y x' y' [] []) : Links X x y Y x' y' X.list Y.list := by
 let i:D₀ j:= ⟨j',Ne.symm p⟩; let k:D₀ j':= ⟨j,p⟩;
 let a:=X.list.erase i; let b:=Y.list.erase k
 have ht : Links X x y Y x' y' [i] [k] := ((h.projectroat X d x y Y x' y' (Ne.symm p)).reverse X x y Y x' y'|>.projectroat Y d x' y' X x y p).reverse Y x' y' X x y
 -- Perm (i::a)= a++[i]. compare by deletion
 have hX:X.list.Perm (a++[i]):= (List.perm_cons_erase (X.traverses i)).trans (by exact (List.perm_append_singleton i a).symm)
 have hY:Y.list.Perm (b++[k]):= (List.perm_cons_erase (Y.traverses k)).trans (by exact (List.perm_append_singleton k b).symm)
 have hp:= ht.completes_aux X x y Y x' y' a b (by
    rw [List.perm_ext_iff_of_nodup ((X.unique_list.erase i).map Subtype.val_injective) ((Y.unique_list.erase k).map Subtype.val_injective)]; intro l; rw [otheraxes X i,otheraxes Y k]; exact and_comm)
 intro u U' U''; specialize hp u U' U''; unfold playback at *
 rw [overlay_all P _ _ hX,overlay_all Y.track _ _ hY]; exact hp
where
 otheraxes {H : Hilbert}{j:I} (X:Sunbelt j Γ H)(i : D₀ j)(l:I) : l∈(X.list.erase i).map Subtype.val ↔ l≠i.val ∧ l≠j:=by
    rw [List.mem_map]; constructor
    · rintro ⟨k,v,rfl⟩; obtain ⟨v₁,_⟩:= X.unique_list.mem_erase_iff.mp v; exact ⟨fun e=>v₁ (Subtype.ext e),k.property⟩
    rintro ⟨u,w⟩; exact ⟨⟨l,w⟩, X.unique_list.mem_erase_iff.mpr ⟨fun g=>u (congrArg Subtype.val g),X.traverses _⟩, rfl⟩

omit d
include d in
lemma links_match (p:j≠j') (h:Links X x y Y x' y' [] []) (u:I→ℝ) (xU:0≤ u j) (yU:0 ≤ u j') : X.curtain d x y u = Y.curtain d x' y' u:=by
  let C:= fun i:I=> {v:ℝ| v∈Γ ∧ ((i=j ∨ i=j')→0≤v)}
  let B:= Set.pi (Set.univ : Set I) C
  have ht : ∀ i:I, u i∈ closure (C i):=by
    intro i; by_cases v:i=j ∨ i=j'; swap; · exact ((show C i=(Γ:Set ℝ) by simp [C,v]).symm ▸ (d (u i)))
    have hd₀ : 0 ≤ u i:= v.elim (fun p=>p.symm ▸ xU) fun p=>p.symm ▸ yU
    apply Metric.mem_closure_iff.mpr; intro ε h
    obtain ⟨x,hx,e⟩:= d.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr (show u i<u i+ε by linarith))
    refine ⟨x,⟨hx,fun _=>hd₀.trans e.1.le⟩,?_⟩; rw [Real.dist_eq]; exact abs_lt.mpr (by constructor <;> linarith [e.1,e.2])
  have hw : u∈ closure B := mem_closure_pi.mpr ?_ -- tune
  swap; · intro i v; exact ht i
  refine Set.EqOn.closure (s:=B) ?_ (X.curtain_cont d x y) (Y.curtain_cont d x' y') hw
  intro z tz; let q(i:I):Γ:=⟨z i,(tz _ (Set.mem_univ i)).1⟩; exact ((X.curtain_eq d x y q).symm.trans ((Links.graduates X d x y Y x' y' p h q ((tz _ (Set.mem_univ j)).2 (Or.inl rfl)) ((tz _ (Set.mem_univ j')).2 (Or.inr rfl))).trans (curtain_eq Y d x' y' q))) -- tune
include d in
lemma playback_all (l:List (D₀ j)) (f:I→Γ)
    (h:∀ i, 0≤ (f i:ℝ))(p:∀ i∈ l, ∀ u:I→Γ, (∀ j:I, 0≤(u j:ℝ))→X.Window x y u i []) :
    X.playback x y f l = X.playback x y f []:=by
  induction l generalizing f with
  | nil=> rfl
  | cons i t ih=>
     let T:= X.playback x y; let Q f:= fun v:Γ=>T (Function.update f i.val v)
     have ht i (v:i∈ t) := p i (List.Mem.tail _ v)
     apply Eq.trans _ (ih f h ht)
     apply public_record X d x y f i t (h _)
     refine (p i (List.Mem.head ..) f h).congr ?_
     intro w v; refine ih _ (fun u=> ?_) ht
     by_cases e:u=i.val; rw [e, Function.update_self]; exact v
     rw [Function.update_of_ne e]; exact h _

end Sunbelt
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.Sunbelt.Links.graduates

#print axioms YM.SelectionAnalysis.Sunbelt.links_match
