import YM.SU5.Aria.Miasma
import YM.Heat.Extend
/-! # Timeline: allocate cuts between neighbors; their location is immaterial to the chosen vacuum matrix element. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Aria
open Set Function Filter NormedSpace Metric Germ Alliance
open scoped Topology NNReal InnerProductSpace
variable {I:Type*}
section chosen
-- Start b (wall clock from 0). f,v legal threshold opens only strictly INSIDE for jitter. actual cut handles closed
variable (u v : I→ℝ)
def Sheet (l : List I) (b:ℝ) : Prop:=match l with
 | []=> True
 | i::L=> b<u i ∧ Sheet L (v i)
abbrev Weave (l: List I) : Prop:=∃ b, Sheet u v l b
structure Curtains (l : List I) where
 first : I→ℝ
 last : I→ℝ
 inside : ∀ i∈l, first i < u i
 outside : ∀ i∈l,v i<last i
 joins : ∀ (i j:I)(t L:List I), l=t++i::j::L → last i=first j
namespace Curtains
variable {u v}
lemma beyond {i:I}{L : List I}(C : Curtains u v (i::L)): Nonempty (Curtains u v L):=⟨C.first, C.last, fun i e=> C.inside _ (List.Mem.tail _ e),fun i e=> C.outside _ (List.Mem.tail _ e),fun i j l p e=>C.joins i j (_::l) p (by rw [List.cons_append,← e])⟩
end Curtains
lemma choose_curtains [DecidableEq I] (l:List I)(t:l.Nodup)(h:Weave u v l): Nonempty (Curtains u v l):=by
 -- `first i` of tail is NOT guaranteed inside gap on left (could be before v of anterior); can request by Sheet. strengthen.
 suffices p: ∀ b:ℝ, Sheet u v l b → ∃ C:Curtains u v l, (∀ i L,l=i::L→C.first i=b) by obtain ⟨b,Y⟩:=h; obtain ⟨c,y⟩:=p b Y; exact ⟨c⟩
 clear h; induction l with
 | nil=> intro b _; exact ⟨⟨u,v,by simp,by simp,by simp⟩,by simp⟩
 | cons i l ih=>
   intro b e; obtain ⟨p,q⟩:=e
   obtain ⟨y,t'⟩:= List.nodup_cons.mp t
   cases l with
   | nil=> exact ⟨⟨fun _=>b,fun x=>v x+1,by simpa using p,by simp, by intro i j p L h; have hp:=congrArg List.length h; simp at hp; omega⟩,by simp⟩
   | cons j l=>
     obtain ⟨q,e⟩:=q; let L:=(v i+u j)/2; have hb:v i<L:=by unfold L; linarith
     have hs:u j>L:=by unfold L; linarith
     obtain ⟨C,c⟩:=ih t' L (And.intro hs e)
     let D:= Function.update C.first i b; let V:= Function.update C.last i L
     have d {a:I}(e:a∈j::l): D a=C.first a:= update_of_ne (show a ≠ i from fun h=>y (h ▸ e)) ..
     have z {a:I}(e:a∈j::l): V a=C.last a:= update_of_ne (show a ≠ i from fun h=>y (h ▸ e)) ..
     refine ⟨⟨D,V,fun a h'=> ?_,fun a h'=>?_,?_⟩,?_⟩
     · rcases List.mem_cons.mp h' with h|q; · subst a; simpa [D]
       rw [d q]; exact C.inside _ q
     · rcases List.mem_cons.mp h' with h|q; · subst a; simpa [V]
       rw [z q]; exact C.outside _ q
     · intro a b t L' ht; cases t with
       | nil=> cases ht; rw [show V i=L from update_self .., d (List.Mem.head ..)]; exact (c j l rfl).symm
       | cons k t=>
         obtain ⟨_,ht⟩:= List.cons.inj ht
         rw [d (show b∈j::l by rw [ht]; simp), z (show a∈j::l by rw [ht]; simp)]; exact C.joins a b t L' ht
     intro a k e; rw [← (show i=a from List.cons.inj e|>.1)]; exact update_self ..
lemma weaves_sorted (l:List I)(s:l.Pairwise (fun i j=> v i<u j)): Weave u v l:=by
 induction l with
 | nil=> exact ⟨0,trivial⟩
 | cons i l ih=>
   obtain ⟨a,h⟩:=ih (List.pairwise_cons.mp s).2; refine ⟨u i-1,And.intro (by linarith) ?_⟩; cases l with
   | nil=> trivial
   | cons j l=> exact And.intro ((List.pairwise_cons.mp s).1 j (List.Mem.head ..)) (show _ ∧ Sheet u v l _ from h).2
end chosen
open OS OS.Semigroup
section timeline
variable {H:Hilbert}{i:Axis} (S:OS.Semigroup H i)(Ω:H)
local notation "E"=> S.E
open ContinuousLinearMap
local notation "Id"=> ContinuousLinearMap.id ℂ H.space
local notation "τ" r:max=> Real.toNNReal r
variable (X:I→H.Op)(u v : I→ℝ)
noncomputable def rector : List I→ ℝ → H.Op
| [],_=> Id
| i::l,b=> (E (τ (u i-b))).comp ((X i).comp (rector l (v i)))
lemma rector_left (k:I)(t:List I)(b:ℝ): rector S X u v (k::t) b=(E (τ (u k-b))).comp ((X k).comp (rector S X u v t (v k))):=rfl
noncomputable def before : List I → ℝ
| []=>0
| i::_=> u i
noncomputable def receive (l:List I):ℂ:= inner ℂ Ω (rector S X u v l (before u l) Ω)
variable (y z:I→ℝ)
lemma terraces (a b:ℝ)(ha:0≤a)(hb:0≤b): (E (τ a)).comp (E (τ b))=E (τ (a+b)):= by rw [Real.toNNReal_add ha hb]; exact (S.time ..).symm
lemma steam_contPos (x:ℝ)(h:0<x): ContinuousAt (fun t=> S.E (τ t)) x :=by
 let C:ℝ→ℂ:= Complex.ofRealCLM; let f:= S.F ∘ C
 have hx:C x∈ OS.Semigroup.inside:=h
 have he:= (S.localHeat (C x) hx).continuousAt.comp Complex.ofRealCLM.continuous.continuousAt
 apply he.congr; filter_upwards [lt_mem_nhds h] with t p; exact (congrArg S.F (show C t=duration (τ t) from (congrArg ((↑):ℝ→ℂ) (Real.coe_toNNReal t p.le)).symm)).trans (S.roots_heat (Real.toNNReal_pos.mpr p))
lemma rector_deeper (hΩ: ∀ t,E t Ω=Ω)(p a:ℝ)(l:List I)(hp:p≤a)(he: l ≠ [] → a ≤ before u l):
    (E (τ (a-p))) ((rector S X u v l a) Ω) = (rector S X u v l p) Ω:=by
 cases l with
 | nil => exact hΩ _
 | cons j t=>
   have h:a ≤ u j:= he (List.cons_ne_nil _ _); let ξ:= (X j).comp (rector S X u v t (v j)); rw [rector_left,rector_left];
   change E _ (E _ (ξ Ω))= E _ (ξ Ω); rw [←ContinuousLinearMap.comp_apply,terraces S] -- S field notation won't work
   · rw [show a-p+(u j-a)=u j-p by abel]
   · exact sub_nonneg.mpr hp
   exact sub_nonneg.mpr h
lemma rector_view (hΩ:∀ t,E t Ω=Ω)(p:ℝ)(l:List I): inner ℂ Ω (rector S X u v l p Ω)=receive S Ω X u v l:=by
 unfold receive; cases l with
 | nil=> rfl
 | cons j L=>
   let z:=(X j).comp (rector S X u v L (v j))
   have he(r:ℝ): inner ℂ Ω (rector S X u v (j::L) r Ω)=inner ℂ Ω (z Ω) := by rw [rector_left,ContinuousLinearMap.comp_apply,← S.swing,hΩ]
   rw [he,he]
noncomputable def behind (j:I): H.Op := (E (τ (u j-y j))).comp ((X j).comp (E (τ (z j-v j))))
lemma behind_pay(j:I): ‖behind S X u v y z j‖≤ ‖X j‖:= by
 unfold behind; refine (opNorm_comp_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _)).trans ((opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (S.shrinks _))))
include Ω
lemma with_curtains (hΩ:∀ t,E t Ω=Ω)(l:List I)(a:ℝ)(t:∀ i∈l,y i<u i ∧ v i<z i)(e:∀ i j t L, l=t++i::j::L → z i=y j)(p:∀ i L, l=i::L→ y i=a):
  (l.map (behind S X u v y z)).prod Ω = (rector S X u v l a) Ω:=by
 induction l generalizing a with
 | nil=> rfl
 | cons j l ih =>
   let f:=behind S X u v y z; let b:=z j; let r:=v j
   have h:y j=a:= p j l rfl; have hz:r < b:= (t _ (List.Mem.head ..)).2; have hp:∀i L,l=i::L→y i=b:=fun i L p=> (e j i [] L (by rw [p]; rfl)).symm
   have hh:= ih b (fun i u=> t i (List.Mem.tail _ u)) (fun i a t L u=> e i a (j::t) L (by rw [u]; rfl)) hp
   change E (τ (u j-y j)) (X j (E (τ (b-r)) ((l.map f).prod Ω)))= E (τ (u j-a)) (X j (rector S X u v l r Ω)); rw [h]; congr 2
   rw [show (l.map f).prod Ω =rector S X u v l b Ω from hh,rector_deeper S Ω X u v hΩ r b l hz.le]
   cases l with
   | nil=> simp
   | cons i L=> intro _; exact (hp i L rfl) ▸ (t _ (List.Mem.tail _ (List.Mem.head ..))).1.le
lemma curtain_payment (hΩ:∀ t,E t Ω=Ω)(l:List I)(t:∀ i∈l,y i<u i ∧ v i<z i)(e:∀ i j t L, l=t++i::j::L → z i=y j): inner ℂ Ω ((l.map (behind S X u v y z)).prod Ω) = receive S Ω X u v l:=by cases l with
 | nil=>rfl
 | cons i L=> rw [with_curtains S Ω X u v y z hΩ (i::L) (y i) t e (fun _ L h=>congrArg y (List.cons.inj h).1.symm), rector_view S Ω X u v hΩ]
end timeline
end YM.CF.Buffered.Afterglow.Tower.Aria
