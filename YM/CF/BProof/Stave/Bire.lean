import YM.CF.BProof.Stave.Hull
import YM.CF.BProof.Stave.Pigment
import YM.CF.BProof.Stave.Refrain
/-! Building the fillers with symmetry. Use the conjugation bit and no invariant simplex
(unique colors with independent bits). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave
open Function Metric Finset Sim Extension
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal
variable {I J:Type*}[Fintype I][DecidableEq I][Fintype J]
structure Gallery (I J:Type*) [Fintype I][Fintype J] where
  adm : Finset I→Prop
  less {S T:Finset I}: S⊆T → adm T→ adm S
  car : I→ plate J
  portrait (i:I):car i∈ King J
  μ : I≃I
  flip_μ : μ.symm=μ
  μ_adm (S):adm (S.map μ.toEmbedding)=adm S
  μ_car(i):car (μ i) = blink (car i)
  cross (S): adm S→S.Nonempty→ S.map μ.toEmbedding≠S
namespace Gallery
variable (g:Gallery I J)
def tribe(S:Finset I):= S.map g.μ.toEmbedding
omit [DecidableEq I] in
lemma tribe_2(S:Finset I):g.tribe (g.tribe S)=S:=by have h:= octa_back g.μ S; rw [g.flip_μ] at h; exact h
omit [DecidableEq I] in
lemma tribe_size(S:Finset I):(g.tribe S).card=S.card:=card_map _
def tilt (x:Pool I): Pool I:=octa g.μ x
omit [DecidableEq I] in
@[simp] lemma tilt_tilt (x:Pool I): g.tilt (g.tilt x)=x:=by unfold tilt; nth_rw 1 [← g.flip_μ]; exact octa_oct g.μ x
omit [DecidableEq I] in
@[simp] lemma tilt_dist(x y:Pool I):dist (g.tilt x) (g.tilt y)=dist x y:= (octa_iso _).dist_eq x y
omit [DecidableEq I] in
lemma tilt_pl {x:Pool I}{S: Finset I}: Sim S x → Sim (g.tribe S) (g.tilt x):= octa_sim g.μ
omit [DecidableEq I] in
lemma team_tilt(x:Pool I): supp (g.tilt x)=g.tribe (supp x):= supp_octa _ _
lemma tilt_w {S:Finset I}{x:Pool I}(h:x∈ Wall S):g.tilt x∈Wall (g.tribe S):=by
 apply (wall_iff (g.tilt_pl (wall_le h))).mpr; rw [team_tilt]; intro e; apply (wall_iff (wall_le h)).1 h; rw [←g.tribe_2 (supp x),e,g.tribe_2]
def tonic (d:ℝ)(S:Finset I):= g.adm S∧∀ i∈S,∀ j∈S,Like d (g.car i) (g.car j)
omit [DecidableEq I] in
lemma migrates (d:ℝ)(S:Finset I)(p:g.tonic d S):g.tonic d (g.tribe S):=by
 constructor; exact (g.μ_adm S).symm ▸ p.1
 intro i hi j hj; obtain ⟨a,h,rfl⟩:= mem_map.mp hi; obtain ⟨b,w,rfl⟩:=mem_map.mp hj; change Like d (g.car (g.μ a)) (g.car (g.μ b)); rw [g.μ_car,g.μ_car]; exact (p.2 _ h _ w).blink
omit [DecidableEq I] in
lemma tonic_mono {u v:ℝ}{s t:Finset I}(k:g.tonic u t)(a:s⊆t)(b:u≤v):g.tonic v s:=⟨g.less a k.1,fun i h j g=> (k.2 i (a h) j (a g)).weaken b⟩
abbrev Drum (P:Type*) (J:Type*):= Pool P→plate J
variable {g}
structure Small (g:Gallery I J)(d:ℝ)(S:Finset I)(F:Drum I J):Prop where
  spot : Tame (Park S) F
  fee {x:Pool I}: Sim S x→∀ i∈S,Like d (g.car i) (F x)
structure Coat (g:Gallery I J)(d:ℝ)(k:ℕ)(u:ℝ)(F:Drum I J): Prop where
  kit (S:Finset I) : g.tonic u S→ S.card≤ k→ Small g d S F
  note (x:Pool I) : F (g.tilt x)=blink (F x)
private def actor (g:Gallery I J)(F:Drum I J):Drum I J := fun x=> blink (F (g.tilt x))
private structure Artist (g:Gallery I J)(d:ℝ)(S:Finset I)(Z F:Drum I J) : Prop extends Small g d S F where
  tick : Set.EqOn Z F (Wall S)
private theorem sings {Z F:Drum I J}{d:ℝ}{S: Finset I}
    (h:Artist g d (g.tribe S) Z F)(p:∀ x, Z (g.tilt x)=blink (Z x)) : Artist g d S Z (actor g F):=by
 refine ⟨⟨⟨h.spot.choose,LipschitzOnWith.of_dist_le_mul (fun x hx y hy=>?_)⟩,fun {x} hx i hi=>?_⟩,fun x hx=>?_⟩
 · rw [actor,actor,blink_dist,← tilt_dist g x]; exact h.spot.li.dist_le_mul _ (g.tilt_pl hx) _ (g.tilt_pl hy)
 · unfold actor; have ht:= (h.fee (g.tilt_pl hx) (g.μ i) (mem_map_of_mem _ hi)).blink; rw [g.μ_car,blink_blink] at ht; exact ht
 unfold actor; rw [← h.tick (g.tilt_w hx),p,blink_blink]
private theorem paint (d:ℝ)(h:0<d):∃ u:ℝ,0<u∧ u≤d∧∀ {I:Type}[Fintype I][DecidableEq I] (S:Finset I)(T:ℝ)(g:Gallery I J)(F:Drum I J),T ≤ u→ g.tonic T S→ S.Nonempty→ S.card≤4→ (∀ i∈S,Small g u (S.erase i) F)→ ∃ X:Drum I J,Artist g d S F X:=by
 obtain ⟨u,hU,U,K⟩:=Sim.fee (J:=J) (d/2) (by positivity); refine ⟨u/2,by positivity,by linarith,fun {I} _ _ S T g F k h n p f=>?_⟩
 obtain ⟨i,hi⟩:=n; obtain ⟨X,w,e,q⟩:= K S F (g.car i) ⟨i,hi⟩ p (g.portrait _) (rises (fun i hi=> (f i hi).spot)) (fun x hx=>by
    obtain ⟨j,hj,g'⟩:=hx; obtain ⟨l,z⟩:=(Sim.nonempty g'); exact ((h.2 i hi l (erase_subset _ _ z)).trans ((f j hj).fee g' _ z)).weaken (by linarith)) -- hole
 exact ⟨X,⟨⟨w,fun {x} hx j hj=> ((h.2 _ hj _ hi).trans (q x hx)).weaken (by linarith)⟩,e⟩⟩
private lemma shell {d u v:ℝ}{Z:Drum I J}{k:ℕ} (h:g.Coat u k v Z)(A: ∀ S, S.card=k+1 → g.tonic v S→ ∃ F:Drum I J, g.Artist d S Z F) (hd:u≤d): ∃ F:Drum I J,g.Coat d (k+1) v F:=by
 classical
 let P(s:Finset I) := s.card=k+1∧ g.tonic v s
 let b(S:Finset I):= g.tribe S; let a(S:Finset I):= (Fintype.equivFin (Finset I)) S
 have ha(S)(p:P S): a S ≠ a (b S):= (Fintype.equivFin (Finset I)).injective.ne (Ne.symm (g.cross S p.2.1 (card_pos.mp (p.1.symm ▸ Nat.succ_pos k))))
 have t(S)(p:P S): P (b S):=⟨(tribe_size ..).trans p.1,g.migrates v S p.2⟩
 have w(S):b (b S)=S:= tribe_2 ..
 choose D y using fun s:{s//P s}=>A s.val s.property.1 s.property.2
 let F(S:Finset I):Drum I J:= if hi:P S then D ⟨_,hi⟩ else 0
 have H(S)(h:P S): g.Artist d S Z (F S):=by unfold F; rw [dif_pos h]; exact y ⟨S,h⟩
 let X(S:Finset I): Drum I J:= if a S<a (b S) then F S else actor g (F (b S)); have hp (S)(h:P S): g.Artist d S Z (X S):=by
    unfold X; split; exact H S h; exact sings (H (b S) (t S h)) (‹Coat ..›.note)
 have hk (S)(p:P S)(x): X (b S) (g.tilt x)=blink (X S x):=by
    unfold X; rw [w]; cases lt_or_gt_of_ne (ha S p) <;> rename_i l
    · simp only [if_pos l,if_neg l.not_gt,actor,tilt_tilt]
    simp only [if_pos l, if_neg l.not_gt,actor,blink_blink]
 let G(x:Pool I):=if P (supp x) then X (supp x) x else Z x
 refine ⟨G,⟨fun S e hS=>?_,fun x=>?_⟩⟩
 · by_cases l:S.card=k+1
   · have hv:P S:=⟨l,e⟩; have hg:=hp S hv
     have hm:Set.EqOn G (X S) (Park S):=by
        intro x hx; unfold G; have H: Sim S x:= hx; by_cases z:supp x=S; rw [z, if_pos hv]; rw [if_neg (show ¬P (supp x) from fun p=> Nat.ne_of_lt (card_lt_card ⟨H.box,fun q=>z (Subset.antisymm H.box q)⟩) (p.1.trans l.symm))]; exact hg.tick ((wall_iff H).mpr z)
     exact ⟨hg.spot.copy hm.symm,fun {x} hx i hi=> (hm hx).symm ▸ hg.fee hx i hi⟩
   have hr:S.card≤k:=by omega
   have hg:=h.kit S e hr
   have hm:Set.EqOn G Z (Park S):=by intro x hx; unfold G; rw [if_neg (fun p=> (Nat.lt_succ_of_le ((card_le_card (show Sim S x from hx).box).trans hr)).ne (show (supp x).card=k+1 from p.1))]
   exact ⟨hg.spot.copy hm.symm,fun {x} hx i hi=> (hm hx).symm ▸ (hg.fee hx i hi).weaken hd⟩
 unfold G; rw [team_tilt]; change (if P (b (supp x)) then _ else _)=_; by_cases a:P (supp x); rw [if_pos (t _ a), if_pos a]; exact hk _ a _; rw [if_neg (fun p=> a (w (supp x) ▸ t _ p)),if_neg a]; exact h.note _
private lemma budget (d:ℝ)(h:0<d)(k:ℕ)(p:k≤4):∃ u:ℝ,0<u∧ u≤d∧∀ (v:ℝ), v≤u→∀ {I:Type}[Fintype I] [DecidableEq I](g:Gallery I J),∃ F:Drum I J, Coat g d k v F:=by
 induction k generalizing d with
 | zero =>
    refine ⟨d,h,le_rfl,fun _ _ I _ _ g=>⟨0, ⟨fun S _ hs=>⟨⟨_,(LipschitzWith.const 0).lipschitzOnWith⟩, fun {x} s=>?_⟩, fun _=> blink_zero.symm⟩⟩⟩ -- implicit lambda issues
    have :=card_pos.mpr s.nonempty; omega -- goal List?
 | succ k ih=>
    obtain ⟨u,hu,U,Q⟩:= paint (J:=J) d h; obtain ⟨v,hv,W,w⟩:= ih u hu (by omega)
    refine ⟨v,hv,W.trans U,fun y e I _ _ g=>?_⟩
    obtain ⟨F,hF⟩:=w y e g; refine shell hF (fun S kS c=>Q S y g F (e.trans W) c (card_pos.mp (by omega)) (by rw [kS]; exact p) (fun i hi=>hF.kit (S.erase i) (g.tonic_mono c (erase_subset ..) le_rfl) ?_)) U
    rw [card_erase_of_mem hi,kS]; omega

/-- Tame dummy: one frame filler on good faces through dimension three, charge-equivariant, prescribed before periods & history. Used with vertex ε-net. -/
theorem costume (d:ℝ)(h:0<d): ∃ u:ℝ, 0<u ∧ u≤d ∧ ∀ {I:Type}[Fintype I][DecidableEq I](g:Gallery I J),∃ F:Drum I J,Coat g d 4 u F:=by obtain ⟨u,h,H,Q⟩:=budget (J:=J) d h 4 le_rfl; exact ⟨u,h,H,@Q u le_rfl⟩ -- @
end Gallery
end YM.CF.BProof.Mesh.Stave
