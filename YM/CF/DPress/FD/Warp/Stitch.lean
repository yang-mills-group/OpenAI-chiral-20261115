import YM.CF.DPress.FD.Warp.Rung
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Lat Scroll Tw Finset Con Row
open Cube (More)
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m N:ℕ}{u:ℝ}
namespace Turf
-- level width k = number of vertices.
variable (T:Trophy n l u)(η:Cotton n)
local notation "SF"=>supportT
structure Leader {n:Side}{l:ℕ}{u:ℝ}(T:Trophy n l u)(m k:ℕ)(a:ℝ) where
 F : Cotton n→ Pane n→ Clove n m
 m_F : ∀ η, Measurable (F η)
 v_F : ∀ s η X, (clove n m).mv s (F η X)= F (act s η) (flashA s X)
 ℒ_F : ∀ S,Clan l S→S.card≤ k→∀ c X, Tends S (F c X) a
 keep : ∀ c X w, Grade l u X (supportT w)→ F c X w=basic T c X w
 clear : ∀ c X w, Skip (F c X w) (Late n k)
 foot : ∀ w,Live w → Clan l (supportT w) → ∀ c c' X Y,Prints c c' (supportT w)→Agrees (halo (globe l+5) (supportT w)) X Y → F c X w=F c' Y w
lemma entry0 (p:0<m): Nonempty (Leader T m 0 baseP):=by
 let A:=basic (m:=m) T; refine ⟨{ F:=A,m_F:=fun i=>basic_M ..,v_F:=fun s η X=>basic_x .., ℒ_F:= ?_,keep:=fun _ _ _ _=>rfl, clear:=fun _ _ _=>ClearV.2 (fun _ _=>rfl), foot:=fun w t _ η μ X Y b v=> basic_p T η μ w b (agrees_mono v (Finset.coe_subset.mpr (end_h (Finset.Subset.refl _) (by omega)))) (wave_eq w t p)}⟩
 intro S t v c X; have e(i:leaf n m): i∉facet S:=fun t=> Nat.not_lt.mpr v (card_pos.mpr ((wave_eq i t.1 p).mono t.2)); exact ⟨A c X,⟨fun i t=> False.elim (e _ t),fun _ _=>Frame.reflex _,fun i t=> False.elim (e i t)⟩⟩ -- tune
variable {T} {X Y:Pane n}{S:MaskU n}{a b:ℝ}
lemma Tends.widen {F:Clove n m}(r:a≤ b)(p:Tends S F a): Tends S F b:=by obtain ⟨f,g⟩:=p; exact ⟨f,g.more (Set.Subset.refl _) b r⟩
lemma Tends.T_v {F G:Clove n m}(e:Set.EqOn F G (facet S))(t:Tends S F a):Tends S G a:=by obtain ⟨f,g⟩:=t; exact ⟨f,Warm.Seam.backward g (Set.EqOn.symm e)⟩ -- tune namespace Seam
abbrev Solace (a b:ℝ):Prop:=∀ {n:Side}{m r:ℕ}(F:Clove n m) {S:MaskU n},S.Nonempty→0<m→ r<5 →S.card=r+1→(∀ D⊂ S,Tends D F a) → (∀ i,Skip (F i) (Late n r)) →∃ G,Receipt S (Late n (r+1)) b F G
lemma merrit(a:ℝ)(p:0 ≤a): ∃ b:ℝ,a≤b∧Solace a b:=by
 obtain ⟨b,h,v⟩:=issue a p; refine ⟨b,h,?_⟩; intro n m r F S H q v' t y w; let i: Fin 5:=⟨r,v'⟩; apply v (I:=Seat n) (K:=Front n) m q S H (by omega) F y (Sum.inr i) (Late n (r+1)) _ _ (fun j _=> ClearV.2 (fun i t=> ClearV.1 (w j) i (by omega)))
 · intro P; obtain ⟨j,e,t⟩:= (mem_filter.mp P).2; apply Nat.lt_irrefl r; rw [←Sum.inr.inj e] at t; exact t
 exact fun y _=>ClearV.1 (w y) _ le_rfl
-- case pattern. note not assume Live when deciding Kappa
local notation "ρv"=> (Set (Ramp (Seat n) m))
abbrev upto(l r:ℕ)(w:leaf n m):Prop:= Live w ∧ Clan l (SF w) ∧ (SF w).card=r+1
def TryV {k:ℕ}(P: Leader T m k a)(V: ClerkK n m (k+1) b) (η:Cotton n)(X:Pane n):Clove n m:= fun w=> if upto l k w∧ ¬ Grade l u X (SF w) then V.f η (SF w) (P.F η X) w else P.F η X w
lemma uptake(s:Sweep n)(w:leaf n m): upto l r w = upto l r (ωr s w):=by
 have ht(s:Sweep n)(w:leaf n m): upto l r w→ upto l r (ωr s w):=by
    rintro ⟨t,p,v⟩; refine ⟨ω_L s t,?_,?_⟩; rw [ω_S]; exact p.rotate; rw [ω_S,ζ,card_map,v]
 apply propext; refine ⟨ht s w,fun p=> ?_⟩; simpa only [ωr,(pullW n m).vert] using ht s⁻¹ (ωr s w) p
variable (P: Leader T m r a)(V:ClerkK n m (r+1) b)
lemma try_F (s:Sweep n)(η:Cotton n)(X:Pane n): (clove n m).mv s (TryV P V η X)=TryV P V (act s η) (flashA s X):=by
 funext i; obtain ⟨i,e⟩:= (e (pullW n m) s).surjective i; change ωr s i=_ at e; subst_eqs; rw [valid_v,show ωr s⁻¹ (ωr s i)=i from (pullW n m).vert s _]; unfold TryV; have he: upto l r i ∧ ¬ Grade l u X (SF i) ↔ upto l r (ωr s i) ∧ ¬Grade l u (flashA s X) (SF (ωr s i)):= (by apply Iff.trans (and_congr (eq_iff_iff.mp (uptake s i)) Iff.rfl); refine and_congr_right fun _=>?_ ; refine not_congr (Iff.symm ?_); rw [ω_S, grade_u,ζ_rev]) -- tune eq_iff_iff
 split
 next t=> rw [if_pos (he.1 t),←P.v_F s η,ω_S,V.rot,valid_v,show ωr s⁻¹ (ωr s i)=i from (pullW n m).vert s _]
 next t=> rw [if_neg (show ¬ (_∧_) from fun v=> t (he.2 v)),←P.v_F s η,valid_v,show ωr s⁻¹ (ωr s i)=i from (pullW n m).vert s _]
lemma try_p (c:Cotton n) : Measurable (TryV P V c):=by
 apply measurable_pi_lambda _; intro i; unfold TryV; refine Measurable.ite ?_ ((measurable_pi_apply _).comp ((V.m_p _ _).comp (P.m_F _))) ((measurable_pi_apply _).comp (P.m_F _)); rw [Set.setOf_and]; exact (show MeasurableSet (setOf (fun v:Pane n=> upto l r i)) from by by_cases h:upto l r i <;> simp [h]).inter (grade_M l u (SF i)).compl
lemma try_good (z: Solace a b)(v: r<5)(t:0<m)(c: Cotton n)(X:Pane n)(U:MaskU n)(w: Clan l U)(h:U.card=r+1) :Receipt U (Late n (r+1)) b (P.F c X) (V.f c U (P.F c X)):= V.good _ _ _ (z (P.F c X) (card_pos.mp (by omega)) t v h (fun i t=> P.ℒ_F i (w.mono t.le) (by have ht:= card_lt_card t; omega) c X) (P.clear c X))
lemma try_m (z:Solace a b)(v: r<5)(t:0<m)(c:Cotton n)(X:Pane n)(U:MaskU n)(w:Clan l U)(h:U.card=r+1)(p:¬Grade l u X U) :Set.EqOn (TryV P V c X) (V.f c U (P.F c X)) (facet U):=by
 intro i f; have hp:SF i⊆ U:= f.2; unfold TryV; by_cases e:SF i=U
 · rw [if_pos (show _ from ⟨⟨(show Live i from f.1),e.symm ▸ w,(congrArg Finset.card e).trans h⟩,e.symm ▸ p⟩),e]
 have hv:i∈boundary U:=⟨f.1,lt_of_le_of_ne hp e⟩; rw [if_neg (show ¬ (upto l r i∧ _) from fun h'=> (card_lt_card hv.2).ne (h'.1.2.2.trans h.symm))]; exact ((try_good P V z v t c X U w h).1 hv).symm
lemma try_keep (c:Cotton n)(X:Pane n)(i)(v:Grade l u X (SF i)):TryV P V c X i=basic T c X i:=by rw [TryV,if_neg,P.keep _ _ _ v]; exact fun w=>w.2 v -- tune typo
end Turf
end YM.CF.DPress.FD
