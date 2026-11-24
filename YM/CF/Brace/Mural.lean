import YM.CF.Dial.Pry
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B:Side}
-- bottom row at most one sample
def singleU (m:Side)(a:Spot m):List (Ramp m)→ Prop
 | []=>True
 | i::l=> a.2≠0 ∧ singleU m i.1 l
instance (a l):Decidable (singleU m a l):=Classical.propDecidable _
def fees (m:Side)(a: Spot m)(r:Finset Row):=(permits m a r).filter (singleU m a)
lemma fee_in {l a r}(h:l∈fees m a r): l∈permits m a r:= (mem_filter.mp h).1
-- relax check
def Cap (m B:Side)(U: Skin m B)(s:ArrayF m)(r: Finset Row)(a:Spot m):=∀ l∈fees m a r, margin < ‖restrain margin (train m B U s a.1 l) (s a).val‖
def Attested(m B:Side)(U: Skin m B)(s:ArrayF m)(r:Finset Row):=∀ a:Spot m, a.2∈r→ Cap m B U s r a
lemma small_margin(m B:Side):margin<1:=by
  let U:Skin m B:=1
  obtain ⟨x,h⟩:= cue_from U
  let a:Spot m:=(0,0); have ht := h a (mem_singleton_self _) [] (permits_iff.mpr ⟨trivial,fun i p=>by simp at p⟩)
  simpa only [train,restrain,vote_unit] using ht
lemma baseA(m B U s):Attested m B U s {0}:=by
  intro a p l k; replace p:=mem_singleton.mp p; cases l
  · simp only [train,restrain,vote_unit]; exact small_margin m B
  exact False.elim ((singleU.eq_2 .. ▸ (mem_filter.mp k).2).1 p) -- tune
lemma Attested.form {U s r a l}(h:Attested m B U s r)(p:l∈fees m a r)(g:a.2∈r): Thick margin (serve m B U s a l):=by
  constructor; exact h a g l p
  induction l generalizing a with
  | nil=> trivial
  | cons b l ih=>
    rcases b with ⟨w,o⟩; obtain ⟨hh,hk⟩:=mem_filter.mp p; obtain ⟨hl,hW⟩:=permits_iff.mp hh
    change Thick margin (train _ _ _ _ _ ((w,o)::l)); rw [train,thick_turn_iff];
    have hz:l∈fees m w r:= mem_filter.mpr ⟨permits_iff.mpr ⟨hl.2,fun i h=>hW i (List.mem_cons_of_mem _ h)⟩,hk.2⟩
    have hv:w.2∈r:=hW _ List.mem_cons_self
    exact ⟨h w hv l hz,ih hz hv⟩
lemma cap_tip (m B U) {I : Type} [DecidableEq I] (S: Finset I)(f:I→ ArrayF m)(r:I→Finset Row)(j:Row)(h:S.card≤6)(a:Index m)(w:Cube.Field m):∃ v:Ballot,∀ i∈S, Cap m B U (capRow (f i) j (Function.update w a v)) (insert j (r i)) (a,j):=by obtain ⟨v,p⟩:= check_tip m B U S f r j h a w; exact ⟨v,fun i hp l H=>p i hp l (fee_in H)⟩
lemma cap_dep (m B U s j r a){w v:Cube.Field m} (h:Cap m B U (capRow s j w) r (a,j))(he:∀ b,Fits m b a →w b=v b): Cap m B U (capRow s j v) r (a,j):=by
  intro l hl; rw [train_eq m B U (capRow s j w) a l _, show capRow s j v (a,j)=capRow s j w (a,j) by simp [capRow,he a (fits_id m a)]]; exact h l hl
  rintro ⟨⟨b,g⟩,o⟩ hb; have H :Fits m b a:=(move_mem (permits_iff.mp (fee_in hl)).1 _ hb).1; simp [capRow,he b H]
lemma Att_end (m B U) {I : Type} [DecidableEq I] (S : Finset I) (f : I → ArrayF m) (r : I → Finset Row) (j : Row)
    (h : S.card≤6) (he : ∀ i∈S, ending (r i) j) (hg : ∀ i∈S, Attested m B U (f i) (r i)) :
    ∃ v : Cube.Field m, ∀ i∈S, Attested m B U (capRow (f i) j v) (insert j (r i)) := by
  have q (k : ℕ) : ∃ v : Cube.Field m, ∀ a, degree m a < k → ∀ i∈S, Cap m B U (capRow (f i) j v) (insert j (r i)) (a,j) := by
    induction k with
    | zero => exact ⟨fun _ => Classical.arbitrary Ballot,fun _ hi=> by omega⟩
    | succ k ih =>
      obtain ⟨w,hw⟩ := ih
      choose p H using fun a => cap_tip m B U S f r j h a w
      let v : Cube.Field m := fun a=> if degree m a=k then p a else w a
      refine ⟨v,?_⟩; intro a ha i hi
      by_cases g : degree m a=k
      · apply cap_dep _ _ _ _ _ _ _ (H a i hi); intro b hb; by_cases gx : b=a
        · subst b; simp [v,g]
        have hu := fits_degree hb gx; rw [g] at hu; simp [v,hu.ne,gx]
      apply cap_dep _ _ _ _ _ _ _ (hw a (by omega) i hi); intro b hb
      have he : degree m b≤degree m a := card_le_card (fits_os hb)
      unfold v; rw [if_neg (by omega)]
  obtain ⟨v,H⟩ := q 5
  refine ⟨v,?_⟩; intro i hi ⟨a,t⟩ ht
  rcases mem_insert.mp ht with hq|hq
  · simp only at hq; subst t; exact H a (lt_of_le_of_lt (degree_le ..) (by norm_num)) i hi
  have hj : t < j := he i hi _ hq
  intro l hl; have G := permits_iff.mp (fee_in hl)
  have hr {x : Ramp m} (h : x∈l) : x.1.2 < j := lt_of_le_of_lt (move_mem G.1 _ h).2.1 hj
  have he : InRows (r i) l := fun x hx=>(mem_insert.mp (G.2 x hx)).resolve_left (hr hx).ne
  rw [show capRow (f i) j v (a,t)=f i (a,t) from if_neg hj.ne,train_eq m B U (f i) a l _]; exact hg i hi _ hq _ (mem_filter.mpr ⟨permits_iff.mpr ⟨G.1,he⟩,(mem_filter.mp hl).2⟩)
  exact fun x hx=>if_neg (hr hx).ne
lemma ward_c(m B r): IsOpen {t: FlagU m B|Attested m B t.1 t.2 r}:=by
  unfold Attested Cap; simp_rw [Set.setOf_forall]; apply isOpen_iInter_of_finite; intro i; apply isOpen_iInter_of_finite; intro h; apply isOpen_biInter_finset; exact fun _ _=> isOpen_lt continuous_const (fee_cont ..)
lemma ward_g(m B U s r)(g:Site (Domain m B)→ E): Attested m B (gauge g U) (onF g s) r ↔ Attested m B U s r:=by
  unfold Attested Cap; simp_rw [train_g]; unfold onF scaledV; dsimp only; simp_rw [strain_turn,turn_norm]
end YM.CF.Brace
