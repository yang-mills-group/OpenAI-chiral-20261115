import YM.CF.BPress.Grid.Polish
/-! Full factor-of-two refinement. Accounting for axes and locality of memory. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid.Half
open Function Filter Lattice Finset SU Cube MeasureTheory
open scoped Topology BigOperators Classical
variable {s : Side} {r : ℕ} (P:Method){d:ℕ}
local notation "ρ" => Delivery.FabrReq group d s E
local notation "Xr" => Fabric d s E

private structure Here (S:Finset (Fin d))(r t:ℕ)(F:ρ→ Xr) : Prop where
 see (x y:ρ)(o) (h:o∈nodeM r S): NearLine r x.1 y.1 t o → NearRead (r+r) x.2 y.2 t o → F x o = F y o
 leave (x:ρ)(o) : o∈mesh (r+r)→ F x o=x.2 o
 borel : Measurable F
lemma near_mono {t u:ℕ} {x o:Space d s}(e:t+delta o x ≤ u) (i:Space d s)(p:delta x i ≤ t) : delta o i≤u:=by apply (delta_triangle _ x _).trans; omega
private lemma here_step {S : Finset (Fin d)} {t : ℕ} {i:Fin d} {F:ρ→ Xr} (h:Here S r t F) (p:r+r∣s.val)(v:0<r)(e:i∉S): Here (insert i S) r (r+t) fun x=> polish P S x.1 (F x) i r:= by
 constructor
 · intro x y o g a b; have he (i)(v:delta o i ≤ r)(t:i∈nodeM r S): F x i=F y i:= h.see x y i t (fun _ w p=> a _ w (near_mono (by omega) _ p)) fun _ u w=> b _ u (near_mono (by omega) _ w); unfold polish; split; next l=> exact he o (by simp) l
   next l =>
    let u:=backs o i r; let y':=hop o i r; have h0:u∈nodeM r S:= parentM S i p v e o l g; have h1:y'∈nodeM r S:= (flip_step p v o S e g).mpr l; have v:delta o u ≤ r:=by -- tune
        nth_rw 1 [←hop_backs o i r,delta_comm]; exact delta_hop ..
    rw [he u v h0, he y' (delta_hop ..) h1, a (u,i) (subnodeM h0) (v.trans (by omega)), a (o,i) (subnodeM g) (by simp)]
 · intro x o p; have hp:o∈nodeM r S:=nodeM_mono (empty_subset _) (show o∈nodeM r (∅:Finset (Fin d)) from nodeM_empty s r d|>.symm ▸ p); unfold polish; rw [if_pos hp]; exact h.leave x o p
 apply measurable_pi_lambda; intro x; unfold polish; split; exact (measurable_pi_apply x).comp h.borel
 let T(j:WalkEdge d s) := Measurable.comp (measurable_pi_apply j) (pad_meas s r d group); exact P.borel.comp (Measurable.prodMk (((measurable_pi_apply _).comp h.borel).mul ((T _).comp measurable_fst)) (((measurable_pi_apply _).comp h.borel).mul (((T _).comp measurable_fst).inv))) -- tune

include P
private lemma iter_polish (S:Finset (Fin d))(p:r+r∣s.val)(v:0<r) : ∃ F : ρ→ Xr, Here S r (r*S.card) F ∧ ∀ (a b c K δ m : ℝ) (x:ρ), Price δ K → 0 ≤ a → (a+ S.card*b < c) → 0 ≤ b → c ≤ δ → 4*((r:ℝ)^2*m + K*c^2) ≤ b → Flat x.1 m → arcFee (r+r) x.1 x.2 a → Nice S x.1 (F x) r (a+ S.card*b) := by
 induction S using Finset.induction_on with
 | empty=>
    refine ⟨fun v=>v.2,⟨?_,fun _ _ _=>rfl,measurable_snd⟩,?_⟩
    · intro x y i w _ h; rw [nodeM_empty] at w; exact h i w (by simp)
    intro a b c K δ m x _ _ _ _ _ _ e v; unfold Nice; simp only [stride,fee,nodeM_empty, notMem_empty,if_false,card_empty,Nat.cast_zero,zero_mul, add_zero]; exact v
 | @insert i S e ih=>
    obtain ⟨F,h,H⟩:=ih; refine ⟨ fun x:ρ=> polish P S x.1 (F x) i r, ?_, ?_⟩; show Here _ _ _ (fun x:ρ=> polish P S x.1 (F x) i r); convert here_step P h p v e using 1; rw [card_insert_of_notMem e]; ring
    intro a b c K δ m x π A B t' g q hp w
    let y:ℝ:= a+ S.card*b; rw [card_insert_of_notMem e,Nat.cast_add_one,add_mul,one_mul] at *; have he:y < c:= by unfold y; linarith
    apply nice_weaken _ _ _ (one_axis P e hp (H a b c K δ m x π A he t' g q hp w) π (he.trans_le g) p v); change y+ _≤ a+ _; rw [← add_assoc]; apply add_le_add_right _ y; -- tune
    refine le_trans ?_ q; gcongr
    · exact π.positive.le

theorem half_step (p:r+r∣s.val)(v:0<r) : ∃ T:ρ→ Xr, Only r (r+r) (r*d) T ∧
    ∀ (a b c K δ m : ℝ) (x:ρ), Price δ K → 0 ≤ a → (a+ d*b < c) → 0 ≤ b → c ≤ δ → 4*((r:ℝ)^2*m+ K*c^2) ≤ b → Flat x.1 m → arcFee (r+r) x.1 x.2 a → arcFee r x.1 (T x) ((a+d*b)/2):= by
 obtain ⟨F,h,H⟩ := iter_polish P (@univ (Fin d) _) p v; simp only [card_univ,Fintype.card_fin] at h H; refine ⟨F,⟨fun x y o e t v=> h.see x y o (nodeM_all _ _ _|>.symm ▸ e) t v,h.leave,h.borel⟩,fun a b c K δ m x π A B t h g e p=>?_⟩; have hp:= H a b c K δ m x π A B t h g e p; simpa [Nice,arcFee,stride,fee] using hp
end YM.CF.BPress.Grid.Half
