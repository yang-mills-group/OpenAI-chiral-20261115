import YM.CF.Cubes.Paint

/-! Nonvanishing on the entire flagged prism through two extra rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side} {U : Bkg (Domain m B)} {e : ℝ}
lemma walk_band (m B z q) (h : prob q) {S : Finset (Spot m)} (g : S⊆bandS m B z q) (hz : S.Nonempty) :
    ∃ a : Spot m, ∃ l : List (Ramp m), Moves m a l ∧ S=(a::l.map Prod.fst).toFinset ∧ (a::l.map Prod.fst).Nodup := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain ⟨a,H,G⟩ := S.exists_max_image (valS m) hz
    by_cases he : (S.erase a).Nonempty
    · obtain ⟨b,l,ht,hq,hx⟩ := ih _ (erase_ssubset H) (Subset.trans (erase_subset _ _) g) he
      have hb : b∈S.erase a := by rw [hq]; simp
      have he := (mem_erase.mp hb).1; have hp := (mem_erase.mp hb).2
      have hm : Prev m b a := (arc h (g hp) (g H) he).resolve_right (fun x=>not_lt_of_ge (G b hp) (prev_sign x))
      refine ⟨a,(b,1)::l,⟨hm,ht⟩,?_,?_⟩
      · rw [List.map_cons,List.toFinset_cons,←hq,insert_erase H]
      rw [List.nodup_cons,List.map_cons]; refine ⟨fun H => notMem_erase a S ?_,hx⟩; rw [hq]; exact List.mem_toFinset.mpr H
    refine ⟨a,[],trivial,?_,by simp⟩
    calc S = insert a (S.erase a) := (insert_erase H).symm
         _ = _ := by rw [not_nonempty_iff_eq_empty.mp he]; simp

def serve (m B : Side) (U : Bkg (Domain m B)) (s : ArrayF m) (a : Spot m) (l : List (Ramp m)) := (s a).val :: train m B U s a.1 l
def coal (m : Side) (p : Spot m → ℝ) (a : Spot m) (l : List (Ramp m)) := p a :: l.map (fun j=>p j.1)
lemma serve_cons (m B U s a w o l) : serve m B U s a ((w,o)::l)=(s a).val :: (serve m B U s w l).map (turn (parcel m B U a.1 w.1 o)) := by rw [serve,train]; rfl
lemma coal_cons (m p a w o l) : coal m p a ((w,o)::l)=p a::coal m p w l := by rw [coal,List.map_cons]; rfl
lemma served (m B U s a l) : ∀ z∈serve m B U s a l, ‖z‖=1 := by
  induction l generalizing a with
  | nil => intro z h; simp only [serve,train,List.mem_singleton] at h; subst z; exact vote_unit _
  | cons r l ih => rcases r with ⟨w,o⟩; rw [serve_cons]; intro z h
                   rcases List.mem_cons.mp h with g|g; subst z; exact vote_unit _
                   obtain ⟨t,H,rfl⟩ := List.mem_map.mp g; rw [turn_norm]; exact ih _ _ H
lemma coal_pos (m) (p : Spot m→ℝ) (h : ∀ i, 0≤p i) (a l) : ∀ z∈coal m p a l, 0≤z := by
  intro z he; rcases List.mem_cons.mp he with hx|hx; subst z; exact h _
  obtain ⟨t,-,rfl⟩ := List.mem_map.mp hx; exact h _
lemma menu (m B U s a l) : (serve m B U s a l).length=l.length+1 := by simp [serve,train_len]
def tray (b : List ℝ) (q : List Vect) := combo (b.zip q) Prod.snd Prod.fst
lemma tray_cons (c : ℝ) (l : List ℝ) (w : Vect) (x : List Vect) : tray (c::l) (w::x)=c • w+tray l x := by simp [tray,combo]
lemma tray_turn (g : E) (x : List ℝ) (y : List Vect) : tray x (y.map (turn g))=turn g (tray x y) := by
  induction x generalizing y with
  | nil => simp [tray,combo,turn]
  | cons i x ih =>
    cases y with
    | nil => simp [tray,combo,turn]
    | cons j y => rw [List.map_cons,tray_cons,tray_cons,ih,show ∀ u v, turn g (u+v)=turn g u+turn g v from fun _ _=>map_add (spinV g) ..,turn_mul]
lemma tray_bound (b : List ℝ) (hb : ∀ i ∈ b, 0 ≤ i) (q : List Vect) (hq : ∀ v∈q, ‖v‖≤1) (h : b.length=q.length) : ‖tray b q‖≤b.sum := by
  induction b generalizing q with
  | nil => simp [tray,combo]
  | cons i b ih =>
    cases q with
    | nil => simp at h
    | cons j q =>
      simp only [List.length_cons] at h; rw [tray_cons,List.sum_cons]; apply (norm_add_le ..).trans; apply add_le_add _ (ih (fun i hi=>hb _ (List.mem_cons_of_mem _ hi)) q (fun j hj=>hq _ (List.mem_cons_of_mem _ hj)) (by omega))
      have hi := hb i List.mem_cons_self
      rw [norm_smul,Real.norm_of_nonneg hi]; exact (mul_le_mul_of_nonneg_left (hq j List.mem_cons_self) hi).trans (le_of_eq (mul_one _))
lemma tray_size (b : List ℝ) (hb : ∀ i ∈ b, 0 ≤ i) (q : List Vect) (hq : ∀ v∈q, ‖v‖=1) (h : b.length=q.length) {e : ℝ} (hp : 0<e) (ht : Thick e q) : b.sum ≤ magC e q.length*‖tray b q‖ := by
  let l := b.zip q
  have hi : l.map Prod.snd=q := List.map_snd_zip h.ge
  have hg : l.map Prod.fst=b := List.map_fst_zip h.le
  have he := combo_guard l Prod.snd Prod.fst e hp (by rw [hi]; exact ht) (fun i g=>hb i.1 (by rw [←hg]; exact List.mem_map_of_mem g)) (fun i g=>hq i.2 (by rw [←hi]; exact List.mem_map_of_mem g))
  rw [show l.length=q.length by rw [←hi,List.length_map],hg] at he; exact he

lemma mispaint (p : Spot m → ℝ) (hp : ∀ i,0≤p i) (he : 0≤e) (h : Guard U e) (s : ArrayF m) {z : Site (Domain m B)}
    (a : Spot m) (l : List (Ramp m)) (H : Moves m a l) (ha : a.1∈active m B z) (hl : ∀ i∈l, (i:Ramp m).1.1∈active m B z) :
    ‖turn (tax m B U z a.1 1) (tray (coal m p a l) (serve m B U s a l))-
        combo (a::l.map Prod.fst) (fun i=>freight m B U z i.1 (s i)) p‖≤
          pot B e*(l.length+1:ℝ)*(coal m p a l).sum := by
  have hr : 0 ≤ pot B e := by unfold pot; positivity
  induction l generalizing a with
  | nil =>
    have he : ‖launch m B U z a.1 1 (s a)-freight m B U z a.1 (s a)‖≤pot B e := by rw [norm_sub_rev]; exact freight_gap he h _ _ _ ha _
    change ‖turn _ (tray [_] [_])-combo [a] _ _‖≤ _; rw [tray_cons,show tray [] []=0 from by simp [tray,combo],add_zero,turn_mul]; simp only [combo,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,coal,List.length_nil,Nat.cast_zero,zero_add,mul_one]
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg (hp a),mul_comm _ (p a)]; exact mul_le_mul_of_nonneg_left he (hp _)
  | cons r l ih =>
    rcases r with ⟨w,o⟩
    have hb := hp a; have hw : w.1∈active m B z := hl _ List.mem_cons_self
    rw [serve_cons,coal_cons,tray_cons,tray_turn, show ∀ k:E, ∀ x y, turn k (x+y)=turn k x+turn k y from fun k x y=>map_add (spinV k) x y]
    let T := pot B e; let t := tax m B U z a.1 1; let R := parcel m B U a.1 w.1 o; let f : Spot m→Vect := fun i=>freight m B U z i.1 (s i)
    let b := coal m p w l; let L := serve m B U s w l; let l' := combo (w::l.map Prod.fst) f p; let u := tax m B U z w.1 1; let Y := tray b L
    have hA : ‖turn t (p a • (s a).val)-p a • f a‖≤p a * T := by
      rw [turn_mul,← smul_sub,norm_smul,Real.norm_of_nonneg hb,norm_sub_rev]; exact mul_le_mul_of_nonneg_left (freight_gap he h z a.1 (s a) ha 1) hb
    have hZ := show ‖turn t (turn R Y)-turn u Y‖≤T*b.sum from (parcel_gap he h ha hw (show Fits m _ _ from H.1.1) Y 1 o 1).trans (mul_le_mul_of_nonneg_left (tray_bound b (coal_pos m p hp _ _) L (fun i hi=>(served m B U s w l i hi).le) (by simp [b,coal,L,menu])) hr)
    have hU : ‖turn u Y-l'‖≤T*(l.length+1:ℝ)*b.sum := ih w H.2 hw (fun i hi=>hl i (List.mem_cons_of_mem _ hi))
    rw [show combo _ _ p = p a • f a+l' from by simp [List.map_cons,combo,l',f]]
    rw [add_sub_add_comm]; apply (norm_add_le ..).trans
    apply (add_le_add hA ((norm_sub_le_norm_sub_add_norm_sub _ (turn u Y) _).trans (add_le_add hZ hU))).trans
    rw [List.length_cons,List.sum_cons]; push_cast; change _≤T*_*(p a+b.sum)
    unfold T at *; nlinarith [mul_nonneg hr hb, mul_nonneg (show 0≤(l.length:ℝ) from Nat.cast_nonneg _) (mul_nonneg hr hb)]
-- lower constant before B and volume
def low := (magC margin 7)⁻¹
lemma low_p : 0<low := inv_pos.mpr (magC_pos margin margin_pos 7)
theorem prism_nonzero (s : ArrayF m) {q : Sq} (g : prob q) (he : 0≤e) (h : Guard U e) {r : Finset Row}
    (hv : Verified m B margin U s r) (hs : ∀ i∉r, q i=0) (hc : pot B e*7≤low/2) (z : Site (Domain m B)) :
    low/2≤ ‖paint m B U s q z‖ := by
  let S := bandS m B z q
  obtain ⟨a,l,hl,H,G⟩ := walk_band m B z q g (subset_refl _) (has_bandS m B z q g)
  change S=_ at H
  have he' : a∈S := by rw [H]; simp
  have ht i (g:i∈l) : i.1∈S := by rw [H]; simp only [List.mem_toFinset]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem g)
  have ho i (e : i∈S) : i.2∈r := by
    by_contra k; have G : 0 < cash m B z q i := (mem_filter.mp e).2; rw [show cash m B z q i=0 from empty_cash (m:=m) (B:=B) (hs _ k) z i.1] at G; linarith
  let b := coal m (cash m B z q) a l; let L := serve m B U s a l; let Y := tray b L
  have hy : Thick margin L := thick_train hv (permits_iff.mpr ⟨hl,fun i hi=>ho _ (ht i hi)⟩) (ho _ he')
  have hi := tray_size b (coal_pos _ _ (cash_nonneg m B z q) _ _) L (served m B U s a l) (by simp [b,L,coal,menu]) margin_pos hy
  have hb : b.sum=1 := by
    rw [← cash_sum m B z q g, ← sum_subset (S.subset_univ), H,List.sum_toFinset _ G]; swap; exact fun i _ hi=>outside hi
    simp [b,coal,List.map_map]; rfl
  rw [hb] at hi
  have hz : paint m B U s q z = combo (a::l.map Prod.fst) (fun i=>freight m B U z i.1 (s i)) (cash m B z q) := by
    rw [paint,←sum_subset (S.subset_univ),H,List.sum_toFinset _ G]
    · rfl
    intro i _ Hx; rw [outside (m:=m) (B:=B) (z:=z) (q:=q) Hx,zero_smul]
  have hd := total_len hl
  have hY : low ≤ ‖Y‖ := by
    have he : L.length≤7 := by unfold L; rw [menu]; omega
    unfold low; rw [←one_div,div_le_iff₀ (magC_pos ..)] -- tune
    · rw [mul_comm]; exact hi.trans (mul_le_mul_of_nonneg_right (magC_inc margin margin_pos he) (norm_nonneg _))
    exact margin_pos
  let x := turn (tax m B U z a.1 1) Y
  have hX : low ≤ ‖x‖ := by unfold x; rw [turn_norm]; exact hY
  have hk : ‖x-paint m B U s q z‖ ≤ low/2 := by
    rw [hz]; apply (mispaint (cash m B z q) (cash_nonneg m B z q) he h s a l hl (spot_hit he') (fun i hi=>spot_hit (ht i hi))).trans
    change _*b.sum≤_; rw [hb,mul_one]
    have H : (l.length:ℝ)≤6 := by exact_mod_cast hd
    exact le_trans (mul_le_mul_of_nonneg_left (show (l.length:ℝ)+1≤7 by linarith) (show 0≤pot B e by unfold pot; positivity)) hc
  linarith [norm_le_norm_sub_add x (paint m B U s q z)]
end YM.CF.Cube
