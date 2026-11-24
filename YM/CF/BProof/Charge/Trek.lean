import YM.CF.BProof.Charge.Tones
import YM.Work.E04

/-! Transport the per-edge Tone property to all support tests and shortened paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge.Form
open Function Filter RG Wilson Lattice Finset Work Micro Moment MeasureTheory Angular AnalyticBridge.SectorAffine Mag
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
local notation "Cl"=> SU.group.colorScale
variable {s:Side}(W:Argument s)(σ: Signed)(U:Config G s)(y:ℝ)
abbrev Wet (S:Support s)(b:Bond s) := b.1∈S∧b.1+step b.2∈S
lemma per_fac (S:Support s)(b:Bond s) (h:Wet S b): Wet (move σ S) (sendEdge σ 0 b):=by
 rcases b with ⟨u,i⟩; unfold sendEdge; have he: spin σ (u+step i)=spin σ u + ((posDir i).rotate σ).vec:=by rw [spin,Signed.act_add,Step.vec_rotate,Step.vec_pos]
 let U:=spin σ u; rw [show affine σ 0 u=spin σ u from add_zero _]; have hq:=moves σ h.2; dsimp only at *; rw [he] at hq; cases e:((posDir i).rotate σ) with|mk a x=> rw [e] at hq; cases x; exact ⟨moves σ h.1,hq⟩; rw [show (Step.vec ⟨a,true⟩: Site s)= -step a from rfl] at hq; rw [← sub_eq_add_neg] at hq; exact ⟨hq,by simpa only [Step.used,if_true, sub_add_cancel] using (moves σ h.1)⟩ -- tune `cases` both occurrences

lemma jogB (t:RG.Slot)(x:Site s)(u:Site s)(h:u∈ touched (F03.slotFace t x)): separation x u≤ t.length+2:= by
 apply (separation_triangle x (wrap s t.offset+x) u).trans; exact Nat.add_le_add (E04.slot_separation ..) (((separation_comm ..) ▸ (E01.sep_touched (F03.slotFace t x) u h))) -- check comm

def Spread (S:Support s) := ∀ b,Wet S b→ Tone W y b U
lemma spread_le {S D:Support s}(h:S⊆ D)(k:Spread W U y D): Spread W U y S:= fun _ u=> k _ ⟨h u.1,h u.2⟩
abbrev pulley (a:Lam s) (M:ℕ):= halo (M+2) {a.center}
lemma pulley_ref (a:Lam s)(M:ℕ): pulley a M=move a.1 (halo (M+2) {(ref a).1}):=by rw [move_halo]; unfold pulley; rw [show spin a.1 (ref a).1=a.center from (equiv a.1).apply_symm_apply _]
lemma fetched (x:Site s)(M:ℕ){S:Support s}(g:S ⊆ halo M {x})(b:Bond s)(v:Wet S b): Wet (move σ (halo M {x})) (sendEdge σ 0 b):= per_fac σ _ _ ⟨g v.1,g v.2⟩
lemma spread_chrom (S:Support s)(e:Spread W U y (move σ S))(a:Cell s)(h:touched a⊆S): Chromic W y σ U a:= fun i=>e (sendEdge σ 0 (positions a i)) (per_fac σ _ _ ⟨h (curl_positions a i).1,h (curl_positions a i).2⟩)
lemma chrom_slot (a:Lam s)(M:ℕ)(e:Spread W U y (pulley a M))(t:Slot)(p:t∈Stack.allShort M): Chromic W y a.1 U (F03.slotFace t (ref a).1) := by
 rw [pulley_ref] at e; apply spread_chrom W a.1 U y _ e; exact fun x h=> halo_spec.mpr ⟨_,mem_singleton_self _,(jogB t _ _ h).trans (by have := (Stack.short_iff ..).1 p; omega)⟩
lemma pull_chords (S:Support s)(W: Argument s)(K:Chart G){C:ℝ}(e:Spread W U y (move σ S))(h:Ink K C y) (b:Bond s)(z:Wet S b) : SU.group.chord (lRead σ U b) ≤stepC C y :=noise_walk K W y σ b U h (e _ (per_fac σ _ _ z))
lemma walk_fee {S:Support s}(U:Config G s)(r:ℝ)(h:∀ i,Wet S i→ SU.group.chord (U i) ≤r)(x:Site s)(w:Walk)(v:(visits x w).toFinset⊆S) : SU.group.chord (travel U x w) ≤ w.length*r:= by
 induction w generalizing x with
 | nil=> simp [travel]
 | cons p q ih =>
    have hv:(visits (x+p.vec) q).toFinset⊆S:=by intro i hx; apply v; rw [visits,List.toFinset_cons]; exact mem_insert_of_mem hx
    have H:= ih _ hv; have hx:x∈ S:= v (by simp [visits]); have hj:x+p.vec∈S:= hv (by cases q<;>simp [visits]); have ha:SU.group.chord (p.read U x) ≤ r:=by
       rcases p with ⟨i,p⟩; cases p; exact h _ ⟨hx,hj⟩; rw [show (⟨i,true⟩:Step)=negDir i from rfl,Step.neg_read,Gauge.chord_inv]; change x+(-step i)∈ S at hj; rw [← sub_eq_add_neg] at hj; exact h _ ⟨hj,by simpa using hx⟩
    exact (SU.group.chord_triangle _ _).trans ((add_le_add ha H).trans_eq (by rw [List.length_cons,Nat.cast_add_one]; ring))
lemma spread_walk (K:Chart G){C:ℝ}(h:Ink K C y)(a:Lam s)(M:ℕ)(e: Spread W U y (pulley a M))(t:Slot)(q:t∈Stack.allShort M): SU.group.chord (travel (lRead a.1 U) (ref a).1 t.walk) ≤ M * stepC C y:=by
 rw [pulley_ref] at e; let x:=(ref a).1; let T:Support s:=halo (M+2) {x}; have hh(k)(hp:Wet T k):=pull_chords a.1 U y T W K e h k hp -- tune
 have hg: t.walk.length≤M:= le_trans (Nat.le_add_right _ 4) ((Stack.short_iff t M).1 q); have hv:0≤stepC C y:=mul_nonneg h.up.le (coin_pos ..).le
 apply le_trans (walk_fee (s:=s) (lRead a.1 U) _ hh x t.walk (fun i hi=>halo_spec.mpr ⟨_,mem_singleton_self _,(Extra.Iteration.Shapes.visits_dist _ _ _ (List.mem_toFinset.mp hi)).trans (hg.trans (by omega))⟩)); exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hg) hv
-- kept switch allows local with specified radius about PHYSICAL center not touching any columns backwards. Vertical plaquettes count all depth from Y.dawn.
lemma stays (p:BudgetPoint)(c:Clip)(a:Lam s)(M:ℕ)(e:Spread W U y (pulley a M))(v:p.threshold=thresh y)(K:Chart G){C:ℝ}(h:Ink K C y)(hv:ValidR c p M): PathData.kept c p.threshold (ref a).1 (lRead a.1 U):=by
 intro x; by_cases hm:p.threshold*Real.exp (separation (ref a).1 x.1/c.relaxation)<2; swap
 · exact le_trans (SU.group.chord_le_two _) (le_of_not_gt hm)
 rw [pulley_ref] at e; have hp := chord_price K W y a.1 U h x (spread_chrom W a.1 U y (halo _ {(ref a).1}) e x (fun y hy=>halo_spec.mpr ⟨(ref a).1,mem_singleton_self _,le_trans (separation_triangle _ x.1 _) (le_trans (Nat.add_le_add_left (?_) _) (hv _ hm))⟩)); -- tune position
 · rw [← v] at hp; apply hp.trans; apply le_mul_of_one_le_right p.threshold_pos.le; exact Real.one_le_exp (by have :=c.radius_pos; positivity)
 exact E01.sep_touched _ _ hy -- tune
end YM.CF.BProof.Charge.Form
