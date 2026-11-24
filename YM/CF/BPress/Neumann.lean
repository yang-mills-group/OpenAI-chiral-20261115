import YM.CF.BPress.Template
/-! N angular Mark kernels incl label sum. Plaquette cost in `SupportN.lean`. Finset & versions of sums for later weighted factors. Import physical observable from Test. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function MeasureTheory LocalH Lattice SU Mag Cube Grid Filter Branch Sheet Tunnel Finset
open scoped Topology BigOperators Classical Matrix
variable {s : Side} {T : Atlas} {y C C' Lf : ℝ} {B : ℕ} (F : Net s T Lf y C C' B) (W : Tunnel s) (U V : Micro s) (p : Duo s)
namespace Sheet.Atlas
variable (T y) (x : FacesH s)
def pairs : Finset (Duo s) := T.seats y x.1 ×ˢ T.seats y x.2
lemma pairs_ok (h : T.Coasts y) : p∈ T.pairs y x ↔ T.allowed y x.1 p.1 ∧ T.allowed y x.2 p.2:=by simp [pairs,T.seats_ok y h]
lemma pairs_ceiling (h : T.Coasts y) : (T.pairs y x).card≤25 :=by rw [pairs,card_product,T.seats_ceiling y _,T.seats_ceiling]; exact Nat.mul_le_mul (T.room_ceiling y x.1 h) (T.room_ceiling y x.2 h)
lemma pairs_a (h : T.Coasts y)(a:Mach s) : T.pairs y (W.reads (gauge a U))=(T.pairs y (W.reads U)).image fun p=>p*(W.framesE a)⁻¹:=by
 let f:=W.framesE a; rw [W.reads_a,pairs]; dsimp only; rw [T.seats_adj y _ h f.1,T.seats_adj y _ h f.2];
 ext u; obtain ⟨i,j⟩:=u; simp only [mem_product, mem_image]; constructor; rintro ⟨⟨i,p,rfl⟩,j,t,rfl⟩; exact ⟨(i,j),mem_product.mpr ⟨p,t⟩,rfl⟩; rintro ⟨⟨i,p⟩,v,e⟩; refine ⟨⟨_,(mem_product.mp v).1,congrArg Prod.fst e⟩,p,(mem_product.mp v).2,congrArg Prod.snd e⟩
-- `sum_borel`: measurable via H law rather than big parameter on frame functions.
lemma pairs_sum {X A:Type*} [MeasurableSpace X][AddCommMonoid A][MeasurableSpace A][MeasurableAdd₂ A] (g:X → FacesH s)(v: Measurable g)(f : X × Duo s → A)(w:Measurable f): Measurable fun x=> ∑ p∈T.pairs y (g x),f (x,p):= by
 simp_rw [pairs,Finset.sum_product]; refine T.sum_borel y (x:=fun x=>(g x).1) (f:=fun x=> ∑ i∈T.seats y (g x.1).2, f (x.1,x.2,i)) (measurable_fst.comp v) ?_; refine T.sum_borel y (x:=fun x:X × HFrame s=> (g x.1).2) (f:=fun x=> f (x.1.1,x.1.2,x.2)) (measurable_snd.comp (v.comp measurable_fst)) ?_; exact w.comp ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) -- g param x
end Sheet.Atlas
namespace Net
-- weight in sum over seats only (can add Mark costs to each)
def markN := ∏ i∈ W.banks, chord.ballDensity (xi y) (F.template W (W.reads U) p i) (W.orient U i)
lemma markN_local : LocalOn W.mem (fun U : Micro s=> F.markN W U p):=by
 intro U V h; change F.markN W U p=F.markN W V p; unfold markN; rw [W.reads_local U V h]; apply prod_congr rfl; intro i k; rw [W.orient_local U h i ((inside_iff ..).mp (W.banks_sub k)).1 ((inside_iff ..).mp (W.banks_sub k)).2]
lemma markN_a (a : Mach s) : F.markN W (gauge a U) (p*(W.framesE a)⁻¹)=F.markN W U p:=by
 unfold markN; apply prod_congr rfl; intro i h; let b:= W.banks_sub h; rw [F.template_a W U p a b, W.orient_a U a i ((inside_iff ..).mp b).1 ((inside_iff ..).mp b).2]; simp only [chord.ballDensity,Lattice.gauge,chord.right,chord.left]
lemma markN_nonneg : 0≤ F.markN W U p:= prod_nonneg fun _ _=> chord.density_nonneg ..
lemma markN_bound : F.markN W U p ≤ chord.charge group (xi y) ^ W.banks.card:=by
 rw [←abs_of_nonneg (F.markN_nonneg W U p), markN, Finset.abs_prod, ←prod_const]; exact prod_le_prod (fun _ _=> abs_nonneg _) (fun _ _=> chord.bound ..)
lemma markN_meas : Measurable (fun x : Micro s × Duo s=> F.markN W x.1 x.2):=by
 unfold markN; refine Finset.measurable_fun_prod _ fun i _=> (chord.density_meas _).comp (f:=fun x: Micro s × Duo s=> (F.template W (W.reads x.1) x.2 i,W.orient x.1 i)) ?_; exact Measurable.prodMk ((measurable_pi_apply i).comp ((F.template_meas W).comp ((W.reads_cont.measurable.comp measurable_fst).prodMk measurable_snd))) ((measurable_pi_apply i).comp (W.orient_cont.measurable.comp measurable_fst)) -- tune
lemma exact_in (h : ∀ i∈W.stores,U i=1) : F.markN W U p=∏ i∈W.banks, chord.ballDensity (xi y) (F.template W (W.reads U) p i) (U i):=by rw [markN,W.no_orient U h]
-- template = actual oriented on all face horizontal and all stores. use for cert horizontal+vertical.
lemma nonbanks {i : Link s} (h:i ∈ W.stores ∪ W.crown): F.template W (W.reads U) p i=W.orient U i:=by
 rcases mem_union.mp h with t|t
 · obtain ⟨k,w,v,j,rfl⟩:= W.stores_eq.mp t; rw [W.orient_trivial U (W.stores_eq.mpr ⟨k,w,v,j,rfl⟩)] -- tune
   change normal (W.rise k) (F.template W (W.reads U) p) j=1; rw [F.readV _ _ _ w,F.tar_plain _ _ _ v]; rfl
 obtain ⟨x,v|v⟩:=W.crown_mem _|>.mp t <;> subst i
 · change horizontal W.o (F.template W (W.reads U) p) x=horizontal W.o (W.orient U) x; rw [W.orient_o U]; have hp:= F.readH W (W.reads U) p (Nat.zero_le _); rw [rise_zero,F.tar_o W (W.reads U) p (Nat.zero_le _)] at hp; exact congrFun hp x
 change horizontal W.last (F.template W (W.reads U) p) x=horizontal W.last (W.orient U) x; rw [W.orient_last U, F.readH W _ _ le_rfl,F.tar_last W _ _ W.collar_ends.2.2]; rfl
lemma isclose {U : Micro s} (h:F.markN W U p≠0) (q : 0≤xi y) : chord.Close (W.orient U) (F.template W (W.reads U) p) W.mem (xi y):=by
 intro i a b; by_cases t:i∈ W.banks; exact chord.density_ne _ _ _ fun g=> h (prod_eq_zero t g)
 rw [F.nonbanks W U p (by contrapose! t; exact mem_sdiff.mpr ⟨(inside_iff ..).mpr ⟨a,b⟩,t⟩),chord.refl]; exact q

-- sum angular kernel without Fock or further marker scalars
def neumann := ∑ p∈T.pairs y (W.reads U), F.markN W U p
lemma neumann_local : LocalOn W.mem (F.neumann W):=by
 intro U V h; unfold neumann; rw [W.reads_local U V h]; exact sum_congr rfl fun i _=> F.markN_local W i U V h
lemma neumann_nonneg : 0≤F.neumann W U:=sum_nonneg fun _ _=> F.markN_nonneg ..
lemma neumann_bound (h : T.Coasts y) : |F.neumann W U| ≤ 25*chord.charge group (xi y)^ W.banks.card:=by
 rw [abs_of_nonneg (F.neumann_nonneg ..),neumann]; apply le_trans (sum_le_sum (fun i (_:i∈T.pairs y (W.reads U))=> F.markN_bound _ _ i)); rw [sum_const, nsmul_eq_mul]; gcongr; swap; · exact_mod_cast T.pairs_ceiling y (W.reads U) h
 unfold chord.charge; positivity
lemma neumann_a (h:T.Coasts y): GaugeInvariant (F.neumann W):=by
 intro a U; rw [neumann,T.pairs_a y W U h a,sum_image]; swap; · exact fun i _ j _ t=> mul_right_cancel t
 exact sum_congr rfl fun i _=> F.markN_a W U i a
lemma neumann_borel : Measurable (F.neumann W):=T.pairs_sum y W.reads W.reads_cont.measurable (fun x:Micro s× Duo s=> F.markN W x.1 x.2) (F.markN_meas W)
end Net
end YM.CF.BPress
