import YM.CF.BPress.House.Packet
/- default prob measure conditioned on $v$ costs. This includes elemental blocks.Frame sums.E etc. Count for Exc. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.House
open RG Wilson Push.SectorMeasure MeasureTheory LocalH Lattice Cube Bands Locale Wealth Net Grid Finset Function SU Mag Branch Port Weave Vesper Skye Hazel Reserve
open scoped Classical Topology BigOperators YM.CF.BPress.Vesper ENNReal
variable {N:Side}{B:BandWidth}(A:Bands (More N) B)(R:Hangar (More N)) (y:ℝ)
-- projection arithmetic.
def unholy(x: Realm B N R):Prop := ∃ i:Patio R, (x.1 i).1 ∨ heigh y ≤ ‖x.2.1.1 i‖
def humbug(x:Platter (B:=B) R):Prop:= ∃ i, heigh y≤‖x i‖
def cooled(x:Attire (B:=B) R) := ¬humbug R y x.1.1
def brisk := ({background R 0} : Set (Bank R)) ×ˢ {u:Attire (B:=B) R|cooled R y u}
def excite(x: Realm B N R):Prop:= x∉brisk (B:=B) R y
lemma brisk_eq (x: Realm B N R): (x∈brisk R y) ↔ ¬unholy R y x ∧ ∀ i,(x.1 i).2=0:=by
 constructor
 · intro p; obtain ⟨a,v⟩:= p; change x.1= _ at a; refine ⟨fun ⟨i,k⟩=> ?_, fun i=>?_ ⟩; rw [a] at k; exact v ⟨i,k.resolve_left (by simp [background])⟩; rw [a]; rfl
 rintro ⟨a,b⟩; refine ⟨funext fun i=>Prod.ext ?_ (b i),fun ⟨i,g⟩=> a ⟨i,.inr g⟩⟩; by_cases t:(x.1 i).1; exact False.elim (a ⟨i,.inl t⟩); exact Bool.eq_false_iff.mpr t
lemma succ_excite (x:Realm B N R)(e:unholy R y x): excite R y x:= fun v=> (((brisk_eq ..).1 v).1 e) -- tune
lemma unholy_body (p:Choir A R)(i:BlockY A R): i∈bawl A R y (Sread A R p) (βread A R p) ↔ unholy R y (p i):=by
 constructor
 · intro v; obtain ⟨a,t,V⟩:= mem_image.mp v; obtain ht|ht:=(mem_filter.mp t).2; refine ⟨packB R a.2,.inl ?_⟩; rw [←V]; exact (beset_me ..).1 ht; refine ⟨packB R a.2,.inr ?_⟩; rw [←V]; exact ht
 rintro ⟨a,h⟩; let k:=porch A R i a; refine mem_image.mpr ⟨k, mem_filter.mpr ⟨mem_univ _,?_ ⟩, porch_own ..⟩; rcases h with h|h; refine Or.inl ((beset_me A R (icon A R p) k).2 ?_); unfold k; rw [gather_p]; exact h; right; rw [βread,gather_p]; exact h -- tune order
lemma unholy_flag : MeasurableSet {x:Realm B N R|unholy R y x}:= by
 unfold unholy; simp only [Set.setOf_exists,Set.setOf_or]; apply MeasurableSet.iUnion; intro i; exact (measurableSet_eq_fun (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst)) (measurable_const (a:=true))).union (measurableSet_le measurable_const (show Measurable fun x:Realm B N R=>‖x.2.1.1 i‖ from by fun_prop)) -- tune
lemma cooled_flag : MeasurableSet {x:Attire (B:=B) R|cooled R y x}:=by apply MeasurableSet.compl (s:={x:Attire (B:=B) R|humbug R y x.1.1}); unfold humbug; simp only [Set.setOf_exists]; exact (MeasurableSet.iUnion fun i=> measurableSet_le measurable_const (show Measurable fun x:Attire (B:=B) R=> ‖x.1.1 i‖ from by fun_prop))
lemma brisk_meas : MeasurableSet (brisk (B:=B) R y):= (measurableSet_singleton _).prod (cooled_flag ..) -- tune ellipsis
lemma excite_meas : MeasurableSet {x: Realm B N R|excite R y x}:= (brisk_meas (B:=B) R y).compl
-- $p_o$ normalization even if p_o small. Require smallness later.
def paysP (y:ℝ) := (Training R B y).real (brisk R y)
def hit (P :Set (Realm B N R)):= ENNReal.ofReal (paysP (B:=B) R y)⁻¹ • ((Training R B y).restrict P) -- parsing desired ofReal INVERSE(real)
def coldM :Measure (Realm B N R):= hit R y (brisk R y)
def hotM :Measure (Realm B N R):= hit R y (brisk R y)ᶜ
instance hit_finite (P:Set (Realm B N R)): IsFiniteMeasure (hit R y P):=by unfold hit; apply Measure.smul_finite _ ENNReal.ofReal_ne_top
instance cold_fin : IsFiniteMeasure (coldM (B:=B) R y):=by unfold coldM; infer_instance
instance hot_fin : IsFiniteMeasure (hotM (B:=B) R y):=by unfold hotM; infer_instance
lemma payday : paysP (B:=B) R y=(sunny (B:=B) R y).real {u:Attire (B:=B) R|cooled R y u}:=by rw [paysP, Training,brisk,measureReal_prod_prod]; simp [Measure.real,count]
lemma payday_cap (h:Fast y): paysP (B:=B) R y ≤1:=by rw [payday]; haveI:= summerP (B:=B) R h; rw [←probReal_univ (μ:=sunny (B:=B) R y)]; exact measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
abbrev HumCost (D L:ℕ)(y:ℝ):= (L:ℝ)^3*(hBound D*Real.exp (-(1/4)*(heigh y)^2))
lemma salary (h:Fast y) : 1 -paysP (B:=B) R y ≤ HumCost B.D R.L.val y:=by
 haveI:= summerP (B:=B) R h; let V(i:Patio R):= {x:Attire (B:=B) R| heigh y≤ ‖x.1.1 i‖}; let μ:= sunny (B:=B) R y; have hp := (measureReal_compl (μ:=μ) (cooled_flag (B:=B) R y)); haveI:IsProbabilityMeasure μ:= summerP (B:=B) R h; rw [probReal_univ] at hp -- tune
 rw [payday,←hp]; -- tune
 rw [show {u:Attire (B:=B) R| cooled R y u}ᶜ=⋃ i,V i from ?_]; swap; · ext x; simp [cooled,humbug,V]
 apply (measureReal_iUnion_fintype_le _).trans; apply le_trans (sum_le_sum (g:=fun _=> hBound B.D*Real.exp (-(1/4)*(heigh y)^2)) ?_) ?_
 · intro i _; haveI:= paleQ h N; have ht:MeasurePreserving (fun x:Attire (B:=B) R=> x.1.1 i) μ (volts B.D y):= (measurePreserving_eval (fun _ : Patio R=> volts B.D y) i).comp ((measurePreserving_fst (ν:=hard (B:=B) R)).comp measurePreserving_fst) -- tune
   have hv:=vcost_tail B.D y (heigh y) (heigh_pos y).le; unfold Measure.real; let c:= hBound B.D* Real.exp (-(1/4)*(heigh y)^2); refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top ((ht.measure_preimage (tailw B.D _).nullMeasurableSet).le.trans hv)).trans ?_; rw [ENNReal.toReal_ofReal]; have he:= hbound_pos B.D; positivity
 simp only [HumCost,sum_const,nsmul_eq_mul,card_univ,Patio,Fintype.card_pi_const,Fintype.card_fin, Nat.cast_pow]; exact le_rfl
lemma salary_Q (hp:0<paysP (B:=B) R y) : IsProbabilityMeasure (coldM (B:=B) R y):=by
 constructor; unfold coldM hit; rw [Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul, ← show ENNReal.ofReal (paysP (B:=B) R y)= _ from ENNReal.ofReal_toReal (measure_ne_top (Training R B y) (brisk R y)), ← ENNReal.ofReal_mul (inv_pos.mpr hp).le, inv_mul_cancel₀ hp.ne', ENNReal.ofReal_one]
end YM.CF.BPress.House
