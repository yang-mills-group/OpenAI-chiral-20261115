import YM.CF.BPress.Manna.Leaves
/- corner rates.prob.H.Micro.ρ.OK. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Manna
open Function Finset NormedSpace MeasureTheory Measure Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A:Bands (More N) B} {R:Hangar (More N)}{H:Crew A}
open Huon Rates Env Mosaic
variable (K:Rates)
def Bad0 (y:ℝ)(x:Realm B N R):ℝ:= Real.exp K.bad*(Real.exp (-K.severe) + if cooled R y x.2 then 0 else 1)
def Good0 (x:Realm B N R):ℝ:= if curious x then Real.exp (-K.pay) else 0
variable {y:ℝ}
lemma bp(x:Realm B N R):0≤ Bad0 K y x:=by unfold Bad0; split <;> positivity
lemma gp(x:Realm B N R):0≤ Good0 K x:=by unfold Good0; split; positivity; rfl
lemma Bbe : Envelope (Bad0 (B:=B) (R:=R) K y):= Envelope.mul (Envelope.const _) ((Envelope.const _).add (Law.switchP (measurable_snd (cooled_flag ..)) (Envelope.const _) (Envelope.const _))) -- tune y
lemma Gbe : Envelope (Good0 (B:=B) (R:=R) K):= Law.switchP care (Envelope.const _) (Envelope.const _)
lemma relax (x:Realm B N R)(p:unholy R y x): Real.exp K.bad* (if spent x then Real.exp (-K.severe) else 1) ≤ Bad0 K y x:=by
 unfold Bad0; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; split; next h=> apply le_add_of_nonneg_right; split <;> norm_num
 next h=> obtain ⟨i,q⟩:=p; have ht: ¬cooled R y x.2:=fun t=> t ⟨i,q.resolve_left (fun v=>h ⟨_,v⟩)⟩; rw [if_neg ht]; exact le_add_of_nonneg_left (Real.exp_pos _).le

def hotCap (R:Hangar (More N))(D:ℕ)(y:ℝ):= Real.exp K.bad * areaB R * (Real.exp (-K.severe)+HumCost D R.L.val y)
def coolCap := 8*Real.exp (-K.pay)
variable (z:Fast y) (r:1/2≤ paysP (B:=B) R y)
include z r
lemma bpt : ∫ i,Bad0 K y i∂hotM (B:=B) R y ≤ hotCap K R B.D y:=by
 let S:={x:Realm B N R| ¬cooled R y x.2}; let M:= hotM (B:=B) R y; let f(x:Realm B N R):= S.indicator (fun _=> (1:ℝ)) x; have hm(i: Realm B N R): (if cooled R y i.2 then (0:ℝ) else 1)=f i:=by unfold f Set.indicator; simp only [S,Set.mem_setOf]; split <;> simp_all -- tune
 have he:MeasurableSet S:=measurable_snd (cooled_flag ..).compl; unfold Bad0; simp_rw [hm]; rw [integral_const_mul, integral_add (integrable_const _) ((integrable_const (μ:=M) (1:ℝ)).indicator he)]
 rw [integral_const,integral_indicator he,setIntegral_const,smul_eq_mul,smul_eq_mul,mul_one, hotCap,mul_assoc,mul_add (areaB R)]; exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right (cap_area z r) (Real.exp_pos _).le) (caption z r)) (Real.exp_pos _).le
lemma gpt : ∫ i,Good0 K i∂ hotM (B:=B) R y ≤ coolCap K:=by
 let S:={x:Realm B N R| curious x}; have he : (Good0 (R:=R) (B:=B) K)=S.indicator (fun i=>Real.exp (-K.pay)):= by ext i; by_cases h:curious i<;> simp [Good0,h,S,Set.indicator]
 rw [he,integral_indicator care,setIntegral_const, smul_eq_mul]; exact mul_le_mul_of_nonneg_right (slim z r) (Real.exp_pos _).le
omit z r
abbrev fallout (H:Crew A) (x: Choir A R)(T:SlotT A R):= (debris H x T).filter fun i=> spent (x i)
lemma spent_at (x: Choir A R)(T: SlotT A R): (fallout H x T).card ≤ (ice x T).card:=by
 suffices h : fallout H x T⊆ (ice x T).image (own A R) from (card_le_card h).trans card_image_le
 intro i g; obtain ⟨p,v,h⟩:= mem_filter.mp g; rw [mem_image]; let z:=porch A R i v; refine ⟨z,mem_filter.mpr ⟨ (?_), porch_own A R i v|>.symm ▸ (mem_inter.mp p).2⟩,porch_own ..⟩; exact (beset_me ..).2 (by rw [show gather A R (icon A R x) z=(x i).1 v from gather_p A R _ i v]; exact h)
end YM.CF.BPress.Manna
