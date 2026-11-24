import YM.CF.BPress.Manna.Dish
/- Lemma:B-lastQ integrated. Shelf recurrence does not truncate core family cardinal. slack P rebounds.FrameCenters. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Manna
open Function Finset NormedSpace MeasureTheory Measure Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
attribute [local instance] Gauge.frobInner
variable {N:Side}{B:BandWidth}{A:Bands (More N) B} {R:Hangar (More N)}{H:Crew A}
open Huon Rates Env Mosaic Contour
variable {K:Rates}{Q D:SlotT A R}
abbrev kroot := estate 29
lemma presets (b:D⊆ Q): Q.card=(D.card+(NotT D Q).card)+(Middle D Q).card:=by
 rw [← card_union_of_disjoint (NotTD (Q:=Q) (D:=D)), add_comm]; exact (card_sdiff_add_card_eq_card (rejoin b)).symm
lemma middle_bound (D Q:SlotT A R): (Middle D Q).card≤ D.card*kroot:=by refine le_trans (card_le_card (show Middle D Q⊆ untouch D from fun i p=>?_)) (vista_card ..); obtain ⟨p,q⟩:= mem_sdiff.mp p; exact Classical.byContradiction fun e=> q (mem_union_right _ (Finset.mem_sdiff.mpr (show _ from ⟨p,e⟩)))
variable {C:ℝ} (H)
structure Trust (K:Rates)(b:ℝ) :Prop where
 bright : Fast H.y
 reputation : 1/2≤ paysP (B:=B) R H.y
 life : 0<b
 Lad : b≤ 1
 glow: coolCap K ≤ b
 bread: hotCap K R B.D H.y * (areaB R/b)^kroot ≤ b
variable {H}
namespace Trust
variable (p: Trust (R:=R) H K C)
include p
private lemma parcel (b:D⊆ Q) : ∫ x,basket K H D Q x ∂ Century A R H.y Q= ∏ i∈ Q,(∫ x, towel K H D Q i x ∂ hotM R H.y):=by
 let M(i:BlockY A R):= if i∈ Q then hotM (B:=B) R H.y else coldM R H.y; let K':= Century A R H.y Q; have hp:= pay_f p.bright p.reputation; haveI:= salary_Q (B:=B) R H.y hp; let f(i:BlockY A R)(x: Realm B N R):= if i∈Q then towel K H D Q i x else 1; have he: K'=Measure.pi M:=rfl
 haveI : ∀ i, SigmaFinite (M i):= by intro i; unfold M; split <;> infer_instance
 unfold basket; rw [show Century A R H.y Q= _ from he, show (fun x=>∏ i∈Q, towel K H D Q i (x i))=(fun x: Choir A R=>∏ i,f i (x i)) from ?_, integral_fintype_prod_eq_prod]; swap; · funext x; unfold f; rw [←prod_filter]; simp -- tune goal order
 rw [←prod_subset (Finset.subset_univ Q) (f:= fun i=> ∫ x,f i x∂ M i)]; swap; · intro i _ t; simp [f,M,t]
 exact prod_congr rfl (fun i p=>by simp only [f,p,M,ite_true])
private lemma hotP : 0 ≤ hotCap K R B.D H.y:=by unfold hotCap HumCost; have hp:= hbound_pos B.D; have hv:= zero_le_one.trans (AreaPos R); positivity
lemma portion (b:D⊆ Q) : ∫ x,basket K H D Q x ∂ Century A R H.y Q ≤ C^Q.card:=by
 let w(i:BlockY A R):=∫ x,towel K H D Q i x ∂ hotM R H.y; let Z:= hotCap K R B.D H.y; let V:=areaB R; let u:=(NotT D Q); let v:=Middle D Q; have p0(i):0≤w i:= integral_nonneg (fun _=> θ_pos ..); have pv:= p.life; have hv:1 ≤ V:= AreaPos R; have hv':0 < V:= zero_lt_one.trans_le hv; rw [p.parcel b, metag b w]; -- tune Name
 have h₀(F:SlotT A R):0≤ ∏ i∈F, w i:=prod_nonneg fun i _=> p0 i
 have ht: ∏ i∈D,w i ≤ Z^D.card:=by rw [←prod_const]; refine Finset.prod_le_prod (fun i _=>p0 i) (?_ ); intro i h; unfold w; simp_rw [towel,if_pos h]; exact bpt K p.bright p.reputation
 have hh: ∏ i∈u,w i ≤ C^u.card:=by rw [←prod_const]; refine Finset.prod_le_prod (fun i _=>p0 i) (?_ ); intro i h; unfold w; simp_rw [towel, if_neg (fun a=>Finset.disjoint_left.mp NotTD a h),if_pos (show i∈ NotT D Q from h)]; exact (gpt K p.bright p.reputation).trans p.glow -- tune simp implicit i
 have hx :∏ i∈v,w i≤ V^v.card:=by rw [←prod_const]; refine Finset.prod_le_prod (fun i _=>p0 i) (?_); intro i h; obtain ⟨_,t⟩:= mem_sdiff.mp (show i∈v from h); have hT:i∉ D:= fun u=> t (mem_union_left (NotT D Q) u); have hu:i∉ NotT D Q:=fun u=> t (mem_union_right D u); unfold w; simp_rw [towel,if_neg hT,if_neg hu,integral_const]; simp only [smul_eq_mul,mul_one]; exact cap_area p.bright p.reputation -- tune
 have hz:0 ≤ Z:= p.hotP; refine (mul_le_mul (mul_le_mul ht hh (h₀ _) (pow_nonneg hz _)) hx (h₀ _) (by positivity)).trans ?_; rw [presets b,pow_add,pow_add]; calc
    _ = (Z^D.card*(V/C)^v.card)*(C^u.card*C^v.card) := by rw [div_pow]; field_simp -- tune ring powers
    _ ≤ ((Z*(V/C)^kroot)^D.card)*(C^u.card*C^v.card):=by
       rw [mul_pow,← pow_mul]; gcongr
       next=> exact (one_le_div pv).mpr (p.Lad.trans hv)
       next=> rw [mul_comm]; exact middle_bound ..
    _ ≤ _:= by rw [mul_assoc]; gcongr ?_ ^ _ * _; apply p.bread -- tune
lemma sweet (f: Choir A R→ℂ){T:Visit A R H→ℂ}(t:PaidQ Q K H T f): ∫ x,‖f x‖∂ Century A R H.y Q ≤ (2*C)^Q.card:=by
 let V:= Century A R H.y Q; haveI:= salary_Q R H.y (pay_f p.bright p.reputation); haveI : IsFiniteMeasure V:= by unfold V Century; infer_instance -- tune instance.P.C.Contour defaults not Prob for this need add.
 let G:=fun (D:SlotT A R) x=>basket K H D Q x; have hv(i):Integrable (G i) V:= Envelope.integrable (basket_env ..) V
 refine (integral_mono (integrableX t.env V|>.norm) (integrable_finsetSum Q.powerset (fun i _=>hv i)) (stars t)).trans ?_; rw [integral_finsetSum _ (fun i _=> hv i)]; refine (sum_le_sum (fun i h=> p.portion (mem_powerset.mp h))).trans_eq ?_; rw [sum_const,nsmul_eq_mul,card_powerset,mul_pow]; push_cast; rfl -- tune order integral.Inst
end Trust
end YM.CF.BPress.Manna
