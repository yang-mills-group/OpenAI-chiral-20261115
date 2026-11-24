import YM.SU5.FiniteGaugeData.Steam.Contest
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
-- examples of operators. all words `risky=copies indicator * W`, constants pay. 'rare finite law' absolute norms even though complex signed read; on this course. moving supports okay if signposted explicit waits. `UnsafeSp` counts cover faces; possibly multiple faces choices. trigger if ANY; simplifies conditioning later. orientation Law. costs bound includes union of both, with parameter trust (ℕ). membership no continuum. 
namespace Quest
open Window.Steve
variable {Λ:Py.Rate.LocalLimit.Preparation}{l:ℕ}
variable (K:Calibration)(w:Set Cover)(Y: Finset (Face ℤ)) (t:ℝ)
open scoped Classical
abbrev surface (i:Face ℤ): Finset Cover:= (visits i.1 (square i.2.val.1 i.2.val.2)).toFinset
def carpet (Y: Finset (Face ℤ)) := Y.biUnion surface
def alarm (x:PairsC):Prop:= ∃ i∈ Y,t < SU.group.chord (faceValue x.1 i)
def strike : PairsC→ℂ := fun x=> if alarm Y t x then 1 else 0
lemma crimson_trigger : Coeff true (carpet Y) (strike Y t):= by
 have h:MeasurableSet (setOf (alarm Y t)):=by
    unfold alarm; simp_rw [← exists_prop, Set.setOf_exists]; exact MeasurableSet.iUnion fun i=> MeasurableSet.iUnion fun h=> isOpen_lt continuous_const (by unfold faceValue; fun_prop)|>.measurableSet
 refine ⟨fun _=>by contradiction, ⟨Measurable.ite h measurable_const measurable_const,1, fun i=>?_⟩,?_⟩
 · unfold strike; split <;> simp
 intro x y u v; unfold strike; refine ite_congr (propext ?_) (fun _=>rfl) (fun _=>rfl); unfold alarm
 have he(i:Face ℤ)(p:i∈Y):faceValue x.1 i=faceValue y.1 i:= travel_local _ _ _ _ fun e h k=> u e (mem_biUnion.mpr ⟨i,p,List.mem_toFinset.mpr h⟩) (mem_biUnion.mpr ⟨i,p,List.mem_toFinset.mpr k⟩)
 refine exists_congr fun i=> and_congr_right fun h=> ?_; rw [he i h]
variable {n m:Side}
def troubles := scalar K (strike Y t)
lemma undone : InTest K true (carpet Y) false (troubles K Y t):=.seed (crimson_trigger Y t)
lemma hovers (x:Fields (K.c m)): ‖troubles K Y t m x‖ ≤ 1:=by change ‖(if _ then (1:ℂ) else 0) • (1:FC _)‖≤_; split <;> simp
lemma press_face (p:Face ℤ)(x:Fields n): faceValue x.1 (wrap (More n) p.1,p.2)=faceValue (onC n x.1) p:= by unfold onC faceValue; rw [travel_at]; simp
private lemma w_image(x:Cover)(l:Walk){z:Seat n}(h:z∈visits (wrap (More n) x) l): z∈region (visits x l).toFinset n:=by
 induction l generalizing x z with
 | nil=> exact mem_image.mpr ⟨_, (show x∈ (visits x []).toFinset by simp [visits]),(List.mem_singleton.mp h).symm⟩
 | cons i l ih=> rcases List.mem_cons.mp h with (rfl|v); exact mem_image.mpr ⟨_,(show x∈_ from List.mem_toFinset.mpr (show x∈ visits x _ from List.mem_cons_self)),rfl⟩; rw [show wrap (More n) x + i.vec= wrap _ (x+i.vec) from ?_] at v; obtain ⟨u,k,e⟩:= mem_image.mp (ih (x+i.vec) v); exact mem_image.mpr ⟨u,List.mem_toFinset.mpr (List.mem_cons_of_mem x (List.mem_toFinset.mp k)),e⟩; rw [map_add,wrap_vec]
lemma tripped (i:Side): Glints 1 (region (carpet Y) (K.c i)) t (troubles K Y t i):=by
 intro x u; by_cases h:alarm Y t (Prod.map (onC _) (onC _) x); swap
 · apply False.elim (u ?_); exact (by unfold troubles scalar strike; change ¬ alarm Y t (onC _ x.1,onC _ x.2) at h; rw [if_neg h,zero_smul])
 obtain ⟨z,v,g⟩:=h; let p: admiss (K.c i):= (wrap _ z.1,z.2); refine card_pos.mpr ⟨p,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,by rw [show faceValue x.1 p=_ from press_face z x]; exact g⟩,?_⟩⟩
 intro w k; exact Finset.image_subset_image (show surface z ⊆ carpet Y from fun s h=>mem_biUnion.mpr ⟨z,v,h⟩) (w_image z.1 _ (List.mem_toFinset.mp k))
-- use Tint orientation & durable. SU gauge both.
lemma qualified : Tint.Durable K (troubles K Y t):=by
 intro m g x -- tune
 have ht(i:Face ℤ): SU.group.chord (faceValue (onC (K.c m) (simultaneous g x).1) i)=SU.group.chord (faceValue (onC (K.c m) x.1) i):=by rw [←press_face i (simultaneous g x), ←press_face i x]; exact (congrArg SU.group.chord (face_gauge (K:=SU.E) g x.1 (wrap _ i.1,i.2))).trans (SU.group.chord_conj ..)
 unfold troubles scalar strike; simp_rw [twist_scalar,map_one,alarm,ht]; congr 2
-- cost lemma rarity etc
open Py Py.Rate Steam LocalLimit Steam Preparation Journey
variable (Q:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x){s i:ℕ} {f:Family (tent Q h)} {u v:ℕ→ℕ} {E:ℕ→ Family (tent Q h)→ℂ} {I:ℕ→Family (tent Q h)→ℕ→ℂ}
    {r c:ℝ} (X:Universal Q h u v I E)(H:r ≥ 0)
local notation "μ"=> (tent Q h)
local notation "Ω"=> (Pressure.temp (Vale.hat Λ.R.L Λ.x s))
variable (C:Club Q r s)
lemma Glints.shrink {T S:Support (More n)}{b:ℕ}{f g:Mark n}(c:Glints b S t f)(e:S⊆T): Glints b T t (f*g):= fun x h=> (c x (left_ne_zero_of_mul h)).trans (card_le_card (show glitches S t _ ⊆ glitches T t _ from fun i h=> mem_filter.mpr ⟨(mem_filter.mp h).1,Subset.trans (mem_filter.mp h).2 e⟩))
include C X H
lemma coverage {S:Finset Cover} (p:InTest (tent Q h) true S false f) (t':0≤c)(g:∀ i x,‖f i x‖≤ c) (D:ℕ)(V:∀ i:Axis,∃ p:ℤ,∀ x∈ carpet Y∪ S,p ≤ x i∧ x i≤ p+D): ‖E s ((troubles μ Y Ω) * f)‖ ≤ c * Real.exp (- frost Λ.K.top.clip (Vale.hat Λ.R.L Λ.x s)) * Real.exp (slopeF Λ.W r * ((4:ℝ)*(D+addgap μ:ℕ))^4):=by
 let l:=carpet Y ∪ S
 apply chosen_M X C (show InTest μ true l false (troubles μ Y Ω * f) from ((undone μ Y Ω).mono subset_union_left).mul (p.mono subset_union_right)) t' H _ D V
 refine Eventually.of_forall (fun i=>?_); rw [sold_v]; let b:= troubles μ Y Ω; let m:=momentm Q (u i) s
 apply castT (terrain Q h (Q.ir _) s) l _ (show Glints 1 (region l ((tent Q h).c m)) Ω ((b*f) m) from Glints.shrink Ω (tripped μ Y Ω m) (Finset.image_subset_image subset_union_left))
 intro x; change ‖b m x * f m x‖ ≤ c; exact (norm_mul_le ..).trans ((mul_le_mul (hovers μ Y Ω _) (g _ x) (norm_nonneg _) zero_le_one).trans (one_mul c).le)
where castT {Λ t':ℝ} {s u:Side}(e:s=u)(L:Finset Cover)(f:Mark s)(g:Glints 1 (region L s) t' f)(v:∀ x,‖f x‖ ≤ Λ): (∀ x, ‖(show Mark u from e▸f) x‖ ≤ Λ) ∧ Glints 1 (region L u) t' (e▸f):=by subst s; exact ⟨v,g⟩
end Quest
end YM.CF.Buffered.Afterglow.Hierarchy
