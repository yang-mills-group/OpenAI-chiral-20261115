import YM.SU5.Registration.Momenta.PublicArt
/-!
 # Access even with bounded rooms in local algebra. Cyclic on THIS R.
 No claim about any one fixed ball. Supports in comparisons use exactly those prices.
 Need older M10-11 budgets even though no requests of rotation or spectrum at here.
 Still need to certify content, not asserting large-room exhaustion of all gauge observables of SU(5).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Carton
open Function Set Filter MeasureTheory Measure Complex Submodule SatinRegistration
open Boundary Probe Mink Mink.Poincare Multiplier Roy Spectral OS.Semigroup SatinEdge.RealSheet
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder
variable {H:Hilbert}{S: _root_.YM.OS.Semigroup H timeAxis}{V:Type*}[AddCommGroup V][Module ℂ V]
variable (B:Carton S V)(J:JMap V)(u:Remembers B J)
local notation "D"=> radial S
local notation "G"=> bands S
local notation "R"=> B.station
local notation "L"=> B.joinT
local notation "F'"=> B.pointGrade
local notation "ε"=> B.citizen
open WView Palette
variable {F:InkWaves V}{W:WView V}(g:InkPort B F W)(K:Courts V)(m:K.Carriage F){n:ℕ}
-- M5 `enact` estimate strong inside domain. polish.
open Grading
lemma opt_tariff (v:V){ι:Type*}(l:Filter ι)(T:ι→ Test4)(f:Test4)(e:Tendsto T l (𝓝 f)) : ∀ k, ∃ i C', ∀ᶠ x in l, ∀ w:D, (G).budget k (B.black v (T x) w).1 ≤ C'*(G).budget i w.val:=by
 let A:= fun t:ℝ≥0 => B.bar t v; obtain ⟨r,C,h,q⟩:= cold_paid S A (B.price v) (B.coherent v); intro k; let u(f:Test4):= (∑' n,tariffW n)*meterLoss r k C f timeAxis
 have he(f:Test4)(w:D) : (G).budget k (B.black v f w).1 ≤ u f*(G).budget (k+2+r+r) w.val:= enact_tariff S _ _ q f w k -- instance inference
 refine ⟨k+2+r+r,u f+1,?_⟩; have hu:Continuous u:= (meter_continuous r k C timeAxis).const_mul _
 exact (((hu.tendsto f).comp e).eventually (gt_mem_nhds (lt_add_one _))).mono fun i p w=> (he (T i) w).trans (mul_le_mul_of_nonneg_right (show u (T i)<_ from p).le ((G).budget_nonneg _ _))
lemma chairs (v:V){ι:Type*}(l:Filter ι)(T:ι→Test4)(f:Test4)(e:Tendsto T l (𝓝 f)) (x:D) (X:ι→ D) (h:(G).Approaches l X x): (G).Approaches l (fun i=> B.black v (T i) (X i)) (B.black v f x) := by
 apply (G).approaches_apply (fun i=> B.black v (T i)) (B.black v f); exact B.opt_tariff v l T f e; intro z; exact enact_distribution S _ _ l T e z; exact h
-- choose k ↑∞ for *all* independent probes.
abbrev portrayedMap (k:ℕ)(p:MarkWords V): MarkWords V:= p.map (fun x=> (x.1,cap k x.2))
lemma chairs_words (p :MarkWords V): (G).Approaches atTop (fun k=> B.row (portrayedMap k p)) (B.row p):=by
 induction p with
 | nil=> exact fun k=>by simp only [portrayedMap,List.map_nil,sub_self,budget,due,map_zero,norm_zero,mul_zero,tsum_zero]; exact tendsto_const_nhds
 | cons x p ih=> exact B.chairs x.1 atTop _ x.2 (persistent _) _ _ ih
lemma chairs_capped (p:MarkWords V) : Tendsto (fun k=> B.engaged (portrayedMap k p)) atTop (𝓝 (B.engaged p)):= by
 apply tendsto_subtype_rng.mpr; exact Approaches.hilbert (G) (B.chairs_words p)
lemma compact_county (p:MarkWords V)(v:∀ i∈p, HasCompactSupport ⇑i.2): ∃ U: Set E4, IsCompact U ∧ B.voice p ∈ B.county U:=by
 suffices g:∃ U:Set E4, IsCompact U ∧ ∀ i∈p, tsupport i.2 ⊆ U by obtain ⟨U,h,u⟩:=g; exact ⟨U,h,B.passportMark U _ u⟩

 induction p with
 | nil=> exact ⟨∅,isCompact_empty,by simp⟩
 | cons i p ih=>
   obtain ⟨U,e,t⟩:= ih (fun j h=> v j (List.mem_cons_of_mem _ h)); refine ⟨tsupport i.2∪U, (IsCompact.union (v i (by simp)) e), fun j h=>?_⟩; exact (List.mem_cons.mp h).elim (fun p=>p ▸ subset_union_left) (fun p=>(t j p).trans subset_union_right) -- p ▸ orientation tune
noncomputable def openBook : Submodule ℂ B.station:= Submodule.span ℂ {x | ∃ (U:Set E4), Bornology.IsBounded U ∧ IsOpen U ∧ ∃ a∈ B.county U,(a B.pointRoot).val=x}
lemma seed_compact (p:MarkWords V)(v:∀ i∈ p, HasCompactSupport ⇑i.2): (B.evaluate p).val∈ B.openBook:=by
 obtain ⟨U,e,t⟩:= B.compact_county p v; obtain ⟨r,hr⟩:= e.isBounded.subset_ball (0:E4); refine subset_span ⟨ Metric.ball 0 r, Metric.isBounded_ball,Metric.isOpen_ball, B.voice p, (B.isotone hr t),?_⟩; unfold pointRoot; rw [B.spoken,List.append_nil]
lemma bounded_cyclic : Dense (B.openBook:Set B.station):= by
 intro x; have he:x∈ _root_.closure (B.openBook:Set B.station):= ?_; exact he
 refine closure_minimal (s:= (ε:Set B.station)) (?_) isClosed_closure (B.populous x)
 change ε ≤ B.openBook.topologicalClosure; apply Submodule.span_le.mpr; rintro _ ⟨p,rfl⟩; refine mem_closure_of_tendsto (B.chairs_capped p) (Eventually.of_forall fun k=> B.seed_compact (portrayedMap k p) (fun i v=> ?_))
 obtain ⟨a,h,rfl⟩:=List.mem_map.mp v; exact finite_cap k
-- determination of WView.expect even testing the bounded support calls only. (no Eu budget needed)
variable {V':Type*}[AddCommGroup V'][Module ℂ V'](W:WView V)(W':WView V')(P: V→V')
lemma limited_answers : (∀ n (x:Fin n→V), W.W n x=W'.W n (P ∘ x)) ↔ ∀ n (v:Fin n→V)(f:Fin n→Test4), (∀ i,HasCompactSupport ⇑(f i))→ W.expect (List.ofFn fun i=>(v i,f i))= W'.expect (List.ofFn fun i=>(P (v i), f i)):=by
 refine ⟨fun h n v f _=> (material_eq P).1 h n v f,fun q=> (material_eq P).2 ?_⟩; intro n v f; rw [W.expect_ofFn,W'.expect_ofFn];
 let X(k:ℕ)(i:Fin n):= cap k (f i); have ht:Tendsto X atTop (𝓝 f):= tendsto_pi_nhds.mpr fun i=> persistent (f i); have h:= ((Joint.jointCont n).tendsto f).comp ht
 apply tendsto_nhds_unique_of_eventuallyEq ((W.W n v).continuous.tendsto _|>.comp h) ((W'.W n (P ∘ v)).continuous.tendsto _|>.comp h); refine Eventually.of_forall fun k=> ?_
 have he:= q n v (X k) (fun i=> finite_cap k); rw [expect_ofFn, expect_ofFn] at he; exact he
end YM.SatinWFixed.Carton
