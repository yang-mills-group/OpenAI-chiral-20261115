import ZecaFleet
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


open Poin Vp.Folio
variable {H:Hilbert}{ι:Type}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)(Ω:H.space)
 (hΩ:∀x:E4,M S x Ω=Ω)
local notation "a"=>timeAxis
local notation "Λ"=>List (Item G.Chip)
local notation "φ"=>face S Ω G.dep G.grade
local notation "ψ"=>role S Ω G.dep G.grade

variable (d:E4→ₗ[ℝ]ℝ) (e:d (basis timeAxis)=0)

open Celeritas
variable (HF:Cinema S) (u:Cross timeAxis) (hu:‖u‖≤1) (hd:0<d u.val)

variable (R:ℝ)
open Submodule
local notation "X"=>FarJ S G Ω d R
local notation "Y"=>ArcJ S G Ω d
include hd hΩ
lemma sofar (x:H.space)(k:x∈ ArcJ S G Ω d): ∀ᶠ q:ℝ in atTop,S.U (q • u) x∈ FarJ S G Ω d R:=by
 obtain ⟨L,v,h,rfl⟩:= ‹x∈Y›
 have P:∀ᶠ q:ℝ in atTop,∀i∈L, R < q*d u.val+d i.2:= by
   clear k h v
   induction L with
   | nil=>simp
   | cons i L ih=>
     filter_upwards [ih, eventually_gt_atTop ((R-d i.2)/ d u.val)] with q v w
     exact List.forall_mem_cons.mpr ⟨by rw [← sub_lt_iff_lt_add];exact (div_lt_iff₀ hd).mp w,v⟩
 filter_upwards [P] with q k
 let m:=q • u
 obtain ⟨b,y⟩:=side_face S G Ω hΩ m 0 L v
 refine ⟨_, b, lifted G d m.val L h, y.symm,?_⟩
 intro i hi
 obtain ⟨i,v,rfl⟩:=List.mem_map.mp hi
 right; change R<d (q • u.val + i.2)
 rw [map_add,map_smul]; exact k i v

include HF hu
lemma fax (t:ℝ≥0)(h:0<t)(x:H.space)(v:x∈ArcJ S G Ω d):
 S.E t x∈ Boxed (FarJ S G Ω d R):=by
 let p:=(Boxed (X)).starProjection
 let A(y:ℝ):= cup S t HF u hu y x
 have g₀ : AnalyticOnNhd ℝ A univ:=by
   intro y _
   have j: (y:ℂ)∈ lanes (t:ℝ):=by unfold lanes; simp; exact h
   have b:AnalyticAt ℂ (fun y=> cup S t HF u hu y x) y:=
     ((ContinuousLinearMap.apply ℂ H.space x).analyticAt _).comp
     (cup_A S u t HF hu _ j)
   exact b.restrictScalars.comp (Complex.ofRealCLM.analyticAt _)
 have b(y:ℝ): A y=S.U (y • u) (S.E t x):=DFunLike.congr_fun (credit_h S u t y HF hu h) x
 have i:=sofar S G Ω hΩ d u hd R _ (warmWord S G Ω hΩ d t x v)
 obtain ⟨c,hc⟩:=eventually_atTop.mp i
 have k: p ∘ A =ᶠ[𝓝 (c+1)] A:=by
   filter_upwards [le_mem_nhds (show c<c+1 by linarith)] with y v
   apply Submodule.starProjection_eq_self_iff.mpr
   rw [b];exact grown X _ (hc y v)
 let L:=p.restrictScalars ℝ
 have g: AnalyticOnNhd ℝ (p ∘ A) univ:=fun y j=> (L.analyticAt _).comp (g₀ y j)

 have o: A 0 ∈ Boxed (X):= Submodule.starProjection_eq_self_iff.mp
    (g.eqOn_of_preconnected_of_eventuallyEq g₀ isPreconnected_univ (Set.mem_univ _) k (show 0∈Set.univ from Set.mem_univ (0:ℝ)))
 rw [b,zero_smul,S.uZero] at o;exact o

lemma farSeed: ArcJ S G Ω d⊆ Boxed (FarJ S G Ω d R):=by
 intro x p
 have h:=((S.continuousE x).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ≥0)))
 suffices S.E 0 x∈Boxed (X) by rw [S.eZero] at this;exact this
 exact (show IsClosed (Boxed (X):Set H.space) from isClosed_closure).mem_of_tendsto h
     ((show ∀ᶠ i in 𝓝[>] (0:ℝ≥0), 0 < i from self_mem_nhdsWithin).mono fun q w=> fax S G Ω hΩ d HF u hu hd R q w x p)
include e
lemma tickets (p:Filled S G Ω) : Annihilated S (FarJ S G Ω d R):=by
 apply raze
 have i:=fun b=> farSeed S G Ω hΩ d HF u hu hd b
 have k:=evergreen Y S G Ω p (eventFern S G Ω hΩ d (i 0) e)
 have j : Boxed (X) = ⊤:=by
   apply eq_top_iff.mpr;intro x _
   exact (span ℂ Y).topologicalClosure_minimal (span_le.mpr (i R)) isClosed_closure (k x)
 intro x;exact show x∈Boxed (X) from j ▸ mem_top
