import YM.SU5.FiniteGaugeData.Tower.CompactFlight
import Mathlib.Analysis.InnerProductSpace.ProdL2
/-!
# Projection retention toolkit. Two-axis regularizing of common slots.

Implement the approach suggested in Tower/GermUnit (direct sum). Not assuming continuity
in a common slot to retain equality *after projection* there. We require
actual equality when varying through marks in that slot.
Also supply one-sided retention (by passing down to boundary point after two-sided
in interior, not assuming test continuity across that point).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectionAnalysis
open Function Set Filter Metric
open CF.Buffered.Afterglow.Tower MeshClock Germ
open scoped Topology InnerProductSpace ENNReal
variable {H H' : Hilbert} {Γ : AddSubgroup ℝ} (P : Players Γ H) (Q : Players Γ H')
local notation "F"=> WithLp 2 (H.space × H'.space)
abbrev twins (H H' : Hilbert) : Hilbert where
  space := WithLp 2 (H.space × H'.space)
local notation "L"=> WithLp.fstL 2 ℂ H.space H'.space
local notation "R"=> WithLp.sndL 2 ℂ H.space H'.space
local notation "Z"=> WithLp.prodContinuousLinearEquiv 2 ℂ H.space H'.space
noncomputable def jointband (i : Γ) : (twins H H').Op := (Z).symm.toContinuousLinearMap ∘L (((P.play i).comp L).prod ((Q.play i).comp R))
local notation "B" i:max=> jointband P Q i
lemma band_prices (i : Γ) (u : F) : ‖(B i) u‖=‖u‖ := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  change ‖(show F from ((B i) u))‖^2= _; simp_rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖P.play i (L u)‖^2+ ‖Q.play i (R u)‖^2= _; rw [P.wins H,Q.wins H']; rfl
noncomputable def jointBand : Players Γ (twins H H') where
  play := jointband P Q
  play_zero := by
    ext1 x; unfold jointband; rw [P.play_zero,Q.play_zero]; rfl
  pulls i x := (band_prices P Q i x).le
  piles i j := by ext1 x; unfold jointband; rw [←P.piles,←Q.piles]; rfl
local notation "S"=> jointBand P Q
lemma twin_sure (x : F) : x∈ (S).lives (twins H H') ↔ L x ∈ P.lives H ∧ R x ∈ Q.lives H' := by
  change ContinuousAt (fun i=>(S).play i (x:twins H H')) 0 ↔ ContinuousAt (fun i=>P.play i (L x)) 0 ∧ ContinuousAt (fun i=>Q.play i (R x)) 0
  constructor
  · intro p
    exact ⟨(L).continuous.continuousAt.comp p, (R).continuous.continuousAt.comp p⟩
  rintro ⟨p,v⟩
  exact (Z).symm.continuous.continuousAt.comp (p.prodMk v)
lemma radiates (x : F) : (S).pi_c x=(Z).symm (P.pi_c (L x), Q.pi_c (R x)):=by
  let K:= (twins H H'); haveI κ : CompleteSpace ((S).lives (twins H H')) := Players.complete (S) -- tune
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((twin_sure P Q ((Z).symm (P.pi_c (L x), Q.pi_c (R x)))).mpr ⟨P.repaired _,Q.repaired _⟩)
  intro v hv
  obtain ⟨t,w⟩:= (twin_sure P Q _).mp hv
  change inner ℂ ((L x)-P.pi_c (L x)) (L (v:F)) + inner ℂ ((R x)-Q.pi_c (R x)) (R v)= _
  rw [show inner ℂ ((L x)-P.pi_c (L x)) (L v)=0 from Submodule.starProjection_inner_eq_zero _ _ t, show inner ℂ ((R x)-Q.pi_c (R x)) (R v)=0 from Submodule.starProjection_inner_eq_zero _ _ w,add_zero]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
lemma tandem (l : H→L[ℂ]Y) (l' : H'→L[ℂ]Y) (x : H) (y : H')
    (h : (fun i:Γ => l (P.play i x)) =ᶠ[𝓝 0] (fun i=> l' (Q.play i y))) :
    l (P.pi_c x)=l' (Q.pi_c y):=by
 let T : WithLp 2 (H.space×H'.space) →L[ℂ] Y := (l.comp L)-(l'.comp R)
 let v : F:=(Z).symm (x,y)
 have he : (fun i:Γ => T ((jointBand P Q).play i v)) =ᶠ[𝓝 0] (fun _=> (0:Y)):= h.mono fun j k=> (sub_eq_zero.mpr k : l (P.play j x)-l' (Q.play j y)=0)
 have hp : T v= (0:Y):=by have h0 : T ((jointBand P Q).play 0 v)=0:= he.self_of_nhds; rw [(jointBand P Q).play_zero] at h0; exact h0
 apply sub_eq_zero.mp
 have ht : ContinuousAt (fun i:Γ=>T (jointBand P Q|>.play i v)) (0:Γ):= (continuousAt_const : ContinuousAt (fun _ : Γ=>(0:Y)) 0).congr he.symm
 have hx := (S).retain T v ht
 rw [hp,radiates] at hx; exact hx

include P
lemma retain_ge (l : H→L[ℂ]Y) (d : Dense (Γ:Set ℝ)) (x : H) (h : ContinuousOn (fun i:Γ => l (P.play i x)) (Set.Ici 0))
    (v : Γ) (p : 0 ≤ (v:ℝ)) : l (P.play v (P.pi_c x))=l (P.play v x):=by
 have hv(i:Γ)(q:0<(i:ℝ)) : l (P.play i (P.pi_c x))=l (P.play i x):= P.retains_at l x i ((h i q.le).continuousAt (by
    have ht : ∀ᶠ b:Γ in 𝓝 i,0<(b:ℝ):= continuous_subtype_val.continuousAt.tendsto.eventually (lt_mem_nhds q)
    exact ht.mono fun _ t=> t.le))
 let U : Γ → Y:=fun v:Γ=> l (P.route d v.val x)
 have hu: Continuous U:= (l.continuous.comp ((P.route_uc d x).continuous)).comp continuous_subtype_val
 rcases lt_or_eq_of_le p with p|p; exact hv v p
 have hx: v=0:=Subtype.ext p.symm; subst v
 have hd: (0:Γ)∈ closure {b:Γ|0<(b:ℝ)}:=by
   apply Metric.mem_closure_iff.mpr; intro ε e; obtain ⟨b,u,v⟩:= d.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr e)
   let i:Γ:= ⟨b,?_⟩; refine ⟨i,?_,?_⟩ -- order
   all_goals first | exact u | exact v.1 | (change dist (0:ℝ) b < ε; rw [dist_comm,Real.dist_0_eq_abs,abs_of_nonneg (show 0≤b from v.1.le)]; exact v.2)
 letI := mem_closure_iff_nhdsWithin_neBot.mp hd
 apply tendsto_nhds_unique (f:=fun i:Γ=> l (P.play i x)) (l:=𝓝[{b:Γ|0<(b:ℝ)}] (0:Γ)) -- arg x maybe wrong
 · have hp := (hu.continuousAt (x:=0)).tendsto.mono_left (nhdsWithin_le_nhds (s:={b:Γ|0<(b:ℝ)})); rw [show U 0=l (P.play 0 (P.pi_c x)) from congrArg l (P.route_on d 0 _)] at hp
   apply hp.congr'; filter_upwards [self_mem_nhdsWithin] with i v; exact (congrArg l (P.route_on d i _)).trans (hv i v)
 exact (h _ (show (0:Γ)∈ Set.Ici 0 from Set.mem_Ici.mpr (le_refl (0:Γ)))).mono (fun i (v:0<(i.val:ℝ))=> v.le)
end YM.SelectionAnalysis
#print axioms YM.SelectionAnalysis.tandem
#print axioms YM.SelectionAnalysis.retain_ge
