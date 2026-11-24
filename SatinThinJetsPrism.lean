import SatinThinJetsMeshes
/-! # Dense thermal jets, choose in any open cross-channel test
        without losing to a disconnected power -/
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex
open OS.Semigroup
open scoped NNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j : Axis} (S : OS.Semigroup H j) (Y : ℝ → H)
variable {s : ℝ}

/-- `n` indexes the `(n+1)`-th coefficient. Don't accept a term at order zero. -/
abbrev Prism := ℕ→₀ℂ

def jets (s:ℝ): Prism→ₗ[ℂ] H:= Finsupp.linearCombination ℂ (fun n=> jet S Y (n+1) s)
def prism (F:Prism)(s:ℝ):H:= jets S Y s F
variable (F: Prism)
lemma prism_ret : prism S Y F s = ∑ i∈F.support,F i • jet S Y (i+1) s:= rfl
variable (h:Positive S Y)
include h
lemma prism_pos: Positive S (prism S Y F):= by
 intro s t p q; rw [prism_ret, prism_ret, map_sum]; exact Finset.sum_congr rfl fun i _=> by rw [map_smul]; exact congrArg (F i • ·) (jet_positive S (i+1) Y h _ _ p q) -- order i+1
lemma prism_dark (p:0<s): S.orth (prism S Y F s)=0:=by rw [prism_ret,map_sum]; exact Finset.sum_eq_zero fun i _=>by rw [map_smul,jet_dark S i Y h p,smul_zero]
omit h
lemma prism_night (S:OS.Semigroup H timeAxis) (h:Positive S Y)(p:0<s): S.ℚmeasure.region Six.night (prism S Y F s)=0:=by rw [prism_ret,map_sum]; exact Finset.sum_eq_zero fun i _=>by rw [map_smul,jet_night i _ _ h p,smul_zero]
include h
variable {a t : ℝ≥0}
/-- Any pair of strictly forward/zero time shifts at any interior momentum-profile sample
can be matched after taking differences. -/
private lemma all_chords (p:0<s)(v:H)(R:∀ w∈ (jets S Y s).range, inner ℂ v w = 0) :
    EqOn (fun z=> inner ℂ v (lifted S Y z)) (fun _=> inner ℂ v (Y s)) inside:= by
 let c := (s:ℂ)
 let X : H →L[ℂ] ℂ:= innerSL ℂ v
 let y:=X (Y s)
 let T:= X ∘ lifted S Y
 have E (n:ℕ): X (jet S Y (n+1) c) = 0:= R _ ⟨Finsupp.single n 1,by simp [jets,c]⟩
 have g: AnalyticOnNhd ℂ (fun z=>inner ℂ v (lifted S Y z)) inside:= fun z t=> (X.analyticAt _).comp (lifted_analytic S Y h z t)
 obtain ⟨ε,u,hε⟩:= Metric.mem_nhds_iff.mp (open_inside.mem_nhds (show c∈inside from p))
 apply g.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
          (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0|>.isPreconnected) (show c∈inside from p)
 filter_upwards [ball_mem_nhds _ u] with z t
 have e: DifferentiableOn ℂ (lifted S Y) (Metric.ball c ε):= (lifted_analytic S Y h).differentiableOn.mono hε
 have w:= (Complex.hasSum_taylorSeries_on_ball e t).mapL X |>.tsum_eq -- parentheses
 change X (lifted S Y z)= X (Y s); rw [← w, tsum_eq_single (0:ℕ)]
 · simp [c,lifted_heat S Y h p]
 intro n hn; rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨i,h'⟩; subst n; simp only [map_smul]; rw [show X (iteratedDeriv i.succ (lifted S Y) c) =_ from E i]; simp

lemma enter_prism (p:0<s): S.E t (Y s)-S.E a (Y s)∈ closure (Set.range (fun e:Prism=> prism S Y e s)):=by
 let Z:= (jets S Y s).range
 change _ ∈ Z.topologicalClosure; rw [←Submodule.orthogonal_orthogonal_eq_closure]; intro v w
 let b(d:ℝ≥0):= s+ ↑d; have hb(d:ℝ≥0):0<b d:= add_pos_of_pos_of_nonneg p d.property
 have A(t:ℝ≥0): inner ℂ v (S.E t (Y s))=inner ℂ v (Y s):=by
    rw [← Positive.moves S Y h p t, ← lifted_heat S Y h (hb t)]
    exact all_chords S Y h p v ((Z.mem_orthogonal' v).mp w) (show (b t:ℂ) ∈inside from hb t)
 rw [inner_sub_right,A t,A a,sub_self]

variable {L : Type*}{f:Filter L}{d:L→ℝ≥0}
def prism_on (p:Prism)(d:ℝ≥0):H.Op:= ∑ i∈ p.support, p i • (mesh_diff S d)^(i+1)
lemma prism_limit (w:L→ ℝ→ H)(W:Operates (f:=f) S Y w)
    (p:Tendsto d f (𝓝 0))(q:∀ᶠ i in f,0< d i)(hs:0<s):
    Tendsto (fun i:L=> prism_on S F (d i) (w i s)) f (𝓝 (prism S Y F s)):=by
 simp_rw [prism_ret,prism_on,sum_apply,smul_apply]; exact tendsto_finsetSum _ fun i _ => (mesh_limit S (i+1) Y h w W p q hs).const_smul _
omit h
lemma prism_on_dark (d:ℝ≥0) (w:H): S.orth (prism_on S F d w)=0:=by
 rw [prism_on,sum_apply,map_sum]; refine Finset.sum_eq_zero fun i _=> ?_
 rw [smul_apply,map_smul,pow_succ',mul_apply_eq_comp,mesh_dark,smul_zero]
lemma prism_on_night (S:OS.Semigroup H timeAxis)(d:ℝ≥0)(w:H): S.ℚmeasure.region Six.night (prism_on S F d w)=0:=by
 rw [prism_on,sum_apply,map_sum]; refine Finset.sum_eq_zero fun i _=> ?_
 rw [smul_apply,map_smul,pow_succ',mul_apply_eq_comp,mesh_night,smul_zero]
-- density simultaneously (any future openings)
lemma spectrum_seek {α:Type*} (p:0<s) (V: α→ ℝ→ H)(h:∀ i,Positive S (V i)) (t a:α→ℝ≥0) (U:Set (α→ H))(q: U∈𝓝 (fun i=> S.E (t i) (V i s)-S.E (a i) (V i s))):
    ∃ u:α→Prism, (fun i=> prism S (V i) (u i) s)∈U:= by
 let T (i:α):= {y | ∃ u, prism S (V i) u s=y}
 let x(i:α):= S.E (t i) (V i s)-S.E (a i) (V i s)
 have ht:x∈ closure (Set.pi Set.univ T):= mem_closure_pi.mpr fun i _ => enter_prism S _ (h i) p
 obtain ⟨y,hy,g⟩:= mem_closure_iff_nhds.mp ht _ q
 choose u c using fun i:α=> (show y i∈T i from g i (Set.mem_univ i)); exact ⟨u, (funext c).symm ▸ hy⟩
end YM.SatinJets
#print axioms YM.SatinJets.prism_limit
#print axioms YM.SatinJets.prism_dark
#print axioms YM.SatinJets.prism_pos
#print axioms YM.SatinJets.spectrum_seek
#print axioms YM.SatinJets.prism_night
#print axioms YM.SatinJets.prism_on_dark
#print axioms YM.SatinJets.prism_on_night
