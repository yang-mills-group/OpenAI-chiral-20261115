import YM.CF.Atala.Repa
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Atala
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open CF.Forge
variable {M: Monk G S}
lemma tipS(i:Bond f)(p:i∈M.park.trunks): M.sent x T q d l β i=1:= M.park.on_tree _ ⟨i,p⟩
lemma replicaTr (F:Forest S.ratio){i:Bond f}(p:i∈F.trunks)(V:Config G c) : replica S.ratio V i=1:= if_pos (sits (F:=F) p)
lemma highs (hp:1 ≤ radiusB x){u:ℝ}(ht:0≤u)(p:‖M.rich x T q d l β‖≤u) (b:Bond f)(h:S.ratio.parent b.1 ∉ M.key.dome (11*radiusB x)):∃ z:G.Color,‖z‖ ≤ u ∧ M.sent x T q d l β b=G.lieExp z*replica S.ratio M.V b:=by
 by_cases k:b∈ M.park.trunks
 · exact ⟨0,(norm_zero.le.trans ht),by rw [tipS b k,replicaTr M.park k]; simp⟩
 let a:M.park.Free:=⟨b,k⟩; have hv:¬chill M.key x M.park a:=by
    rintro (j|j); · exact h (dome_u j (by change _+separation (S.ratio.parent b.1) (S.ratio.parent b.1)≤ _; simp; first|done|omega))
    apply h (dome_u j ?_); have ht:=Work.E03.parent_step S b.1 b.2; rw [separation_comm] at ht; change _+separation (S.ratio.parent (b.1+step b.2)) _ ≤ _; omega
 let i:Active M.key x M.park:=⟨a,hv⟩; exact ⟨M.rich x T q d l β i,(norm_le_pi_norm ..).trans p,clear_physical x M.key M.park _ _ (M.fuel x T q d l β) i ⟩
lemma glories (hs:40<c.val) {t a D u:ℝ}(hv:0<a)(ht:0<t)(hD:0<D)(hu:0<u)(hrk:4*(D+rate_x*t)≤a) (hp:100 ≤ radiusB x)(h:‖M.rich x T q d l β‖≤u) (hq:flags t M.V ⊆ M.key.place)(hb:∀ z:G.Color,‖z‖≤u → G.chord (G.lieExp z)≤ D):∀ i∈flags a (M.sent x T q d l β), S.ratio.parent i ∈ M.key.dome (12*radiusB x):=by
 intro i p; obtain ⟨j,w,v⟩:= (flags_spec ..).mp p; by_contra k; exact v.not_ge ((saneP S hs hq hD.le ht.le (M.sent x T q d l β) (11*radiusB x) (highs (by omega) hu.le h) hb j (fun v=>k (dome_u v (by have ht:=Work.E04.parent_separation S.ratio j.1 i; have hh:=Work.E01.sep_touched j i w; omega)))).trans hrk)
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset
lemma grace_c {a:ℝ}(h:0<a)(P:Patch):∀ᶠ x:ℝ in atTop,temp x ≤ a:=by
 filter_upwards [expM P (hp:=half_pos h),monitors SU.group P.L] with x ht hx; exact hx.2.2.trans (by linarith only [ht])
lemma vows {G: Gauge}{a:ℝ}(t:0<a):∃ u:ℝ,0<u ∧ ∀ i:G.Color,‖i‖≤u→G.chord (G.lieExp i) ≤ a:=by
 have he:= G.continuous_chord.comp G.lieExp_cont; have hx:=he.continuousAt (x:=0); obtain ⟨u,b,h⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp (hx.eventually (gt_mem_nhds (show (G.chord ∘ G.lieExp) 0<a from by simp [t]))); refine ⟨u,b,fun i p=> (h (by simpa [mem_closedBall] using p)).le⟩
local notation "G"=>SU.group
structure Bell (S:StepData c f)(M:Monk G S)(x:ℝ)(T:Tube G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(a b:ℝ):Prop where
 years : 100≤ radiusB x
 tax: temp x ≤ a
 height: flags (temp x) M.V⊆ M.key.flags
 reach(i):i∈flags a (M.sent x T q d l β) → S.ratio.parent i ∈ M.key.dome (12*radiusB x)
 low : ‖M.rich x T q d l β‖≤b
lemma threshold (P:Patch)(n l:ℕ)(a b C B:ℝ)(hp:0<a)(hz:0<b)(hv:0<C)(hB:0<B):∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S)(M:Monk G S), S.patch=P→ flags (temp x) M.V ⊆ M.key.flags → 40<c.val → ∀ β∈ Set.Icc (y G P.L x/2) (2*y G P.L x), ‖M.z‖ ≤ B*Scales.p G P.L x →∀ d:ℝ,∀ q:Chi, MossX n l x M.key M.park T M.V M.k C d (fiery G x P.L) q→ Bell S M x T q d l β a b:=by
 let D:=a/8; have hD:0<D:=by unfold D; positivity
 obtain ⟨u,t,g⟩:=@vows SU.group _ hD; let δ:= min u b; let K:= C+2*(2^n*C*B); have hK:0<K:=by unfold K; positivity
 let E:=Push.Uniform.shade G; have he:0<E:=Push.Uniform.shade_pos _; have hh:0<δ:= lt_min t hz
 let W:=max 1 rate_x; have hw:0<W:=zero_lt_one.trans_le (le_max_left ..); let v :=a/(8*W); have hq:0<v:=by unfold v; positivity
 filter_upwards [expM P (hp:=div_pos hh (mul_pos he hK)),Work.E01.radiusB_tendsto.eventually_ge_atTop 100,monitors G P.L, (year G P.L).eventually (eventually_gt_atTop 0),grace_c hp P,grace_c hq P ] with x ht hp hQ hr hg hb c f S T M hx hk hg' β hβ hx' d q k
 let t':= fiery G x P.L; let Y:=B*Scales.p G P.L x; have h1:=hQ.1; have h3:0<Y:=mul_pos hB (Scales.pos ..); have h2:0<β:= (half_pos hr).trans_le hβ.1
 have hp':flags (temp x) M.V ⊆ M.key.place:= fun i h=> mem_union_right _ (hk h); have hX:‖M.rich x T q d l β‖ ≤ δ:=by
    have hy':‖M.bell x‖ ≤ Y:=(pi_norm_le_iff_of_nonneg h3.le).mpr fun i=> (norm_le_pi_norm M.z i.val.val).trans hx'; have W:Jet.Allows n (fun v:Directions SU.group c=>realP β T M.park M.key (Vmove x M.V v) M.k x l q d (M.bush x) (M.bell x)) 0 (C*t'+ |coupling β| * (2^n*C*Y)):=(ready_heat (β:=β) (M.bush x) (M.bell x) t' k Y hy' hv.le).2 -- tune p
    have ht0:E*(C*t'+ |coupling β| *(2^n*C*Y)) ≤ δ:=by
       apply le_trans (b:=E*(K*t')) ?_
       · rw [←mul_assoc,mul_comm (E*K)]; exact (le_div_iff₀ (mul_pos he hK)).mp ht
       apply mul_le_mul_of_nonneg_left _ he.le; rw [abs_of_pos (coupling_pos h2)]
       apply (add_le_add_right (mul_le_mul_of_nonneg_right (compare_v G P.L x hβ hr).1 (show 0≤ 2^n*C*Y from by positivity)) _).trans; unfold t' K Y; rw [Scales.fi]; exact le_of_eq (by ring)
    refine (pi_norm_le_iff_of_nonneg hh.le).mpr fun i=>?_ ; have hv' := (shelJ W i).value; rw [show Vmove x M.V 0=M.V from by simp [Vmove]] at hv'; exact hv'.trans ht0
 refine ⟨hp,hg,hk,glories hg' (lt_of_lt_of_le ?_ hg) h1 hD hh ?_ hp hX hp' (fun z k=>g _ (k.trans (min_le_left ..))),hX.trans (min_le_right ..)⟩ -- tune weird
 · exact h1
 have hL:rate_x*temp x ≤ D:=by refine (mul_le_mul_of_nonneg_right (show rate_x≤W from le_max_right ..) h1.le).trans ((mul_le_mul_of_nonneg_left hb hw.le).trans_eq ?_); unfold v D; field_simp
 unfold D at *; linarith only [hL]
end YM.CF.Atala
