import GaugeFieldConstruction.«EmitBeforeΛL»
import GaugeFieldConstruction.SummitFromStars
/-!
# Local cyclic tests in this reconstruction.
Heated visits along strictly positive variable-height strokes. Exact B.Face canon.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Mink Set Filter MeasureTheory Analysis Distribution LD Bid Work.C22 Work.C23 Work.C24 OS Small
open scoped BigOperators Topology ContDiff InnerProductSpace NNReal
variable {n m:ℕ}{G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}
variable (B:Small S C){p q:ℝ≥0}{F:Waves S}{K:Spins S}{W:Surface S}
lemma PadsRP (y:Heights n)(h:y∈ positiveHeight n):∃ p:ℝ≥0,Small.ample p y:=by
 have hc:Continuous (fun p:ℝ≥0=>4*(p:ℝ)):=by fun_prop
 have hp:Tendsto (fun p:ℝ≥0=>4*(p:ℝ)) (𝓝[>] 0) (𝓝 0):=by simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi _))
 have he:∀ᶠ p:ℝ≥0 in 𝓝[>] 0, ∀ i j:Fin n,i<j→4*(p:ℝ)< y j-y i:=by
    apply eventually_all.mpr; intro i; apply eventually_all.mpr; intro j; by_cases v:i<j
    · filter_upwards [hp.eventually (gt_mem_nhds (sub_pos.mpr (h.1 v)))] with p e v using e
    exact Eventually.of_forall fun p q=>(v q).elim
 have hh:∀ᶠ p:ℝ≥0 in 𝓝[>] 0, ∀ i:Fin n,4*(p:ℝ)<y i:= eventually_all.mpr fun i=> hp.eventually (gt_mem_nhds (h.2 i))
 apply Filter.Eventually.exists (f:=𝓝[>] (0:ℝ≥0)); filter_upwards [he,hh,self_mem_nhdsWithin, (gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with p v w z x using ⟨⟨z,x,v⟩,w⟩
lemma HeightPlusRP {y:Heights n}{a:ℝ}(h:y∈ positiveHeight n)(p:0<a): a • y ∈ positiveHeight n:=⟨fun _ _ t=>mul_lt_mul_of_pos_left (h.1 t) p,fun i=> mul_pos p (h.2 i)⟩
lemma HeightLateRP {p:ℝ≥0}{y:Heights n}(h:Small.ample p y):∀ᶠ y' in 𝓝 y, Small.ample p y' :=by
 have he:∀ᶠ v:Heights n in 𝓝 y,∀ i j:Fin n,i<j→4*(p:ℝ)< v j-v i:=by
    apply eventually_all.mpr; intro i; apply eventually_all.mpr; intro j; by_cases v:i<j
    · filter_upwards [((continuous_apply j).sub (continuous_apply i)).tendsto y |>.eventually (lt_mem_nhds (h.1.2.2 i j v))] with p e v using e
    exact Eventually.of_forall fun p q=>(v q).elim
 have hh:∀ᶠ v:Heights n in 𝓝 y,∀ i:Fin n,4*(p:ℝ)<v i:= eventually_all.mpr fun i=>(continuous_apply i).tendsto y |>.eventually (lt_mem_nhds (h.2 i))
 filter_upwards [he,hh] with x e w using ⟨⟨h.1.1,h.1.2.1,e⟩,w⟩
variable (v:Fin n→Letter S)(w:Fin m→Letter S)
abbrev capRP (p:ℝ≥0)(z:Heights n):= ∫ x:Points n,(Joint.materialize n (Prod.snd∘v) x) • B.shot p n (Prod.fst ∘ v) z x
lemma CupAsRP(t:ℝ):B.heatCup (List.ofFn v) t=capRP B v (Small.logD t) (Small.profile t _):=by
 rw [heatCup_n B _ t n (List.length_ofFn ..)]
 simp only [List.get_ofFn, Fin.cast_cast, Fin.cast_eq_self]; rfl
variable {J:StarOp S}(U:LoreL F K W T){D:∀ i,Blanket i}{X:W.Aurora D}(H:X.FullBody F)(b: Hull B F J)
local notation "σ_T" => (bothT (Prod.fst ∘ v) (Prod.fst ∘ w) J)
local notation "σ_Q" => (bothTest v w J)
include U H b
lemma posKernelRP {a:Heights n}{c:Heights m}(u:Small.ample p a)(e:Small.ample q c) :
    inner ℂ (capRP B v p a) (capRP B w q c)=(D _).partialD (W.W _ σ_T) (dawn (bothH a c)) σ_Q :=by
 let δ(x:Points (n+m)):= F.restricted σ_T (bothH a c) x * σ_Q x
 let l := merger (n:=n) (m:=m)
 have ha:a∈ positiveHeight _:=roomPositive (ample_room u); have hc:c∈ positiveHeight _:= roomPositive (ample_room e)
 have hr:=ordered ha hc
 have hi: Integrable (δ ∘ l) := (preserves.integrable_comp_emb l.toHomeomorph.measurableEmbedding).2 (U.joints.int _ _ _ hr _)
 calc
    _ = ∫ x: Points n, ∫ y:Points m, (δ ∘ l) (x,y) := by
       rw [capRP,← inner_conj_symm,← integral_inner (shot_int _ _ _ _ _ u),← integral_conj]; refine integral_congr_ae <| ae_of_all _ fun x=>?_
       dsimp only; rw [inner_conj_symm,capRP,← integral_inner (shot_int _ _ _ _ _ e)]; refine integral_congr_ae <| ae_of_all _ fun y=>?_
       change inner ℂ (_ • B.shot _ _ _ _ x) (_ • B.shot _ _ _ _ y)=δ (bothP x y)
       rw [inner_smul_left,inner_smul_right,b.join _ _ _ _ _ _ _ _ ha hc u e]
       unfold δ; rw [bothTest_at, Function.comp_def Prod.snd, Function.comp_def Prod.snd]; ring
    _ = ∫ z, (δ ∘ l) z ∂(volume.prod volume) := (integral_prod _ hi).symm
    _ = ∫ x, δ x := preserves.integral_comp l.toHomeomorph.measurableEmbedding δ
    _ = _ := by rw [H.builds _ _ _ (etched hr)]; apply integral_congr_ae; filter_upwards with p; rw [H.pure _ _ _ _ hr]
lemma eqCapRP {y:Heights n}(u:Small.ample p y)(e:Small.ample q y):capRP B v p y= capRP B v q y:=by
 apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp; rw [inner_sub_left,inner_sub_right,inner_sub_right,posKernelRP B v v U H b u u,posKernelRP B v v U H b u e,posKernelRP B v v U H b e u,posKernelRP B v v U H b e e]; ring
#print axioms eqCapRP
end YM.NSF.Boundary
end
