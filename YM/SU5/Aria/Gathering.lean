import YM.SU5.Aria.Repertoire
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric Casting
local notation "ξ"=>P.laysM
local notation "Γ"=>P.VMark
local notation "X"=> P.ColorHil j x
local notation "Χ"=> P.ManyF j x
local notation "ω"=>P.colorZero j x
local notation "Ω"=>P.heaven j x
local notation "ν"=>P.seasons j x
local notation "ψ"=>P.physicalEnergy j x
variable (J:P.Ellis j x) {I:Type*}(A:I→P.Apron)(L:List I)(q:I→ Vantage)(p:ℕ→ I→ P.VMark)
local notation "u" p:max=> P.porchY j A p
local notation "v" p:max=> P.resignY j A p
variable (k:ℕ)
namespace Ellis
abbrev onStage (i:I)(n:ℕ): Mist Γ := (J.mistT n).onFn (fun a=> p n i+a)
local notation "Μ"=> J.onStage P j x p -- check order
abbrev regimen [DecidableEq I](n:ℕ): Mist (I→Γ):= Casting.choice (fun i=> J.onStage P j x p i n) (p n) L
end Ellis
-- epsilon controls independent
abbrev FramesAt (p s:I→ Vantage)(e:ℝ) := ∀ i∈ L,dist (p i) (s i) < e
lemma curtains_stay {c d:I→ℝ}(P':∀ i∈L,c i<(u q) i ∧ (v q) i<d i):
   ∃ e>0,∀ p:I→Vantage, FramesAt L p q e → ∀ i∈ L,c i<(u p) i∧(v p) i<d i:=by
 classical
 let r(n:ℕ):ℝ:=(1/2)^n; have hr:Tendsto r atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
 have hh:∀ᶠ n in atTop,∀ i∈ L.toFinset,c i < (u q) i-r n ∧ (v q) i+r n< d i:=by
    refine (L.toFinset.eventually_all).mpr fun i p=>?_; obtain ⟨a,b⟩:=P' i (List.mem_toFinset.mp p)
    filter_upwards [hr.eventually (gt_mem_nhds (sub_pos.mpr a)),hr.eventually (gt_mem_nhds (sub_pos.mpr b))] with n t y; constructor <;> linarith
 obtain ⟨n,h⟩:= hh.exists; have hp:0< r n:=by positivity
 refine ⟨_,hp,fun p P' i t=> ?_⟩
 have he: |p i j - q i j| < r n:= (vclose_ball _ _ _ hp).2 (P' i t) j; obtain ⟨a,b⟩:= h i (List.mem_toFinset.mpr t); obtain ⟨g,k⟩:=abs_lt.mp he
 unfold porchY resignY Apron.time_panel Apron.time_edge at *; constructor <;> linarith
lemma shelter_frame (s:P.Turnstile j A L q) : ∃ e>0, ∀ p:I→Vantage, FramesAt L p q e → P.Turnstile j A L p:=by
 classical
 -- use pairwise compact direct
 induction L with
 | nil=> exact ⟨1,zero_lt_one,fun _ _=>List.Pairwise.nil⟩
 | cons i L ih=>
    obtain ⟨a,b⟩:= List.pairwise_cons.mp s; obtain ⟨e,h,y⟩:= ih b
    let u'(n:ℕ):ℝ:= (1/2)^n; have ht:Tendsto u' atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨n,T,v'⟩: ∃ n, u' n<e∧∀ v'∈L.toFinset, u' n< ((u q) v'-(v q) i)/2:= (((ht.eventually (gt_mem_nhds h))).and (L.toFinset.eventually_all.mpr fun t h=> ht.eventually (gt_mem_nhds (half_pos (sub_pos.mpr (a t (List.mem_toFinset.mp h))))))).exists -- tune
    have hv:0<u' n:=by positivity
    refine ⟨_,hv,fun p x'=> List.pairwise_cons.mpr ⟨?_, y p (fun j u₀ => (x' j (List.Mem.tail i u₀)).trans T)⟩⟩
    intro k t; specialize v' k (List.mem_toFinset.mpr t)
    have ht:|(p i j)-(q i j)|<u' n := (vclose_ball _ _ _ hv).2 (x' i (List.Mem.head ..)) j
    have h':|(p k j)-(q k j)|<u' n:= (vclose_ball _ _ _ hv).2 (x' k (List.Mem.tail _ t)) j
    obtain ⟨ht,v₂⟩:=abs_lt.mp ht; obtain ⟨he,v₁⟩:= abs_lt.mp h'; unfold porchY resignY Apron.time_edge Apron.time_panel at *; linarith
local notation "Σg" p:max=>P.preview j x A L p
local notation "Σ'" p:max=>P.memorial j x A L p
local notation "ξ'" c:max d:max r:max=>fun i:I=>P.pillar j x (A i) (c i) (d i) (r i)
lemma pill_memorial (p:I→Vantage)(c d:I→ℝ)(h:∀ i∈ L,c i<(u p) i∧(v p) i<d i)(g:∀ a b t L', L=t++a::b::L'→ d a=c b): Σ' p=inner ℂ Ω ((L.map (ξ' c d p)).prod Ω):=(curtain_payment _ _ (P.commuteTight j x A p) (u p) (v p) c d (P.heaven_hot j x) _ h g).symm
lemma pill_preview (p:I→Γ)(c d:I→ℝ)(h:∀ i∈ L,c i<(u (ξ ∘ p)) i∧(v (ξ ∘ p)) i<d i)(g:∀ a b t L',L=t++a::b::L' → d a=c b): Σg p=inner ℂ ω ((L.map (fun i=> P.raze j x (A i) (c i) (d i) (p i))).prod ω):=(curtain_payment (ψ) ω (P.commuteLoose j x A p) _ _ c d (P.sector_hot j x) _ h g).symm
lemma turn_no_clones (s:P.Turnstile j A L q): L.Nodup:= by
 refine s.imp (R:=_) (fun {a b} h t=> ?_); -- t Eq
    subst b; have he:= (A a).real_width_pos P j; unfold porchY resignY Apron.time_panel Apron.time_edge at h; linarith
lemma vantage_approach (x:Vantage):∃ y:ℕ→P.VMark,Tendsto (P.laysM ∘ y) atTop (𝓝 x):=by
 choose p h using fun n:ℕ=> Metric.denseRange_iff.mp (P.marksDense) x ((1/2:ℝ)^n) (by positivity)
 refine ⟨p,Metric.tendsto_nhds.mpr fun ε k=>?_⟩
 filter_upwards [(tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num :(1/2:ℝ)<1)).eventually (gt_mem_nhds k)] with i hi
 rw [dist_comm]; exact lt_trans (h i) hi -- sign
namespace Ellis
variable [DecidableEq I]
local notation "𝔇"=> J.regimen P j x L p
local notation "L₀"=> J.onStage P j x p
variable (g:∀ i∈ L,Tendsto (fun n=> P.laysM (p n i)) atTop (𝓝 (q i)))
include g
lemma recoversPose (e:ℝ)(t:0<e): ∀ᶠ n in atTop,(𝔇 n).holds (fun b=>FramesAt L (P.laysM ∘ b) q e):=by
 refine Casting.costs_all (D:=fun n i=>(L₀) i n) _ L (fun n i b=>dist (P.laysM b) (q i)<e) ?_
 intro i u'
 exact P.gentle_room (P.frugal_moves J.owned (fun n=>p n i) (q i) (g i u')) (Metric.tendsto_nhds.mp tendsto_id e t)
lemma virtueξ (y:Axis)(s:P.Turnstile y A L q): ∀ᶠ i in atTop,(J.regimen P j x L p i).holds (fun r=> P.Turnstile y A L (P.laysM ∘ r)) :=by
 obtain ⟨ε,t,pv⟩:=P.shelter_frame y A _ _ s; exact (J.recoversPose P j x L q p g _ t).mono fun i u' => Mist.promotes _ (fun j h=> pv _ h) u'
variable (y:Axis)(s:P.Turnstile y A L q)
local notation "x'"=> P.advocate j x y
local notation "φ"=> P.ColorHil y x'
local notation "Ψ"=> P.ManyF y x'
local notation "Πϑ"=>P.enter y x'
local notation "ω'"=>P.heaven y x'
local notation "ω₀"=>P.colorZero y x'
local notation "Σπb" r:max=> P.preview y x' A L r
include s
lemma draw_league : Tendsto (fun i=> (J.regimen P j x L p i).mean (P.preview y (P.advocate j x y) A L)) atTop (𝓝 (P.memorial y x' A L q)):=by
 let s' := P.turn_no_clones y A L q s
 let c:= P.porchY y A q; let d:= P.resignY y A q; let M:= 𝔇
 obtain ⟨C⟩:= choose_curtains c d L s' (weaves_sorted _ _ L s)
 let a:= C.first; let b:= C.last; have he:∀ i∈L,a i<c i∧d i<b i:=fun i t=>⟨C.inside i t,C.outside i t⟩
 obtain ⟨ε,t,h⟩:=P.curtains_stay y A L q he -- private fields dot works?
 let Z(i:I):=(A i).engine P y x'; let V(i:I)(r:Vantage):= P.pillar y x' (A i) (a i) (b i) r; let T (i:I)(r:Γ):=P.raze y x' (A i) (a i) (b i) r
 let Φ(i:I)(n:ℕ):= P.remunerate y x' (A i) (a i) (b i) ((L₀) i n); -- notation Φ? none
 have reach : ∀ᶠ n in atTop, (M n).mean (P.preview y x' A L)=inner ℂ ω₀ ((L.map (fun i=> Φ i n)).prod ω₀) := by
   filter_upwards [J.recoversPose P j x L q p g ε t] with n e
   let A':= M n; let F(r:I→Γ):= (L.map (fun i=> T i (r i))).prod ω₀; have hg: ∀ r:I→Γ, FramesAt L (P.laysM∘r) q ε → Σπb r=inner ℂ ω₀ (F r):=fun r hr=>pill_preview P y x' A L r a b (h _ hr) C.joins
   rw [(show (M n).mean (P.preview y x' A L)=(A').mean (fun r=>innerSL ℂ ω₀ (F r)) from Mist.mean_congr _ (P.preview y x' A L) ((A').promotes hg e)), A'.mean_linear' F (innerSL ℂ _),(show A'.mean F=(L.map (fun i=> Φ i n)).prod ω₀ from Casting.mean_run (fun i:I=>(L₀) i n) _ T L s' ω₀)]; rfl
 have hb:Tendsto (fun n=>(L.map (fun i=> Φ i n)).prod ω₀) atTop (𝓝 (Πϑ ((L.map (fun i=> V i (q i))).prod ω'))) :=
    Casting.run_tends (Πϑ) (fun n i=> Φ i n) (fun i=> V i (q i)) (fun i=>‖Z i‖) L ω' (fun i w=> P.firming y x' (A i) (a i) (b i) J.mistT J.owned (J.shaky y) (fun n=>p n i) _ (g i w) ((he i w).1) ((he i w).2)) (fun i _ n=>P.remuneration ..)
 have e: inner ℂ ω₀ (Πϑ ((L.map (fun i=> V i (q i))).prod ω'))= P.memorial y x' A L q:= ((Πϑ).inner_map_map ω' _).trans (pill_memorial P y x' A L q a b he C.joins).symm
 rw [← e]; exact (tendsto_const_nhds.inner hb).congr' (reach.mono (fun i t=>t.symm))
end Ellis
lemma unanimous (y z:Axis)(l:List I) (s:P.Turnstile y A L q)(p:P.Turnstile z A l q) (h:L.Perm l) (J:P.Ellis j x):
    P.memorial y (P.advocate j x y) A L q=P.memorial z (P.advocate j x z) A l q:=by
 choose f y' using fun i:I=> P.vantage_approach (q i)
 letI:DecidableEq I:=Classical.typeDecidableEq I; let v'(n:ℕ)(i:I):= f i n
 have ht:= J.draw_league P j x A L q v' (fun i _=>y' i) y s; have hv:= J.draw_league P j x A l q v' (fun i _=> y' i) z p
 let a:=P.advocate j x y; let b:=P.advocate j x z; refine tendsto_nhds_unique_of_eventuallyEq ht hv ?_
 obtain ⟨ε,e,H⟩:= P.shelter_frame z A l q p; let M:= J.regimen P j x L v'; let M':= J.regimen P j x l v'
 filter_upwards [J.virtueξ P j x A L q v' (fun i _=>y' i) y s, J.recoversPose P j x L q v' (fun i _=> y' i) ε e] with n ε' t
 have hv: (M n).mean (P.preview y a A L)=(M n).mean (P.preview z b A l):= Mist.mean_congr _ (P.preview y a A L) ((M n).promotes (fun b v₀=> P.match_forecast j x A L y z l h b v₀.1 (H _ (fun i u'=> v₀.2 i (h.mem_iff.mpr u')))) ((M n).cradles ε' t))
 exact hv.trans (Casting.mean_order (fun i:I=>J.onStage P j x v' i n) _ L l h (P.turn_no_clones y A L q s) _)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.unanimous
