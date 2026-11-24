import YM.CF.Rill.Pools
import YM.CF.Sour.Pose
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Cube Lat Tulip Peaks Fock Jet Branch Urn Levier Drapes Tenant
attribute [local instance] opCStarAlgebra
variable {N:Side}
set_option synthInstance.maxSize 20000
-- exterior grasp money.Learn Marker.True
abbrev actB (e:ℝ)(n:ℕ)(b:ℝ):Prop:=∀{N:Side}(F:↥(Openc (More N) e)→ Op (Single N)){S:Support (More N)}(W:Toll (Single N)), Suite (badge _) (bail N e) (bail N e) S W F → ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ ↥(Openc (More N) e))(x:E)(T:E→ Pane N), (∀ i,(U i).val=Tulip.profile (T i)) → Guard (T x) e →(∀ i:Bond (More N),Skye.ends i ⊆ S→ Tender (fun y=> T y i) x b n)→∀ i j,Allows n (fun v=> F (U v) i j) x (W i j)
lemma opus_b(n:ℕ)(p:0<e):∃ b:ℝ,0<b∧actB e n b:=by
 let D:ℝ:=(1+(2:ℝ)^n/e)^n; let t:=max 1 (Shake.quota n*D); have ht:0<t:=zero_lt_one.trans_le (le_max_left ..); obtain ⟨a,C,u,h,H⟩:= brand_ask n; have hv:0<C:=zero_lt_one.trans_le h; let b:=min a (1/(C*t)); have hb:0<b:=lt_min u (by positivity)
 refine ⟨b,hb,fun {N} F {S} W q E _ _ U x T l hw hh i j=>?_⟩
 let R(y:E):=(U y).val; let Φ(y:E):Chin N:= twin (Tulip.profile (T y)) S (R x); let A:= R x
 have he:Φ x=R x:=by unfold Φ R; simp_rw [l]; exact twina ..
 have hk: ball (Φ x) e⊆ Openc (More N) e:=by intro y u; refine ⟨T x,hw,?_⟩; change _ ∈ Metric.ball _ _ at u; rw [he,mem_ball_iff_norm] at u; rw [←l]; exact u
 have ha: Shake Φ x (C*b) n:=by
    refine Shake.various _ (by positivity) fun i=> Shake.various _ (by positivity) fun v=>?_ ; unfold Φ twin; split
    next hx => exact H x (min_le_left ..) _ (hh i (insert_subset (mem_filter.mp hx).2.1 (singleton_subset_iff.mpr (mem_filter.mp hx).2.2))) v
    next hx => exact (Shake.holds _).bag (by positivity)
 let L:= fun x=> F x i j; let P':= W i j; have ht0:t*(C*b)≤1:=by unfold b; rw [←mul_assoc,mul_comm t C,mul_comm]; exact (le_div_iff₀ (mul_pos hv ht)).mp (min_le_right ..)
 have hS:Shake (Jet.equalizer L ∘ Φ) x P' n:= ((ha.thorn (Shake.pick (allows_looks (q.fuel i j) (q.expo i j).connected hk p n (q.expo i j).bounded)) ((le_mul_of_one_le_left ha.price (le_max_left ..)).trans ht0))).bag (by
    have hC:0≤P':=(q.expo i j).positive
    calc
    _ = P'* (Shake.quota n*D*(C*b)):=by unfold P' D; ring
    _ ≤ P':= mul_le_of_le_one_right hC ((mul_le_mul_of_nonneg_right (le_max_right ..) ha.price).trans ht0))
 suffices Y:Shake (fun y=>F (U y) i j) x P' n by exact (Y.paid ((q.expo i j).bounded _)).mono (max_le le_rfl le_rfl)
 apply hS.same; filter_upwards [ha.smooth.continuousAt.eventually ((openc _ _).mem_nhds (hk (mem_ball_self p)))] with y z; change Φ y∈ Openc (More N) e at z; unfold Jet.equalizer Function.comp; change (if h:Φ y∈_ then L ⟨Φ y,h⟩ else 0)=_; rw [dif_pos z]; let Y: Openc (More N) e:=⟨_,z⟩; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; have hz: (forum N e).eval S Y (U y)=0:=by change fare S (twin _ _ _) (U y).val/ _ =0; rw [l y,tipper,zero_div] -- tune
 have hu:= (q.expo i j).variation Y (U y); rw [hz,mul_zero] at hu; exact hu
end YM.CF.Rill
