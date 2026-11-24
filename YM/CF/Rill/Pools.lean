import YM.CF.Rill.Salt
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
noncomputable def twin (x:Chin N)(S:Seal (Site (More N)))(y:Chin N): Chin N:=fun i=>if i∈leaks S then x i else y i
lemma tipper(A:Chin N)(S:Seal (Site (More N)))(B:Chin N): fare S (twin A S B) A=0:=by unfold fare; apply sum_eq_zero; intro i h; unfold twin; rw [if_pos h,sub_self,norm_zero]
lemma fiord (k:Ratio c f)(u v:Co (N:=c) (P:=f))(S:Support (More f)) : let X:Co (N:=c) (P:=f):=((twin u.1.1 S v.1.1,twin u.1.2 (cloudG k S) v.1.2), twin u.2 S v.2); deal k S X.1 u.1=0 ∧ fare S X.2 u.2=0:=by
 intro X; unfold X deal; dsimp only; simp [tipper]
lemma twina(A:Chin N)(S:Seal (Site (More N))): twin A S A=A:=funext fun i=>by unfold twin; split <;>rfl
lemma blaze_f(n:ℕ)(p:0<e):∃ b:ℝ,0<b∧∀{N P:Side}(X:Ratio N P)(F:cro X e→ Op (Iota X)){S:Support (More P)}(t k:Bool)(W:Toll (Iota X)), Suite (badge _) (pinH X e t) (pinH X e k) S W F → ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](u:E→ cro X e)(x:E)(V:E→ Nom N P)(T:E→ Pane P), (∀ i,(u i).val=(unionP (V i),Tulip.profile (T i))) → JointB X (V x) e → Guard (T x) e → (∀ i:Bond (More P),Skye.ends i⊆ S → Tender (fun y=> (V y).1 i) x b n ∧ Tender (fun y=>T y i) x b n) → (∀ i:Bond (More N), Skye.ends i⊆ cloudG X S → Tender (fun y=> (V y).2 i) x b n) →∀ i j, Allows n (fun p=> F (u p) i j) x (W i j):=by
 let D:ℝ:=(1+ (2:ℝ)^n/e)^n; let t:=max 1 (Shake.quota n*D); have ht:0<t:=zero_lt_one.trans_le (le_max_left ..); obtain ⟨a,C,u,h,H⟩:= brand_ask n; have hv:0<C:=zero_lt_one.trans_le h; let b:= min a (1/(C*t)); have hb:0<b:=lt_min u (by positivity)
 refine ⟨b,hb,fun {N P} G' F {S} t' k W q E _ _ U x V T l hv' hw hg hx i j=>?_⟩
 let R(y:E):=(U y).val; let Φ(y:E):Co (N:=N) (P:=P):=((twin (Tulip.profile (V y).1) S (R x).1.1,twin (Tulip.profile (V y).2) (cloudG G' S) (R x).1.2), twin (Tulip.profile (T y)) S (R x).2); let A:= R x
 have he:Φ x= R x:=by unfold Φ R; simp_rw [l]; simp [twina,unionP] -- tune
 have hk: ball (Φ x) e⊆ cro G' e:=by
    intro y u; rw [he] at u; rw [mem_ball_iff_norm] at u; change ‖y-(U x).val‖< _ at u; rw [l x] at u
    refine ⟨⟨V x,hv',lt_of_le_of_lt (norm_fst_le (y-(unionP (V x),Tulip.profile (T x)))) u⟩,⟨T x,hw,lt_of_le_of_lt (norm_snd_le (y-(unionP (V x),Tulip.profile (T x)))) u⟩⟩ -- tune
 have hQ {M:Side}(A:Chin M)(S:Support (More M))(V:E→ Pane M)(g:∀ i:Bond (More M),Skye.ends i ⊆ S→Tender (fun y=>V y i) x b n):Shake (fun y=>twin (Tulip.profile (V y)) S A) x (C*b) n:=by
    refine Shake.various _ (by positivity) fun i=>Shake.various _ (by positivity) fun v=>?_; let F(x:E):=V x i; unfold twin; split
    next hx => exact H x (min_le_left ..) F (g i (insert_subset (mem_filter.mp hx).2.1 (singleton_subset_iff.mpr (mem_filter.mp hx).2.2))) v
    next hx => exact (Shake.holds _).bag (by positivity)
 have ha: Shake Φ x (C*b) n:= ((hQ _ _ (fun y=>(V y).1) (fun i v=>(hg i v).1)).team (hQ _ _ (fun y=>(V y).2) hx)).team (hQ _ _ T (fun i v=>(hg i v).2))
 let L:= fun x=> F x i j; let P' := W i j; have ht0 : t*(C*b) ≤ 1:=by unfold b; rw [←mul_assoc,mul_comm t C, mul_comm]; exact (le_div_iff₀ (mul_pos hv ht)).mp (min_le_right ..)
 have hS : Shake (Jet.equalizer L ∘ Φ) x P' n:= ((ha.thorn (Shake.pick (allows_looks (q.fuel i j) (q.expo i j).connected hk p n (q.expo i j).bounded)) ((le_mul_of_one_le_left ha.price (le_max_left ..)).trans ht0))).bag (by
    have hC:0≤P':=(q.expo i j).positive
    calc
    _ = P'* (Shake.quota n* D * (C*b)):=by unfold P' D; ring
    _ ≤ P' :=mul_le_of_le_one_right hC ((mul_le_mul_of_nonneg_right (le_max_right ..) ha.price).trans ht0))
 suffices P: Shake (fun y=> F (U y) i j) x P' n by exact (P.paid ((q.expo i j).bounded _)).mono (max_le le_rfl le_rfl)
 apply hS.same; filter_upwards [ha.smooth.continuousAt.eventually ((cabin G' e).prod (openc _ e)|>.mem_nhds (hk (mem_ball_self p)))] with u z -- maybe crop neq union
 unfold Jet.equalizer Function.comp; dsimp only; change Φ u∈ cro G' e at z; rw [dif_pos z]; let Y:cro G' e:=⟨_,z⟩; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; have hu:= (q.expo i j).variation Y (U u); rw [show (hall G' e).eval S Y (U u)=0 from ?_,mul_zero] at hu; exact hu
 change deal _ S (Φ u).1 _/ _+ fare S (Φ u).2 _/_=_; rw [l u]; unfold Φ; dsimp only [deal,unionP]; simp [tipper] -- tune
end YM.CF.Rill
