import Anomaly.Ward.Choose
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill Sour
open Nacre Next.Free Exterior Precision Wilson _root_.Zephyr.Chern SpectrumQ
open Ione.Clock Hove Spire Regis.Head Next.Rank.Spindle LampP
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace StageQ
local notation "Γ"=> More n
local notation "U" => fieldDir SU.group (More n) 1
local notation "Πp"=> tangD n
open PotQ
variable {s:Sweep n}
lemma screenχ (b:ℕ)(o:Seat n)(t:boxA s o=o) : (halo b {o}).map (boxA s).toEmbedding=halo b {o}:=by rw [←paysT,map_singleton,Equiv.toEmbedding_apply,t] -- embeddings
lemma screenQ (v:Πp): increment 1 (Ione.door_b s 1 v)=flashA s (increment 1 v):=by
 rw [Ione.tour_p]; have ht:flashA s 1=1:=by funext i; rw [Skye.flash]; simp
 rw [ht]
lemma separatePath (x y:Πp) (h: (fun a:ℝ=> RG.increment 1 (a • x)) = (fun a:ℝ=> RG.increment 1 (a • y))): x=y := by
 funext i
 have hv(t:ℝ): SU.group.lieExp (t • x i)=SU.group.lieExp (t • y i):=by have p:=congrFun (congrFun h t) i; simpa [increment] using p
 let M:= SU.group.plog ∘ SU.group.mat
 have he(x:SU.group.Color) : ∀ᶠ a :ℝ in 𝓝 0, M (SU.group.lieExp (a • x))=a • x:= (show Tendsto (fun t:ℝ=>t • x) (𝓝 0) (𝓝 0) from by simpa using! (show Continuous (fun t:ℝ=>t • x) from by fun_prop).tendsto 0).eventually SU.group.plog_left
 obtain ⟨a,ht,h0,hx⟩:= ((he (x i)|>.filter_mono (nhdsWithin_le_nhds (s:={(0:ℝ)}ᶜ))).and ((he (y i)|>.filter_mono (nhdsWithin_le_nhds (s:={(0:ℝ)}ᶜ))).and self_mem_nhdsWithin)).exists
 rw [hv,h0] at ht; exact smul_right_injective _ (show a≠0 from hx) ht.symm -- signature
lemma seaChange (q:Sweep n)(X:U): Ione.door_b q 1 (collect SU.group X)=collect SU.group (sailH q X):=by
 apply separatePath; funext v; rw [←map_smul,screenQ,← survey,← survey]; exact (colorTravel q X v).symm
lemma screenA (s:Sweep n)(v:Πp): ‖Ione.door_b s 1 v‖ ≤ ‖v‖:=(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=>(Ione.cod_E ..).trans_le (norm_le_pi_norm v _)
lemma blank_yaw_sum {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] (x:X) : (∑ i:Signed,dollar i • x)=0:=by
 let F:= Equiv.mulRight (Signed.mirror 0); let Z:= ∑ i:Signed,dollar i • x; have h(i:Signed):dollar (F i)= -dollar i:=by unfold F; change dollar (i * (Signed.mirror 0))=_; rw [dollar_mul,show dollar (Signed.mirror 0)= -1 from if_pos (det_t _),mul_neg,mul_one]
 have ht: Z=-Z:= (Equiv.sum_comp F _).symm.trans (by simp_rw [h,neg_smul,sum_neg_distrib]; rfl); -- no scalar-torsion
 refine (smul_right_injective X (two_ne_zero' ℝ)) ?_ -- syntax
 calc
 _ = Z+Z:= two_smul _ _
 _ = (0:ℝ) • Z:=by nth_rw 1 [ht]; rw [neg_add_cancel,zero_smul]
 _ = _:=by simp [zero_smul,smul_zero]

variable {b k m:ℕ}{d c α C M w:ℝ}{P:BudgetPoint}{K:Loom n}{X:SOp n}{T:tableQ SU.group (More n) ℂ} {x:Site n} (R:Knit X (node x) b d α M C w m T) (L:mintQ α C d m) (H:Roof n c d k K)(hb:b+k+10 ≤ P.B)(hp:P.threshold ≤ c)
local notation "Z"=> traceMeter P K x X
local notation "Σx"=> Lattice.halo b {node x}
local notation "ΣP"=> Lattice.halo P.B {node x}
-- as in manuscript, SUM instead of average, const group size: adjust final budget by that constant
abbrev onStage (x:Site n)(f:Pane n→ℂ)(y:Pane n):=∑ j:Signed,dollar j • f (flashA (gridTulip j x) y)
lemma projectionK (s:Signed)(x:Site n)(f:Pane n→ℂ)(y:Pane n) : onStage x f (flashA (gridTulip s x) y)= dollar s • onStage x f y:=by
 let p(i:Signed):= dollar i • f (flashA (gridTulip i x) y)
 change _= dollar s • (∑ i,p i); let U':= Equiv.mulLeft s; rw [← Equiv.sum_comp U' p,Finset.smul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [lights,←tieMul]; unfold p; change _= dollar s • dollar (s*i) • _; rw [smul_smul,dollar_mul,←mul_assoc,show dollar s*dollar s=1 from (by unfold dollar; split<;>norm_num),one_mul]; rfl
include R L H hb hp
lemma screenCash (W:tableQ SU.group (More n) ℂ)(h:∀ v:U,tariff W (receipt v)=∑ i:Signed, dollar i • tariff T (receipt (sailH (gridTulip i x) v)))(Q₀:Pane n)(f:pingS P.threshold (Lattice.halo P.B {node x}) Q₀)(V':U)(p: Agrees (Lattice.halo b {node x}) Q₀ (represent V'))(v:‖collect SU.group V'‖<α)(y:3 ≤ m) : ‖onStage x (traceMeter P K x X) Q₀ - tariff W (receipt V')‖ ≤ Fintype.card Signed*(2*C*M) *‖collect SU.group V'‖^3:=by -- includes
 unfold onStage; rw [h, show ∑ i:Signed,dollar i • Z (flashA (gridTulip i x) Q₀)= (∑ i:Signed,dollar i • Z (flashA (gridTulip i x) Q₀))-(∑ i:Signed,dollar i • (rawQ X 1)) from (by rw [blank_yaw_sum]; simp),← sum_sub_distrib,← sum_sub_distrib]; apply (norm_sum_le ..).trans ?_
 let Q:=Fintype.card Signed;  -- remove shadow
 rw [mul_assoc,show (Q:ℝ)*_=∑ i:Signed, (2*C*M)*‖collect SU.group V'‖^3 from by simp [Q]]; apply sum_le_sum; intro i _
 rw [← smul_sub,← smul_sub,norm_smul,Real.norm_eq_abs,dollar_fixed,one_mul]; let g:=gridTulip i x; have he:boxA g (node x)=node x:=by rw [←nodeA,tieA]
 refine evaluation R L H hb hp (flashA g Q₀) ?_ (sailH g V') (?_) ?_ v y
 · have ht: boxA g⁻¹ (node x)=node x:= by rw [sitU]; exact (Equiv.symm_apply_eq _).mpr he.symm -- tune
   rw [←show Salt.actY g ΣP=ΣP from ?_]; exact (Salt.glowA ..).2 f
   unfold Salt.actY; rw [← sitU]; exact screenχ _ _ ht
 · have ht:= colorTravel g V' 1; rw [one_smul,one_smul] at ht; rw [ht]; refine flashD _ _ _ _ ?_; rw [screenχ _ _ he]; exact p
 rw [←seaChange]; exact screenA ..
end StageQ
end YM.CF.Swell.Sonar
