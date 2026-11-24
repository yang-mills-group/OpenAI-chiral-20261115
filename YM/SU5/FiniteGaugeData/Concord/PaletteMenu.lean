import YM.SU5.FiniteGaugeData.Concord.Upper
import YM.SU5.FiniteGaugeData.Concord.Rehearsal
/-!
# Output-side compact size budgets for the whole operator. Don't bet stabilization of Last.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover)(s:ℕ)

-- clipped array, retaining necessary gates; for each support these open past period and cutoff thresholds.
local notation "S₁" => swept Λ l S
local notation "T₀" => plaza (Λ:=Λ) S
local notation "K₀" => tent Y H
local notation "C" => (VolumeCape.Dream.plot l).C

structure Stadium (i:ℕ): Prop where
  lower : Tipping (plaza (Λ:=Λ) S) (side Y i s) (VolumeCape.Dream.plot l).C
  bigger : Hosp (tips (swept Λ l S)) ((tent Y H).c (momentm Y i (s+1)))

lemma crowd : ∀ᶠ i:ℕ in atTop, Stadium Y H S s i:= (can_pack Y H s).mono fun _ t=> ⟨t.1,t.2⟩

structure SeasonPass (i k:ℕ) : Prop where
  main : Stadium Y H S s i
  timely : PairIdx Y s i k

abbrev Matinee := {p:ℕ×ℕ // SeasonPass Y H S s p.1 p.2}

def present (i k:ℕ)(p:SeasonPass Y H S s i k) : Palette S→ₗ[ℂ] Palette (swept Λ l S):= concert Y H s p.timely S p.main.bigger

-- single-column expansion, certify embedding from arbitrary actual unit-bounded inputs

def flyer (i:Evens S) (f:swatches S) : Palette S:= Pi.single i f

@[simp] lemma flyer_add (i:Evens S)(f g:swatches S) : flyer S i (f+g)=flyer S i f+flyer S i g:= Pi.single_add ..
@[simp] lemma flyer_smul (i:Evens S)(f:swatches S)(c:ℂ): flyer S i (c • f)=c • flyer S i f:=by unfold flyer; rw [Pi.single_smul] -- lemma?

lemma band_fly (K:Calibration)(i:Evens S)(f:swatches S): pigment S K (flyer S i f)=note K (tint S f) (tagWord S i.val):=by
  rw [pigment_formula, sum_eq_single i, flyer, Pi.single_eq_same]
  · intro j _ p; unfold flyer; rw [Pi.single_eq_of_ne p]; change singleNote _ _ _ 0 = 0; rw [map_zero] -- need specialize
  simp
lemma with_fly (i:Evens S)(f:swatches S)(n:ℕ): nativeHere Y H n s S (flyer S i f)=Satin.knot (side Y n s) (tagWord S i.val) (tint S f):=by rw [nativeHere_eq,band_fly,observe_nota]

lemma all_fly (f:Palette S) : f = ∑ i:Evens S, flyer S i (f i) :=by
  ext1 i; rw [Finset.sum_apply, sum_eq_single i,flyer, Pi.single_eq_same];swap; · simp
  intro _ _ p; exact Pi.single_eq_of_ne p.symm _

-- Menu uniform across f in bounded Swatch and any tipped page
section
variable {I:Type*}(J : I→ Matinee Y H S s)
local notation "Mx" i:max => (J i).1.1
local notation "Fx" i:max => (J i).1.2
local notation "cx" i:max => side Y (Mx i) s
local notation "upx" i:max => side Y (Mx i) (s+1)
local notation "beforeX" i:max => (Y.voyage (Mx i)).X (Y.uv (Fx i))
local notation "Qs" i:max => ((beforeX i).wave s).val
local notation "Ys" i:max => ((beforeX i).gram (s+1))
local notation "watch" i:max => haul Y s (Mx i) (Fx i)
local notation "play" i:max => present Y H S s _ _ (J i).property
local notation "αt" i:max=> (Y.voyage (Mx i)).CapeT s
local notation "αT" i:max=> ((K₀).c (momentm Y (Mx i) (s+1)))
local notation "Rt" => Λ.R
local notation "px" i:max=> (J i).property
variable (g:I→ Palette S){c₀:ℝ}(c:0≤c₀)(g₀:∀ i,‖g i‖ ≤ c₀)

private lemma branch_same (N P: Side)(A B:StepData N P)(h:A.patch=B.patch)(t:A.kernel=B.kernel) : A=B:=by cases A; cases B; congr

include g₀ c
private lemma afterEat (t:Evens S): Menu (T:=fun i=>FC (Single (upx i)))
    (fun i x=> (nativeHere Y H (Mx i) (s+1) (swept Λ l S) ((play i) (flyer S t (g i t)))) (replant (swept Λ l S) (upx i) x)) := by
  rcases isEmpty_or_nonempty I with a|a
  · exact Menu.zero.congr (fun (i:I)=> isEmptyElim i)
  let L:= Λ.R.L; let C' (i:I):= cx i; let P(i:I):=upx i; let K':=(VolumeCape.Dream.plot l).K
  let u(i:I):=toPurse S (g i t)
  let U:=tagWord S t.val
  let b(i:I):= (px i).timely; let s₁(i:I):= (px i).main
  have sz(i:I):(P i).val=(C' i).val*L.val:=(apt (Y.ir (Mx i)) Λ.block L s).exact_size
  let γ:= slate (I:=I) P Rt Λ.K.bind C' sz
  have hv(i:I): steps Λ.V (Y.ir (Mx i)) Λ.block (Y.uv (Fx i)) s=γ i:= branch_same (More (C' i)) (More (P i)) _ _ (Y.pilot_steps s (Mx i) (Fx i)).1 (Y.pilot_steps s (Mx i) (Fx i)).2.1
  have ht(i:I):VolumeCape.Dream.Haven C K' (C' i) (αt i):= (Y.voyage (Mx i)).craft _
  choose μ A₀ θ Z using ht
  letI p':∀i,IsProbabilityMeasure (μ i):=A₀
  let i:=Classical.choice a
  have hB:= (can_cane Y s (i:=(Mx i)) (k:=(Fx i)) (b i)); have hz:= Journey.legal Λ
  have v:Λ.R.Branches Λ.K.bind SU.group:=by
    have h:= (fullness Y (Mx i) (Fx i) (b i).1).cap_grant.branch s (b i).2; rw [hv] at h; exact h
  have Hp:= cards (swept Λ l S) P C' Rt sz Chi.canonical Λ.J.d hB.1 hB.2 Λ.K.j (aliasLaw Λ) hz (fun i=>(Ys i).J.M) (fun i=> Qs i)
    (d:=Λ.R0 (hat Λ.R.L Λ.x s)) (fun i=> (beforeX i).pull.tip s (b i).2) U Λ.K.bind C S T₀ K' (fun i=>(Ys i).beta) (x:=Course.ceiling Λ s) (fun i=> abs_le.mpr (Y.seated s (Mx i) (Fx i) (b i).2)) μ u (b₀:=c₀) (fun i x=> (tint_bound S (g i t) x).trans ((norm_le_pi_norm ..).trans (g₀ i))) c (liner_here ..) (fun i=> (s₁ i).lower) (fun i :I=> αt i) (fun i=>((Y.voyage (Mx i)).ownership s).paid.bill) Z (fun i=> ?_) (fun _=> linen_contains ..) v -- too many (fun _)
  · apply Hp.congr; intro i x
    change _= nativeHere _ _ _ _ _ (concert _ _ _ _ _ _ _) _
    rw [repertoire, with_fly]; unfold haul nextMark; rw [hv]; rfl
  · change AtSupport (Sound.treble U) (region S (side Y _ s)) (knot (side Y _ s) _ _)
    rw [show Sound.treble U=false from t.property]; let n:= Mx i
    exact with_fly Y H S s t (g i t) n ▸ nativeHere_support Y H n s S (flyer S t (g i t))

local notation "Wa" i:max=> replant (swept Λ l S) (upx i)
/-- Vary BOTH period and cutoff, and test itself, keeping local box, level and envelope. -/
lemma wholeHouse : Menu (T:=fun i=> FC (Single (upx i))) (fun i x=> nativeHere Y H (Mx i) (s+1) (swept Λ l S) ((play i) (g i)) ((Wa i) x)):=by
  refine (Menu.total (univ:Finset (Evens S)) (fun t (i:I) x=> nativeHere Y H (Mx i) (s+1) (swept Λ l S) ((play i) (flyer S t (g i t))) ((Wa i) x)) (fun t _=> afterEat Y H S s J g c g₀ t)).congr ?_
  intro i x; conv_rhs => rw [all_fly S (g i)]
  simp_rw [map_sum,Finset.sum_apply]

lemma palette_house (t:Evens (swept Λ l S)) : Menu (fun i=> tint (swept Λ l S) ((play i) (g i) t)) := by
  let A(i:I):= native (swept Λ l S) K₀ (momentm Y (Mx i) (s+1)) ((play i) (g i))
  have h': Menu (T:=fun (i:I)=> FC (Single (αT i))) (fun i x=> A i (replant (swept Λ l S) _ x)):=by
    obtain ⟨h₀,D,d,h⟩:=wholeHouse Y H S s J g c g₀
    refine ⟨?_,D,d,fun i x=> ?_⟩; swap
    · rw [←Copies.constantPost (y:=upx i) (terrain Y H (Y.ir (Mx i)) (s+1))]; exact h i x
    intro ε e; obtain ⟨b,u,z⟩:= h₀ ε e; refine ⟨b,u,fun x y v i=> ?_⟩
    rw [←Copies.constantDist (y:=upx i) (terrain Y H (Y.ir (Mx i)) (s+1))]; exact z x y v i
  let P'(i:I):= bandCoord (K:=tent Y H) (roomy ((px i).main.bigger)) t
  have u: Menu (T:=fun (_:I)=>ℂ) (fun i x=> P' i (A i (replant (swept Λ l S) (αT i) x))) := by
    obtain ⟨D,b,k,h'⟩:= h'; refine ⟨Deal.along (U:=fun _=>ℂ) (fun (i:I) x=> P' i x) D ?_, b,k,fun i x=> (band_bound ..).trans (h' i x)⟩
    intro ε e; refine ⟨ε,e,fun i x y v=>?_⟩; rw [dist_eq_norm,← map_sub]; exact lt_of_le_of_lt (band_bound ..) (by simpa only [dist_eq_norm] using v)
  exact u.congr fun i x=> (band_painted (K:=K₀) (roomy ((px i).main.bigger)) _ x t).symm

lemma house_bound:∃ b:ℝ,0≤b ∧ ∀ i, ‖(play i) (g i)‖ ≤ b:=by
  choose b₁ B C' using fun x:Evens (swept Λ l S)=> (palette_house Y H S s J g c g₀ x).budget
  let b:=∑ i,b₁ i; have he:0≤b:=sum_nonneg fun i _=>B i; refine ⟨b,he,fun i=> (pi_norm_le_iff_of_nonneg he).2 (fun k=> (swatches_norm_le _ he).2 (fun u=> le_trans (C' k i u) ?_))⟩
  exact single_le_sum (fun k _=> B k) (mem_univ _)
end

lemma local_post_bound : ∃ c:ℝ, 0 ≤ c ∧ ∀ i k (t : SeasonPass Y H S s i k) (f:Palette S), ‖present Y H S s i k t f‖ ≤ c*‖f‖:=by
  let J := closedBall (0 : Palette S) 1
  obtain ⟨c,d,h⟩:= house_bound (I:=Matinee Y H S s × ↥J) Y H S s Prod.fst (fun i=> i.2.val) zero_le_one (fun i=> mem_closedBall_zero_iff.mp i.2.property)
  refine ⟨c,d,fun i k t f=>?_⟩; by_cases he:f=0; · subst f; simp
  have he':0<‖f‖:=norm_pos_iff.mpr he; let F:= (‖f‖⁻¹:ℂ) • f
  have hu:‖F‖=1:=by unfold F; rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg he'.le,inv_mul_cancel₀ he'.ne']
  specialize h (show Matinee Y H S s × ↥J from (⟨⟨i,k⟩,t⟩,⟨F,mem_closedBall_zero_iff.mpr hu.le⟩))
  change ‖present Y H S s i k t F‖≤c at h
  unfold F at h; rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg he'.le,mul_comm,←div_eq_mul_inv] at h
  exact (div_le_iff₀ he').1 h

local notation "κ"=> (local_post_bound Y H S s).choose
/-- Clipped to zero offline; qualify support & gates before identifying. -/
def screen (i k:ℕ) : Palette S→L[ℂ] Palette (swept Λ l S) := if h:SeasonPass Y H S s i k then
  (present Y H S s i k h).mkContinuous κ ((local_post_bound Y H S s).choose_spec.2 i k h)
  else 0

lemma house {i k:ℕ}(t:SeasonPass Y H S s i k)(f:Palette S): screen Y H S s i k f=concert Y H s t.timely S t.main.bigger f := by unfold screen; rw [dif_pos t]; rfl
lemma stall {i k:ℕ}(t:¬ SeasonPass Y H S s i k) : screen Y H S s i k=0:= dif_neg t
lemma posted (i k:ℕ) : ‖screen Y H S s i k‖≤κ := by
  unfold screen; split
  · exact LinearMap.mkContinuous_norm_le _ (local_post_bound Y H S s).choose_spec.1 _
  rw [ContinuousLinearMap.opNorm_zero]; exact (local_post_bound Y H S s).choose_spec.1
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.posted
#print axioms YM.CF.Buffered.Concord.palette_house
