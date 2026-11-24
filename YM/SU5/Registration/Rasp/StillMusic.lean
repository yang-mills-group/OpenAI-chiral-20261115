import YM.SU5.Registration.Rasp.Lighting
import YM.SU5.Registration.Heave.MildStitch
import YM.SU5.Registration.Affine.StageAgenda
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "S"=>(P.seasons a (P.advocate 3 x a))
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "G"=>(P.ManyF a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
local notation "T₀"=> (S).E
local notation "Ω"=> P.heaven a ξ
local notation "T"=> timeMesh P.par
open Swatch
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
/-!
 # Extend to gauge and sold trumpets on M8's character
 Keep same point fields. Estimates on the M4 prices, not bootstrap in all
 observers (W only at axis3, including its required partner). See M7 for H estimates.
-/
open Swatch Aria Casting SatinJets Drums OS.Semigroup
-- include original protagonist y (even when other's operations), used here also to extract widths. Not granted every character as qualified for `HandleWith`.
variable (y:P.Spectrum0 3)
local notation "j₁"=> (3:Axis)
local notation "ξ₁" x:max=> P.advocate 3 x j₁
local notation "G₁" x:max=> P.ManyF j₁ (ξ₁ x)
local notation "T₁" x:max=> P.seasons j₁ (ξ₁ x)
variable (A:ℕ→ P.Apron)(K:Set P.Swatch)
local notation "S!" x:max t:max b:max i:max=> P.stageG 3 (P.advocate 3 x 3) (b i) t t
local notation "QA"=> ordinary A
local notation "QB"=> ordinary (fun i=> P.drumStep (A i))
local notation "Qc" n:max=> ordinary (fun i=> P.festival (A i) n)
universe ν
variable (T':StillCurtain.{ν} P j₁ K (ordinary A))(V: Tendsto (fun i=>(A i).s) atTop atTop)
include T' V y
lemma step_included : StillCurtain.{ν} P j₁ K QB:=by
 let h:= T'.card P j₁ K QA; let g:= P.light_music A h V; let f(x):=P.music_step x _ (h.all x) V
 exact P.cinematic_issue j₁ K QB ⟨(f y).thin,Sponsor.threshold _ _ _ _ g (by simpa using h), f⟩ {QA} g (by simpa using T') -- simpa forall i singleton
lemma festival_all_peaks (n:ℕ) : StillCurtain.{ν} P j₁ K (Qc n):=by
 induction n with
 | zero=> exact T'
 | succ n b=> exact P.step_included y (fun i=>P.festival (A i) n) K b (by simpa only [festival_s] using V)
variable (w:Prism)
noncomputable abbrev selectionBand (P:Spine) (A:ℕ→P.Apron)(w:Prism):= Swatch.ordinary (fun i=> P.aTuba w (A i))
local notation "QW"=> P.selectionBand A w
local notation "V!" x:max i:max s:max t:max n:max=> (Qc n).Wstage x j₁ s t i
lemma issuing_music : P.ClearScore j₁ (fun n=> Qc (n+1)) w.support (fun n=>w n) QW:=by
 intro s u
 let F(n:ℕ):= StillCurtain.card P j₁ K _ (festival_all_peaks.{ν} P y A K T' V n)
 let d(i):= P.burst (A i).s; have he:Tendsto d atTop (𝓝 0):=P.burst_zero.comp V
 have hx:= he.const_add s; let Z(n:ℕ)(i:ℕ)(x):= w n • V! x i s s (n+1); let X(n:ℕ)(i:ℕ)(x):= w n • V! x i (s+d i) (s-d i) (n+1)
 have h(n): SatinRegistration.Agrees atTop (X n) (Z n):= P.piece_fixed j₁ ((F (n+1)).wander P j₁ (Qc (n+1)) s u (by simpa using hx) (by simpa using Tendsto.sub (tendsto_const_nhds (x:=s)) he)) (w n)
 -- thirst for widths of keyboard. no Bought3 needed
 have hg(j:Axis): Tendsto (fun i=>(A i).realWidth P j) atTop (𝓝 0):= (P.yearly_cap y A ((StillCurtain.card P j₁ K QA T').all y)).1 j
 have hu:= issuing_music.new_tubas P A V w hg -- where edit
 refine (SatinRegistration.of_eq (?_)).trans (P.piece_sum j₁ (l:=w.support) X Z (fun i _=>h i)); filter_upwards [(hu j₁).eventually (ge_mem_nhds u)] with i h; funext x
 change (ordinary (fun i=> P.aTuba w (A i))).Wstage x j₁ s s i=_; rw [P.ordinary_paper,P.kid_costG x w (A i) s h]; simp only [X, P.ordinary_paper, d]
where
 new_tubas (P:Spine)(A:ℕ→P.Apron)(q:Tendsto (fun i=>(A i).s) atTop atTop)(w:Prism)(g:P.ThinHere A): (Swatch.ordinary (fun i=> P.aTuba w (A i))).Finishes:=by
    intro j; apply NNReal.tendsto_coe.mp
    change Tendsto (fun i=>(((P.aTuba w (A i)).allowance P j):ℝ)) atTop (𝓝 0)
    simp_rw [←Apron.width_real,P.tuba_width]
    simpa only [mul_zero,add_zero,Function.comp_apply] using (g j).add ((P.macroStep_zero.comp q).const_mul _)
lemma tubes_funded : StillCurtain.{ν} P j₁ K (P.selectionBand A w) := ClearScore.cinematic P j₁ K _ _ _ _ (P.issuing_music y A K T' V w) (fun n=>festival_all_peaks P y A K T' V (n+1)) ((issuing_music.new_tubas.{ν} P _ V w ((P.yearly_cap y A ((StillCurtain.card P j₁ K QA T').all y)).1))) -- where binder nonimplicit tune
omit T' V y

-- clear single sponsor unit for seam. compare at all characters.
section stitch
variable (c r n:ℕ→ℕ)(Z:Lead.Clan)(X:P.HandleWith y c r A n)(u:P.ThinHere (P.ClaimedAt c r n A Z))(d:∀ x:P.Spectrum0 3,P.Guest x c r A n)
local notation "B"=> P.ClaimedAt c r n A Z
local notation "B'"=> P.MildAt c r n A Z
local notation "vB"=> ordinary (P.ClaimedAt c r n A Z)
local notation "vC"=> ordinary (P.MildAt c r n A Z)
local notation "F"=> fun _ : Unit=> ordinary A
local notation "w'" i:max=> (A i).allowance P j₁
local notation "ζ"=> (purePrice Z:ℂ)
-- **Target score orientation and moment invoices** on actual drummed stencil.
include u
lemma material_thin : (vB).Finishes:=by
 intro j; apply NNReal.tendsto_coe.mp; change Tendsto (fun i=> (( (B i).allowance P j):ℝ)) atTop (𝓝 0); simp_rw [←Apron.width_real]; exact u j
include y d X
variable (s:ℝ≥0)
-- eventual over all x
lemma votes_everyone (v:0<s) : ∀ᶠ i:ℕ in atTop,∀ x:P.Spectrum0 3, dist (S! x s B i) (ζ • P.stageG j₁ (ξ₁ x) (A i) (s + w' i) (s-w' i)) ≤ P.macroStep i:=by
 have ht:= (P.material_thin A c r n Z u j₁).eventually (ge_mem_nhds v); filter_upwards [ht] with i v x; rw [dist_eq_norm,stageG,stageG,← map_smul,← map_sub]; exact (P.toG_cost ..).trans ((P.unseam (ξ₁ x) (A i) Z _ _ (X.already i) ((d x).covers i Z) s v).trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)).trans ((d x).expenses i Z))) -- B left P.ClaimedAt; inflation factor.
omit d X y
omit u in
lemma wants_seam (Y:P.Commission j₁ (QA))(p:ℕ→P.Apron)(t:∀ s:ℝ≥0,0<s→Agrees (b:=fun x:P.Spectrum0 3=> (G₁ x).Op) atTop (fun i x=>P.stageG j₁ (ξ₁ x) (p i) s s) (fun i x=> ζ • P.stageG j₁ (ξ₁ x) (A i) (s+w' i) (s-w' i))) : P.ClearScore j₁ (F) Finset.univ (fun _=>ζ) (ordinary p):=by -- omit u
 intro s h; let ψ(k:ℕ):= w' k; have he:Tendsto ψ atTop (𝓝 0):= Y.being j₁
 have hx := Commission.wander P j₁ QA Y s h (show Tendsto (fun i=>s+ψ i) atTop (𝓝 s) from by simpa using he.const_add s) (show Tendsto (fun i=>s - ψ i) atTop (𝓝 s) from by simpa using Tendsto.sub (tendsto_const_nhds (x:=s)) he); have hu:= (t s h); simp_rw [P.ordinary_paper]; rw [show (@Finset.univ Unit _)= {()} from (by decide)] -- sum singleton but under binder need simp only
 simp_rw [sum_singleton]; refine hu.trans ?_; simp_rw [P.ordinary_paper] at hx; exact P.piece_fixed j₁ hx ζ
include y d X
lemma seam_score_all (p:P.Commission j₁ QA): P.ClearScore j₁ (F) Finset.univ (fun _=>ζ) vB:=by
 apply P.wants_seam A Z p _; intro s h e v; filter_upwards [P.votes_everyone y A c r n Z X u d s h,P.macroStep_zero.eventually (ge_mem_nhds v)] with i b p x; exact (b x).trans p
omit d
lemma gauze_score_all (p:P.Commission j₁ QA): P.ClearScore j₁ (F) Finset.univ (fun _=>ζ) vC:=by
 apply P.wants_seam A Z p _; intro s h e v; filter_upwards [(P.material_thin A c r n Z u j₁).eventually (ge_mem_nhds h)] with i e' x; have hv:S! x s B' i= ζ • P.stageG j₁ (ξ₁ x) (A i) (s+w' i) (s-w' i):=by
    change P.toStageG j₁ (ξ₁ x) (P.stageH j₁ (ξ₁ x) (P.gaugeStitch Z (A i) _ _) s s)= _; rw [P.gate_price Z (c (n i)) (r (n i)) _ (X.already i),map_smul]; first|rfl|skip
    exact e'
 rw [hv]; exact (dist_self _).le.trans v.le
include d T'
local notation "W+" a:max=> P.soldTrumpet A c r n a Z
lemma music_stage (w:Lead.Clan→Prism)(v:Tendsto (fun i=> c (n i)) atTop atTop):
     StillCurtain.{ν} P j₁ K (ordinary (P.soldTrumpet A c r n w Z)):=by
 apply P.tubes_funded y (B) K (ClearScore.cinematic P j₁ K _ _ _ _ (P.seam_score_all y A c r n Z X u d (T'.card P j₁ K QA)) (fun _=>T') (P.material_thin A c r n Z u)) v (w Z)
omit d
lemma music_gauze (w:Lead.Clan→Prism)(v:Tendsto (fun i=> c (n i)) atTop atTop):
     StillCurtain.{ν} P j₁ K (ordinary (P.gaugeTrumpet A c r n w Z)):=P.tubes_funded y (B') K (ClearScore.cinematic P j₁ K _ _ _ _ (P.gauze_score_all y A c r n Z X u (T'.card P j₁ K QA)) (fun _=>T') (P.material_thin A c r n Z u)) v (w Z)
omit T' u X y
end stitch
-- applicable on M8 A.
abbrev SalonBasis : Set P.Swatch:= Set.range (fun l:List Axis=> ordinary (fun i=>(A i).pivot P l))
local notation "aK"=> P.SalonBasis A
lemma salon_selected : (QA) ∈ P.SalonBasis A:=⟨[],rfl⟩
variable (p:PlanetaryG.{ν} P A) {J:Type ν} (L:List J)
include p y
lemma Booking (W:P.Swatch)(h: W∈P.SalonBasis A): P.Commission a W:=by obtain ⟨l,rfl⟩:=h; let T':= p.purchase a l; exact ⟨(T'.2 y).thin,T'.1,T'.2⟩
lemma salon_any (W:P.Swatch)(h: W∈P.SalonBasis A): StillCurtain.{ν} P a (aK) W:=by
 refine ⟨Extensions.donors P a (aK) W h (P.Booking a y A p W h), Extensions.donors P a (aK) _ ?_ (Commission.turns P a W (P.Booking a y A p W h))⟩ -- `..` might metavars proof. fix
 obtain ⟨l,rfl⟩:=h; refine ⟨a::l,?_⟩; simp_rw [Apron.pivot_cons,P.ordinary_kiss] -- inside Eq orientation
lemma salon_paper (W:J→P.Swatch) (T':∀ i, W i∈ Extensions.{ν} P a (aK)): P.Paper a L W:=by
 apply Paper.all_in _ _ (aK) L W ⟨QA,P.salon_selected A⟩ (fun j h=>P.Booking a y A p j h) ?_ T'; intro V h
 choose l hl using (fun j=> h j); exact fun u p' b f=> p.reads a l V u L p' (fun i=> (hl i).symm) b f

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.tubes_funded
#print axioms Spine.issuing_music
#print axioms Spine.seam_score_all
#print axioms Spine.gauze_score_all
#print axioms Spine.music_stage
#print axioms Spine.salon_any
#print axioms Spine.salon_paper
