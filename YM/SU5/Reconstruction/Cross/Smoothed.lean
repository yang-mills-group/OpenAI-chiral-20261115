import YM.SU5.Reconstruction.Cross.Offset
import YM.SU5.Reconstruction.Cross.Slot
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
open _root_.YM.SelectionAnalysis Vacancy.Average
section average
-- average of raw projections; borrow Multigrid.point and Conveyance's CP4 full offset prices
variable {A : Hilbert} {J:Type*} {M : Mesh}
private lemma collapse₂ {X:Type*}[PseudoMetricSpace X] (g : ℕ → ℕ → X) (z:ℕ→X) (x:X) (p:Tendsto z atTop (𝓝 x)) (q:∀ m,Tendsto (g m) atTop (𝓝 (z m))) : Tendsto (fun v:ℕ×ℕ=> g v.1 v.2) nested (𝓝 x):=by
 rw [Metric.tendsto_nhds]; intro ε e
 rw [eventually_curry_iff]
 filter_upwards [Metric.tendsto_nhds.mp p (ε/2) (half_pos e)] with i hi
 filter_upwards [Metric.tendsto_nhds.mp (q i) (ε/2) (half_pos e)] with j hj
 refine lt_of_le_of_lt (dist_triangle (g i j) (z i) x) ?_
 linarith only [hi,hj]

lemma ignoresExtras (S : Alliance J (marks M) A) (t: List J) {u v : J→marks M} (p : ∀ i ∈ t,u i=v i) :
  S.raw t u = S.raw t v:=by
  induction t with
  | nil=> exact Eq.refl (ContinuousLinearMap.id ℂ A.space)
  | cons i t ih=> rw [S.raw_step,S.raw_step t i v,p i (List.Mem.head ..), ih (fun i e=>p i (List.Mem.tail _ e))] -- tune

noncomputable def probeOffset (s t:ℕ) (i:Fin (M.L^t)) : marks M := notch M (s+t) i.val

local notation "S○" s:max t:max q:max=> probeOffset (M:=M) s t q
local notation "R" s:max => Fin (M.L^s)
lemma centerActs {A : Hilbert} {U:Type*}[Fintype U](x:A)(L: U→ A.Op): (Average.center L) x= Average.center (fun i=> L i x) := (Average.natural L (ContinuousLinearMap.apply ℂ A.space x)).symm
-- manifest defEq robustness across installer choices (classical vs decidable function-space)
lemma reAverage {U : Type*} {V : Type*}[NormedAddCommGroup U][NormedSpace ℂ U] {a b : Fintype V} (y : V → U) (z : U) (h : @Average.center _ a _ _ _ y=z): @Average.center _ b _ _ _ y=z:= by cases Subsingleton.elim a b; exact h

lemma ranges_axis [Fintype J] (S:Alliance J (marks M) A) (t:List J) (p:t.Nodup) (l n:ℕ):
    Average.center (fun q : J → Fin (M.L^n)=> S.raw t (fun i=> probeOffset (M:=M) l n (q i)))= Rides.first M S t l n:=by
 classical
 haveI := avg_lives M n
 induction t with
 | nil=>simp only [Alliance.raw_nil,Average.constant]; rfl
 | cons i t ih=>
    obtain ⟨v,u⟩:=List.nodup_cons.mp p
    rw [Rides.first_step,←ih u]
    let f:=Equiv.funSplitAt i (R n)
    let d(q:J→R n) := S.raw t (fun i=> (S○ l n (q i)))
    let h(q:Other J i→R n) := f.symm ((Classical.arbitrary _ : R n),q)
    have he(x)(q): d (f.symm (x,q))=d (h q):=ignoresExtras _ _ (by
       intro j u; unfold h f; rw [Average.stands _ _ _ (show j≠i from fun e=>v (e ▸ u)),Average.stands _ _ _ (show j≠i from fun e=>v (e ▸ u))])
    have ht:Average.center d= Average.center (fun q=> d (h q)):=by
       rw [Average.point i]
       simp_rw [show ∀ x q, d ((Equiv.funSplitAt i (R n)).symm (x,q))= d (h q) from he,Average.constant] -- tune
    ext w
    -- ext may expands Hilbert dim nonsense
    rw [Average.point i]; let U(q:R n):=(S.crew i).play (S○ l n q)
    have hx(q:R n)(p:Other J i→ R n): S.raw (i::t) (fun j=> (S○ l n (f.symm (q,p) j)))=(U q).comp (d (h p)):=by rw [Alliance.raw_step]; unfold f; rw [Average.stops i]; exact congrArg _ (he q p)
    change (Average.center (fun x=> Average.center (fun z=> S.raw (i::t) (fun j=> S○ l n (f.symm (x,z) j))))) w= (average M _ _ _).comp (Average.center d) w
    rw [ht]
    simp only [hx,centerActs,ContinuousLinearMap.comp_apply,avgvalue]
    apply Average.eq_of; intro p'; rw [Average.natural]; rfl -- inspect

variable {j:Axis} (S:Alliance (Trans j) (marks M) A)
local notation "U" x:max=> ambient (M:=M) S x
lemma among_lives (t n:ℕ): Average.center (fun p:Samples M n=> ambient (M:=M) S (offsets M t n p)) = Rides.first M S (look j) t n:=by
  haveI:= avg_lives M n
  -- use installed f split with our decidability, TRADE accepts any Fintype
  let Y := Equiv.funSplitAt j (R n)
  rw [← Average.trade Y.symm (fun p:Samples M n=> U (offsets M t n p)),Average.domino] -- check
  unfold Y
  have ht (a:R n) (x:Other Axis j→R n) : U (offsets M t n ((Equiv.funSplitAt j _).symm (a,x)))=S.raw (look j) (fun i=> S○ t n (x i)) :=by
    apply ignoresExtras; intro i h; change S○ t n ((Equiv.funSplitAt j _).symm (a,x) i.val)= _
    -- must match Classical prop case vs Axis DecEq implement
    simp [i.property]
  simp_rw [ht,Aveq S t n,Average.constant] -- Aveq transports Base-L presentation!
where
 Aveq (S : Alliance (Trans j) (marks M) A) (t n:ℕ) : Average.center (fun p:Other Axis j→R n=> S.raw (look j) (fun i=> S○ t n (p i)))= Rides.first M S (look j) t n := by
    -- Fintype mismatch
    exact reAverage _ _ (ranges_axis S (look j) (look_one j) t n)
lemma crew_add (t u:seeMesh M) : ambient (M:=M) S (t+u)= (ambient (M:=M) S t).comp (ambient (M:=M) S u):=
  S.travelR (look j) (fun i=>t i.val) (fun i=>u i.val)
lemma glide (v:seeMesh M)(x:A) : Tendsto (smear M (fun t=> (U t) x) v) nested (𝓝 ((U v) ((S.aviator (look j)).starProjection x))):=by
  let Q (t n:ℕ):= (U v) (Rides.first M S (look j) t n x); let Z(i:ℕ):=(U v) (Rides.camp M S (look j) i x)
  rw [show smear _ (fun t=> (U t) x) v=(fun p:ℕ×ℕ=> Q p.1 p.2) from ?_]; swap
  · funext i; unfold smear Q; simp_rw [crew_add,ContinuousLinearMap.comp_apply,Average.natural]; rw [← among_lives S]; congr 1; exact Average.natural (fun p:Samples M i.2=>U (offsets M i.1 i.2 p)) (ContinuousLinearMap.apply ℂ A.space x)
  refine collapse₂ Q Z _ ?_ (fun i=> ((U v).continuous.tendsto _).comp (Rides.consec ..))
  rw [← stack_projection S]; exact ((U v).continuous.tendsto _).comp (Rides.onwards ..)
end average
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.glide
