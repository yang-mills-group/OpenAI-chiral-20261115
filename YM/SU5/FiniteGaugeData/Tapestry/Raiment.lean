import YM.SU5.FiniteGaugeData.Tapestry.Vista
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

open Py Py.Rate LocalLimit Preparation Journey Vale
set_option quotPrecheck false
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable (s i k:ℕ)
lemma sizes : (side Y i (s+1)).val=(side Y i s).val*Λ.R.L.val:= (apt (Y.ir i) Λ.block Λ.R.L s).exact_size
abbrev patternβ := (((Y.voyage i).X (Y.uv k)).gram (s+1)).beta
lemma eventualPairIdx (i:ℕ) : ∀ᶠ k in atTop, Satin.PairIdx Y s i k:= (eventually_ge_atTop ((Y.voyage i).kick)).and (Y.uv_grows.tendsto_atTop.eventually_ge_atTop (s+1))
include Y in
lemma threshold : 0<Λ.J.d ∧ 2*Λ.J.d < firstRadius SU.group := by
  obtain ⟨k,a⟩:=(eventualPairIdx Y (0:ℕ) 0).exists -- order? s omitted if not included?
  obtain ⟨l⟩:= (fullness Y 0 k a.1).cap_grant.grant 0 a.2; exact l.legal
lemma gaugeSizes : (More (side Y i (s+1))).val=(More (side Y i s)).val*Λ.R.L.val:= (ratio (apt (Y.ir i) Λ.block Λ.R.L s)).exact_size
lemma alignedMarks : patternA Y s i k=({patch:=Λ.R, kernel:=Λ.K.bind,sizes:=gaugeSizes Y s i} : StepData (More (side Y i s)) (More (side Y i (s+1)))):= matchEq _ (Y.pilot_steps s i k).1 (Y.pilot_steps s i k).2.1 (gaugeSizes Y s i)
where
  matchEq {n m:Side}{p:Patch}{u:KernelChoices} (A:StepData n m) (x:A.patch=p)(y:A.kernel=u) (h:m.val=n.val*p.L.val): A=⟨p,u,h⟩:= by cases A; subst_vars; rfl
include Y in
lemma sharpBranches : Λ.R.Branches Λ.K.bind SU.group:= by
  obtain ⟨p,q,t⟩:=Y.pilot_steps 0 0 0; rwa [p,q] at t

variable {I: Type*}(S: Finset Cover)(a b:I→ℕ)(p:∀ i,Satin.PairIdx Y s (a i) (b i))
local notation "K"=> tent Y H
local notation "N" i:max=> side Y (a i) s
local notation "P" i:max=> side Y (a i) (s+1)
local notation "Ω" i:max=> patternA Y s (a i) (b i)
local notation "β" i:max=> patternβ Y s (a i) (b i)
local notation "W" i:max x:max=> replant (followBox (Λ:=Λ) (l:=l) S) (P i) x
local notation "G" i:max=> Vale.apt (Y.ir (a i)) Λ.block Λ.R.L s
local notation "μ" i:max=> city (N i)

private def attentionMark (i:I)(x:PairsC)(V:Orbit (side Y (a i) s)) : ℝ:= (Ω i).density (β i) (W i x).1 V.1
include p
local notation "D"=> attentionMark Y s S a b
lemma densityMenu (δ:ℝ)(v:0<δ):∃ P':Deck PairsC,P'.dark∧∀ x y, P'.withZ x y→∀ i u, |D i x u-D i y u| ≤ δ* D i y u := by
  obtain ⟨T,h,W'⟩:= relative_deck (fun i=>More (N i)) (fun i=>P i) Λ.R Λ.K.bind (fun i=> gaugeSizes Y s (a i)) (sharpBranches Y) (followBox (Λ:=Λ) (l:=l) S) (fun i=>β i) (fun i=> (show |patternβ Y s (a i) (b i)| ≤ Course.ceiling Λ s from abs_le.mpr (Y.seated s (a i) (b i) (p i).2))) δ v
  refine ⟨T,h,fun x y v i V=>?_⟩; unfold attentionMark; rw [alignedMarks]; exact W' x y v i V.1
omit p
lemma attentionPos (x:PairsC)(i:I)(z):0≤ D i x z:= StepData.density_positive ..
private lemma branchesA (i:I) : (Ω i).patch.Branches (Ω i).kernel SU.group := (Y.pilot_steps s (a i) (b i)).2.2
lemma attentionCost (x:PairsC)(i:I):Envelope (D i x):= Env.along (g:=Prod.fst) (slice_env (Ω i) (β i) (branchesA ..) _) measurable_fst
lemma attentionTotal (x:PairsC)(i:I): (∫ t,D i x t∂μ i)=1:=by unfold attentionMark city; rw [integral_fun_fst]; simp [(Ω i).density_total (branchesA Y s a b i)]

variable {C:ℝ}(f:I→Swatch S)(v:∀ i,‖f i‖≤ C)
local notation "run" i:max=> gathered (G i) Λ.K.j (patternQ Y s (a i) (b i)).val (((Y.voyage (a i)).X (Y.uv (b i))).gram (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d
local notation "α" i:max=> drawn ((Y.voyage (a i)).CapeT s)
private def billowed (i:I)(x:PairsC)(V: Orbit (side Y (a i) s)): FC (Single (side Y (a i) (s+1))) := (run i) (present Y H s (a i) S (f i)) (W i x) ((α i) V)
-- use single Pres cost
lemma ready_gathered (xi:ℕ) (F:Swatch S) (u:Fields (side Y xi s)) :
  present Y H s xi S F u=∑ i:Evens S, daub S (F i) (Prod.map (onC _) (onC _) u) • spool (side Y xi s) (tagWord S i.val):= broadcast (tent Y H) S F (momentm Y xi s) (side Y xi s) (terrain Y H (Y.ir xi) s) _
where
 broadcast (K':Calibration)(S':Finset Cover)(F:Swatch S')(m z:Side)(p:K'.c m=z)(v:Fields z): arrange (K'.c m) z p (appear S' K' m F) v= ∑ i:Evens S', daub S' (F i) (Prod.map (onC z) (onC z) v) • spool z (tagWord S' i.val):=by subst z; exact appearSpool ..

lemma summing_billow (i:I)(x:PairsC)(u:Fields (N i)) : (run i) (present Y H s (a i) S (f i)) (W i x) u=∑ j:Evens S, daub S (f i j) (Prod.map (onC _) (onC _) u) • ((run i) (wholeZ (N i) (tagWord S j.val)) (W i x) u):=by
  unfold gathered avgF before wholeZ
  simp_rw [ready_gathered Y H s S, map_sum,map_smul]; rw [sum_comm]; simp_rw [←Finset.smul_sum]; rw [Finset.smul_sum]; apply sum_congr rfl; intro j u; rw [smul_comm] -- tune, want move c out on left then averaging prime R both.
include p v
lemma clothMenu : Menu (T:=fun i=> FC (Single (P i))) (fun i x=> ascender Y s (a i) (b i) (present Y H s (a i) S (f i)) (W i x)):=by
  let A:= billowed Y H s S a b f
  let J:= Σ i:I, Orbit (N i); let ν:J→I:=fun i=> i.fst
  let h(i:J)(r:Evens S):= daub S (f (ν i) r) (Prod.map (onC _) (onC _) ((α (ν i)) i.2))
  let X(i:I):= present Y H s (a i) S (f i)
  let V(i:I):= P i
  let Z:= legal Λ
  have v':Menu (T:=fun i: Σ i:I,Orbit (N i)=> FC (Single (V (ν i)))) (fun i x=> A (ν i) x i.2):=by
    unfold A billowed; simp_rw [summing_billow]
    apply Menu.total (T:=fun i:J=> FC (Single (V (ν i)))) (X:=PairsC) _ (fun (r:Evens S) i x=> h i r • ((run (ν i)) (wholeZ (N (ν i)) (tagWord S r.val)) (W (ν i) x) ((α (ν i)) i.2)))
    intro i _; have hm: Menu (T:=fun j:J=> ℂ) (X:=PairsC) (fun j _=> h j i):= Menu.cnst _ (le_max_right C 0) (fun j=> (daubLe ..).trans ((norm_le_pi_norm ..).trans ((v (ν j)).trans (le_max_left ..))))
    refine hm.scale (upperSewn (fun i:J=>N (ν i)) (fun i:J=> P (ν i)) Λ.R.L (fun i:J=> sizes Y s (a (ν i))) _ Chi.canonical Λ.J.d (threshold Y).1 (threshold Y).2 Λ.K.j _ (Journey.legal Λ) Λ.R.odd_side _ _ (fun i:J=> ((Y.voyage (a (ν i))).X (Y.uv (b (ν i)))).pull.tip s (p (ν i)).2) (fun i=> (α (ν i)) i.2) _)
  apply Menu.congr (f:=fun i x=>∫ t:Orbit (N i), D i x t • A i x t∂μ i) _ (fun i x=>?_) -- order
  · exact honored (fun i:I=>μ i) D A v' (fun i x=> attentionPos Y s S a b x i) (fun i x=> attentionTotal Y s S a b x i) (fun i x=> Env.integrableX (attentionCost ..) (city _)) (fun i x y=> pushIntegrable (G i) (Ω i) Λ.K.j _ _ Λ.R.odd_side Chi.canonical Λ.J.d (β i) ((Y.voyage (a i)).CapeT s) _ (Journey.legal _) ((Y.voyage (a i)).ownership s).paid.bill (branchesA Y s a b i) (threshold Y).1 (threshold Y).2 (presented Y H s (a i) S (f i)).env (W i y) ((W i x).1)) (densityMenu Y s S a b p)
  exact (outright (G i) (Ω i) Λ.K.j _ _ Λ.R.odd_side Chi.canonical Λ.J.d _ ((Y.voyage (a i)).CapeT s) (Journey.legal Λ) ((Y.voyage (a i)).ownership s).paid.bill (branchesA Y s a b i) (threshold Y).1 (threshold Y).2 _ (presented Y H s (a i) S (f i)).env (W i x)).symm
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.clothMenu
