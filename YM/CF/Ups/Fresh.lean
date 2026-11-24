import YM.CF.Ups.Lush
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
variable {x':ℕ→ℝ}(t:Tendsto x' atTop atTop){L':ℕ→ℕ} (U':∀ i',SpanPS V a p i N0 J q h R0 δ (x' i') (L' i'))
local notation "N_X"=> rimZ V N0 J (x':=x')
variable(X:Month x a i p N0 V W) (H:MeterQ V a p i N0 J q h R0 δ x X)
open Graph
local notation "Mo"=> oYY V N0 J x
local notation "Zo" j:max=>cell Mo B R.L j
variable {ℓ:ℝ}(hp:1≤h)(ht:0 <ℓ)(hx:0 < x)
open Pyx
local notation "hatQ"=> hat R.L x
variable (L0:∀ l:ℕ,SpanPS V a p i N0 J q h R0 δ x l)(R':Cape (oYY V N0 J x) B R.L)(Q:CoilPS V a p i N0 J q h R0 δ X L0 R')
-- common kernels for this torus geometry and clock
abbrev PionK (M B:Side)(W:Cape M B R.L)(q:Chi)(j:ℕ)(d:ℝ)(β:ℝ)(A:Haro.SpaceM)(x:Orbit (cell M B R.L j))(y:Orbit (cell M B R.L (j+1))): Phys (cell M B R.L (j+1)) →L[ℝ] Phys (cell M B R.L j):= Pyx.Fps (j:=K.j) (apt M B R.L j) (W j) (W (j+1)) q d (V.L.op 0 (kint M B R.L j)) β A x y
section
include V J x
private theorem crownPS(j k:ℕ): V.L.op k (kint Mo B R.L j)= V.L.op 0 (kint Mo B R.L j):=by
 have hp(i:ℕ): V.L.op i (kint Mo B R.L j)=⟨R,K.bind,kint Mo B R.L j⟩:=by
    cases h: V.L.op i (kint Mo B R.L j) with|mk Y Z t=> have ht:Y=R:=Eq.trans (congrArg StepData.patch h.symm) (V.L.lent i); have hv: Z=K.bind:=Eq.trans (congrArg StepData.kernel h.symm) rfl; congr
 exact (hp _).trans (hp 0).symm
end
local notation "Fp"=>PionK V Mo B R' q
-- test include
abbrev ν_P(j l:ℕ): Orbit (cell (oYY V N0 J x) B R.L j)→ Phys (cell (oYY V N0 J x) B R.L j):= ω_den U ((L0 l).E j) (R' j)
#check ν_P
local notation "Eρ"=> ν_P V a p i N0 J q h R0 δ L0 R'
section
include Q
lemma book_ps (j l:ℕ)(z:j<l) :∀ᵐ y: Orbit (Zo j) ∂city _,(Eρ j l) y= ∫ u,Fp j J.d ((L0 l).E (j+1)).beta ((L0 l).Q j) y u (Eρ (j+1) l u) ∂city _:=by
 let K':= L0 l; let X0:= K'.E j; let X1:=K'.E (j+1); let Bv:=partitionZ X0 U (R' j); let v:= city (Zo j); let f:= Fp j J.d X1.beta (K'.Q j); have e:=Q.tale l; have ht:=K'.scale; have hzM: Rue.IsleB SU.group X0.p.threshold:= (ht.note.owns j z.le).width ▸ ht.mark _
 apply Eventually.mono ((Measure.quasiMeasurePreserving_fst (μ:=prior SU.group (More (Zo j))) (ν:=depot (Zo j))).ae (hzM (More (Zo j)))); intro y t; have hp0:= ht.note.wear j z y t; have hw: K'.Y=R':=e; have hz: Bv=partitionZ X1 U (R' (j+1)):=by unfold Bv; rw [←hw]; exact (ht.balance _ (by omega)).trans (ht.balance _ (by omega)|>.symm)
 have he:= crownPS (x:=x) V N0 J j (l-1-j) -- h shadow fix
 rw [hw,he] at hp0; let T:= V.L.op 0 (kint Mo B R.L j); let H(u):= integrated U (R' j) X1 (R' (j+1)) (apt Mo B R.L j) T q J.d (K'.Q j).val y u
 change Bv⁻¹ • denZ X0 U (R' j) y=∫ u,f y u _∂city _; rw [show denZ X0 U (R' j) y=∫ u,H u ∂city _ from hp0.symm,← integral_smul]; apply integral_congr_ae; apply Eventually.of_forall; intro xZ; let P:= (Eρ (j+1) l) xZ; change _ = f y xZ P; rw [hz]; exact (Fps_path (apt Mo B R.L j) _ _ _ _ T y xZ U _ _).symm -- ABI
open scoped ENNReal
-- separate without adding topology to labels
end
open scoped ENNReal
private theorem pst_sep (n:Side): MeasureTheory.IsSeparable (city n):=by
 letI : TopologicalSpace (Sweep n):=⊥
 letI : DiscreteTopology (Sweep n):=⟨rfl⟩
 letI : BorelSpace (Sweep n):= ⟨by exact borel_eq_top_of_discrete.symm⟩
 haveI st:SecondCountableTopology (Sweep n):=inferInstance
 haveI sk:SecondCountableTopology (Orbit n):=inferInstance
 haveI bk:BorelSpace (Orbit n):=inferInstance
 haveI mk:MeasurableSpace.CountablyGenerated (Orbit n):=inferInstance
 infer_instance
attribute [local instance] pst_sep
local instance : Fact ((2:ℝ≥0∞)≠⊤):=⟨by norm_num⟩

abbrev InkPS (n:Side):= Lp (Phys n) 2 (city n)
-- finite dimensions pointwise smoothing in fine variables ⇒ weak L² scan emits exact AEn normalized amplitudes.Plans.Epoch calendar explicitly loop.Act.Structure notion.
local notation "ρ_L" j:max=> InkPS (Zo j)
structure ΦS_P (β:ℕ→ℝ)(A:ℕ→Haro.SpaceM)(G:∀ i, InkPS (cell (oYY V N0 J x) B R.L i))(u:ℕ→ℕ):Prop where
 hz:StrictMono u
 plate(j:ℕ): matchedX (hat R.L x j) (β j)
 beat(j:ℕ): ‖A j‖≤ R0 (hat R.L x j)
 jug(j:ℕ) : ∀ xR, Integrable (fun y:Orbit (cell (oYY V N0 J x) B R.L (j+1))=> PionK V (oYY V N0 J x) B R' q j J.d (β (j+1)) (A j) xR y (G (j+1) y)) (city _)
 cog(j:ℕ): ∀ᵐ xQ∂city (cell (oYY V N0 J x) B R.L j),G j xQ = ∫ y,PionK V (oYY V N0 J x) B R' q j J.d (β (j+1)) (A j) xQ y (G (j+1) y) ∂city _
 lampB(j:ℕ): Tendsto (fun t=>((L0 (u t)).E j).beta) atTop (𝓝 (β j))
 lampA(j:ℕ): Tendsto (fun t=> (L0 (u t)).Q j) atTop (𝓝 (A j))
 stay(j:ℕ):∀ᵐ x∂city (cell (oYY V N0 J x) B R.L j),Tendsto (fun t=> (ν_P V a p i N0 J q h R0 δ L0 R' j (u t) x)) atTop (𝓝 (G j x))
include Q hx
set_option maxHeartbeats 2200000 in
theorem sol_g :∃ (β:ℕ→ℝ)(A:ℕ→Haro.SpaceM)(G:∀ i,InkPS (cell (oYY V N0 J x) B R.L i))(u:ℕ→ℕ), ΦS_P V a p i N0 J q h R0 δ L0 R' β A G u:=by
 let βk(j l:ℕ): Set ℝ := Set.Icc (hatQ j/2) (2*hatQ j); let wt(j):=R0 (hatQ j); have ht(i):0 ≤ wt i:= (norm_nonneg _).trans ((L0 (i+1)).scale.note.tip i (by omega)); have hz(i): 0 < hatQ i := lt_of_lt_of_le hx (crown ..)
 let Z(j):= (βk j 0) × (Metric.closedBall (0:Haro.SpaceM) (wt j)); -- using subtypes? coeSort
 letI vZ:∀ i, CompactSpace (Z i):=fun j=>by
    letI pp:CompactSpace (βk j 0):= isCompact_iff_compactSpace.mp isCompact_Icc; letI qq: CompactSpace (Metric.closedBall (0:Haro.SpaceM) (wt j)):=isCompact_iff_compactSpace.mp (isCompact_closedBall _ _); unfold Z; infer_instance
 let Kβ(j l): βk j 0:= let P:=max j l; ⟨((L0 P).E j).beta,(L0 P).scale.note.sift _ (le_max_left ..)⟩
 let A0(j l):Z j:= let x:=max (j+1) l; (Kβ j l,⟨(L0 x).Q j, mem_closedBall_zero_iff.mpr ((L0 x).scale.note.tip _ (show j<x from Nat.succ_le_iff.mp (le_max_left ..)))⟩)
 choose S L using Q.stain; have hA(j l:ℕ):MemLp (Eρ j (max j l)) 2 (city (Zo j)):=MemLp.of_bound (Q.port _ _ (le_max_left j l)).meas.aestronglyMeasurable (S j) (Eventually.of_forall fun i=> L j _ (le_max_left ..) _); let TK(j l):InkPS (Zo j):=(hA j l).toLp (Eρ j (max j l)); have he(j l): (⇑(TK j l))=ᵐ[city (Zo j)] Eρ j (max j l):= MemLp.coeFn_toLp _
 have hv(j l):∀ᵐ x∂city (Zo j),‖TK j l x‖≤ S j:=(he j l).mono fun x q=>by change _≤_; rw [q]; exact L j _ (le_max_left ..) x
 have hp(j l:ℕ): ‖TK j l‖≤ S j:=by
    have hS:0 ≤ S j:=by obtain ⟨x,h⟩:=(hv j l).exists; exact (norm_nonneg _).trans h
    rw [Lp.norm_def]; refine le_trans (ENNReal.toReal_mono ?_ (eLpNorm_le_of_ae_bound (hv j l))) ?_ <;> simp [hS]
 obtain ⟨O,F,σ,hσ,pW⟩:= TopPS.treat TK hp A0
 let β(j):= (O j).1.val; let A(j):=(O j).2.val
 have hu(j:ℕ):Tendsto (fun i=> (Kβ j (σ i)).val) atTop (𝓝 (β j)):= (continuous_subtype_val.tendsto _).comp ((continuous_fst.tendsto _).comp (pW j).1); have hM(j:ℕ):Tendsto (fun i:ℕ=> (A0 j (σ i)).2.val) atTop (𝓝 (A j)):= (continuous_subtype_val.tendsto _).comp ((continuous_snd.tendsto _).comp (pW j).1)
 let dΘ(j:ℕ)(k:ℕ):= Kβ j (σ k); let dA(j k):= (A0 j (σ k)).2; let Wψ(j l):= TK j (σ l)
 let η(j):=Fp j J.d (β (j+1)) (A j); let f(j k):= Fp j J.d (dΘ (j+1) k).val (dA j k).val
 let lim(j:ℕ)(y:Orbit (Zo j)):=∫ x',η j y x' (F (j+1) x') ∂city _
 have hT(k):∀ᶠ i in atTop,k<σ i:= hσ.tendsto_atTop.eventually (eventually_gt_atTop k)
 have hk(j v l:ℕ)(p':j<σ l)(h': v ≤ j+1): (dΘ v l).val=((L0 (σ l)).E v).beta:=by unfold dΘ Kβ; dsimp only; rw [max_eq_right (by omega:v ≤ σ l)]
 have hh(j l)(v:j<σ l): (dA j l).val=(L0 (σ l)).Q j:=by change (L0 (max (j+1) (σ l))).Q j=_; rw [max_eq_right v]
 have hc(j v l:ℕ)(p':j<σ l)(h': v ≤ j+1):(⇑(Wψ v l))=ᵐ[city _] Eρ v (σ l):=by have hh:= he v (σ l); rw [max_eq_right (by omega:v≤σ l)] at hh; exact hh
 let Vt(j:ℕ)(y:Orbit (Zo j))(i:ℕ):=∫ x,f j i y x (Wψ (j+1) i x) ∂city _
 have hg(j:ℕ)(Y:Orbit (Zo j)): Integrable (fun x'=>η j Y x' (F (j+1) x')) (city _) ∧ Tendsto (Vt j Y) atTop (𝓝 (lim j Y)):=by
    let g:= apt Mo B R.L j; let T':=V.L.op 0 (kint Mo B R.L j); let X':= L0 (j+1); let Vp:= X'.scale; have e:X'.Y=R':=Q.tale _; obtain ⟨K⟩:= Brioche.us V X'.tip J q h Vp j (by omega); let K':Girt.BaseL U g (X'.E (j+1)) (R' j) (R' (j+1)) q J.d:= e ▸ K
    have he : T'.ratio= ratio g ∧ T'.patch.Branches T'.kernel SU.group:=by
       have he:=Brioche.drives V X'.tip J q h Vp j; rw [crownPS (x:=x) V N0 J j (j+1-1-j)] at he; exact he
    obtain ⟨C,b⟩:= earn_ps U g (R' j) (R' (j+1)) q J.d K' T' he.1 he.2 Y (2*hatQ (j+1)) (wt j) (ht j)
    have h(i): ‖(dA j i).val‖≤wt j:=mem_closedBall_zero_iff.mp (dA j i).property; have hp(i):|(dΘ (j+1) i).val|≤2*hatQ (j+1):=by
       let X:=dΘ (j+1) i; have hz:0≤X.val:= le_trans (show 0 ≤ hatQ (j+1)/2 from (half_pos (hz (j+1))).le) X.property.1; rw [abs_of_nonneg hz]; exact X.property.2
    have ht:i=i:=rfl
    refine TopPS.shell_P (city _) _ _ (pW (j+1)).2 (fun i=> hv _ _) (fun i x=> f j i Y x) (fun i=> (b _ (h i) _ (hp i)).1.aestronglyMeasurable) _ (fun i=>Eventually.of_forall ((b _ (h i) _ (hp i)).2)) (Eventually.of_forall fun z=>?_ )
    let hd:= color_ps U g (R' j) (R' (j+1)) q J.d K' T' he.1 he.2 Y z; let Kps(y:ℝ × Haro.SpaceM):= Fp j J.d y.1 y.2 Y z; change Tendsto (fun i:ℕ=>f j i Y z) atTop (𝓝 (η j Y z)); apply (Continuous.tendsto (f:=Kps) hd (β (j+1),A j)).comp (f:=fun i=> ((dΘ (j+1) i).val,(dA j i).val)); exact (hu (j+1)).prodMk_nhds (hM j)
 have hg'(j:ℕ)(m:ℕ)(p':j<σ m): (⇑(Wψ j m)) =ᵐ[city _] (fun y=> Vt j y m):=by
    refine (hc j j m p' (by omega)).trans ?_; have he:=book_ps V a p i N0 J q h R0 δ X L0 R' Q j _ p'; filter_upwards [he] with t u; change _ = Vt j t m; refine u.trans ?_
    unfold Vt f; simp_rw [hk j _ m p' le_rfl,hh j m p']; exact integral_congr_ae ((hc _ _ _ p' le_rfl).mono fun y q=> by dsimp only; rw [q])

 have hZ(j:ℕ):∀ᵐ i∂city _,Tendsto (fun v:ℕ=> Wψ j v i) atTop (𝓝 (lim j i)):=by
    have ht:= ae_all_iff.mpr fun i: {i:ℕ // j<σ i}=> hg' j i.val i.property
    filter_upwards [ht] with i t; exact (hg j i).2.congr' ((hT j).mono fun q v=> (t ⟨q,v⟩).symm)
 have z(j):⇑(F j)=ᵐ[city _] lim j:= TopPS.shade (city _) _ _ (pW j).2 (fun i=>hv ..) (lim j) (hZ j)
 refine ⟨β,A,F,σ,hσ,fun j=>(O j).1.property,fun j=>mem_closedBall_zero_iff.mp (O j).2.property,fun j i=> (hg j i).1,z,fun j=>(hu j).congr' ((hT j).mono fun i v=>hk _ _ _ v (by omega)),fun j=>(hM j).congr' ((hT j).mono fun i v=>hh _ _ v),?_⟩
 intro j; have hp:=ae_all_iff.mpr fun i:{i:ℕ // j<σ i}=> hc j j i i.property (by omega); filter_upwards [hZ j,hp,z j] with x hW hm he; rw [he]; exact hW.congr' ((hT j).mono fun i v=> hm ⟨i,v⟩)
end YM.CF.Py
