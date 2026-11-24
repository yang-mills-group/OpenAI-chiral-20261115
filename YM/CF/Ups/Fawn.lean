import YM.CF.Ups.Leash
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
open Pyx Girt
local notation "hatQ"=> hat R.L x
variable (L0:∀ l:ℕ,SpanPS V a p i N0 J q h R0 δ x l)(R':Cape (oYY V N0 J x) B R.L)(Q:CoilPS V a p i N0 J q h R0 δ X L0 R')
variable {β:ℕ→ℝ}{A:ℕ→Haro.SpaceM}{F:∀ i,InkPS (cell (oYY V N0 J x) B R.L i)}{u:ℕ→ℕ}
local notation "Eρ"=> ν_P V a p i N0 J q h R0 δ L0 R'
variable (dF:ΦS_P V a p i N0 J q h R0 δ L0 R' β A F u)(hpF:K.top.clip.direct ≤1)
include Q hpF
set_option maxHeartbeats 950000 in
private lemma harpy (l k:ℕ)(jQ:k≤l): Hebi (denZ ((L0 l).E (l-k)) U (R' (l-k))):=by
 let Z:= L0 l; let Tp:= Z.scale; have hx:=Q.tale l; have hu(v):Z.Y v=R' v:=congrFun hx _
 induction k with
 |zero=>
    have hxA:= (Brioche.hot V Z.tip J q h Tp hpF).2; intro g; refine Eventually.of_forall ?_; intro y; simp only [Nat.sub_zero]; rw [←hu]; let X:=Z.val.a l; let f(y):=Vale.capP (K:=K) (m:=mesh Mo R.L l) U ((Z.E l).beta) X y
    change denZ (Z.E l) U (Z.Y l) (gird g y)=effectK (tradew (Zo l) g).val (denZ (Z.E l) U (Z.Y l) y); simp_rw [hxA]; let p:= flags X.threshold y.1; have hv: flags X.threshold (Lattice.gauge g y.1)=p:=by unfold p; ext i; simp_rw [flags_spec,face_gauge, Gauge.chord_conj]
    change f (Lattice.gauge g y.1)=effectK (tradew (Zo l) g).val (f y.1); unfold f Vale.capP
    by_cases h:p=∅; swap; · rw [Set.indicator_of_notMem (show Lattice.gauge g y.1∉_ from fun z=>h (hv ▸ z)),Set.indicator_of_notMem (show y.1∉_ from h)]; exact (map_zero (acts _)).symm
    rw [Set.indicator_of_mem (show Lattice.gauge g y.1∈_ from hv.trans h),Set.indicator_of_mem (show y.1∈_ from h)]; rw [Spark.bg]
    let L':= (R' l); have hxZ:= Tp.roof l; rw [hu] at hxZ; let T:=hxZ.paid; have hkZ:L' y=y.1:=by
       have ht:=T.lamp y.1 y.2; have hv: flags J.k y.1=∅:=by refine Finset.eq_empty_iff_forall_notMem.mpr fun i v=>?_ ; obtain ⟨j,p,w⟩:=(flags_spec ..).mp v; have he:i∈flags X.threshold y.1:= (flags_spec ..).2 ⟨j,p,(Tp.pole _).trans_lt w⟩; rw [show flags X.threshold y.1=∅ from h] at he; simp at he
       exact funext fun i=>ht i (by simp [hv])
    have hQj:Guard y.1 d:=hkZ ▸ (T.paid y).shrink J.hr.le; rw [Hive.honey_x W.pearl V.note (J.gran.trans hxZ.size) (by have hp:=V.L.lobby; have he:=R.order_cut; omega) hQj]; exact (map_smul (acts _) ..).symm
 |succ k ih=>
    let j:=l-(k+1); have ht:j<l:=by unfold j; omega
    have hc:l-k=j+1:=by unfold j; omega
    have he:=ih (by omega); rw [hc] at he; obtain ⟨Kb⟩:=Brioche.us V Z.tip J q h Tp j ht; have e: Girt.BaseL U (apt Mo B R.L j) (Z.E (j+1)) (R' j) (R' (j+1)) q J.d:= hu j ▸ hu (j+1) ▸ Kb -- check ▸
    have hx':= Brioche.drives V Z.tip J q h Tp j; let T:= V.L.op (l-1-j) (kint Mo B R.L j); let E':=Z.E j; have hxT: Rue.IsleB SU.group E'.p.threshold:= (Tp.note.owns j ht.le).width ▸ Tp.mark _
    let φ:= stove U (R' j) (Z.E (j+1)) (R' (j+1)) (apt Mo B R.L j) T q J.d (Z.Q j).val; let d:=denZ E' U (R' j); have hz: φ=ᵐ[city _] d:= by
       unfold φ d; rw [←hu j,←hu (j+1)] -- opaque lets. tune
       exact ((Measure.quasiMeasurePreserving_fst (μ:=prior SU.group (More (Zo j))) (ν:=depot (Zo j))).ae (hxT (More (Zo j)))).mono fun i t=> Tp.note.wear j ht i t
    intro g; filter_upwards [hz,(brace_ps g).quasiMeasurePreserving.ae hz] with i p v; change d (gird g i)=effectK (tradew (Zo j) g).val (d i); rw [←p,←v]; exact loaf_p e T hx'.1 hx'.2 (Z.Q j) he g i
include dF
lemma forge_g(j): Hebi (fun x=> F j x):=by
 intro g; let f(i:ℕ):= Eρ j (u i); have hx:∀ k: {k:ℕ// j≤u k},∀ᵐ x∂city _, f k.val (gird g x)=effectK (tradew (Zo j) g).val (f k.val x):=by
    intro k; have h:=harpy V a p i N0 J q h R0 δ X _ _ Q hpF (u k) (u k-j) (Nat.sub_le ..); rw [show u k-(u k-j)=j from (by omega)] at h; refine (h g).mono fun x p=>?_ ; unfold f ν_P ω_den; rw [p]; exact (map_smul (acts _) ..).symm
 have ht:=dF.stay j; have hp:∀ᶠ i in atTop,j≤ u i:= dF.hz.tendsto_atTop.eventually (eventually_ge_atTop j); filter_upwards [ae_all_iff.mpr hx,ht,(brace_ps g).quasiMeasurePreserving.ae ht] with i h p t; apply tendsto_nhds_unique t; let f':=effectK (tradew (Zo j) g).val; exact ( ((show Continuous f' from (acts _).continuous).tendsto _).comp p).congr' (hp.mono fun i p=> (h ⟨i,p⟩).symm)
end YM.CF.Py
