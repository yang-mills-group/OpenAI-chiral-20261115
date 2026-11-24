import YM.CF.Vp929.Retag.Afford
import YM.CF.Vp929.Budget.Correction
import YM.Extra.ITERATION_NO_LOSS.Geometry
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.SplitFlag
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
open Ione Beau Haro Cascade
open scoped Mew
open Jet SU Taxi Rue
open WilsonStartup
abbrev marks {n:Side} (i:Force n):=i.val.2
abbrev patch {n:Side} (i:Force n):=i.val.1.val.2
abbrev anchor {n:Side} (i:Force n):=i.val.1.val.1
-- exact entries
variable {n:Side} (c:Clip)(b p:BudgetPoint) (z:ℂ) (A:ℂ→L[ℝ]ℝ) (U:Pane n)
variable (i:Force n)(D: Support (More n)) (σ : ℝ)
def Used:= Ac.Spark (pad (widen b)) (marks i) ∧ patch i=tiles b (marks i)
def Unmasked:=D ⊆ flags b.threshold U ∧ Healthy p.threshold D U
def minted (D:Support (More n)) := if Unmasked b p U D then A (Complex.exp (-z*tagEnergy c b p D U)) else 0
def entry : ForceBudget n:= fun i W=> if Used b i then moldV n ((#(patch i):ℝ)⁻¹ * minted c b p z A W.1 (marks i)) else 0
def offer (D:Support (More n)):= Real.exp (-σ*(D.card:ℝ))
def quote := if Used b i then (#(patch i):ℝ)⁻¹ * offer σ (marks i) else 0
lemma tails (H : 12 ≤ b.B) : inspected D ⊆ tiles b D:=by rw [tiles_spec]; intro i hi; obtain ⟨j,hj,t⟩:= Extra.Iteration.Shapes.inspect_dist D hi; exact halo_spec.mpr ⟨j,hj,(separation_comm _ _) ▸ t.trans (by omega)⟩
lemma minted_reads (H:Decent c b)(he : 12 ≤ b.B) : LocalOn (tiles b D) (fun U=> minted c b p z A U D):=by
  intro U V h; have hh:= fun t=> flags_agree t U V D (agrees_mono h (tails b D he)); unfold minted; simp only [Unmasked,Healthy,Finset.disjoint_iff_inter_eq_empty, ←inter_eq_left]; rw [energy_reads c b p D H he U V h,hh,hh]
lemma minted_gauge (g) : minted c b p z A (Lattice.gauge g U) D=minted c b p z A U D:=by unfold minted; rw [show Unmasked b p (Lattice.gauge g U) D ↔ Unmasked b p U D from by simp only [Unmasked,Healthy,gauge_flags],energy_gauge]
lemma minted_measurable : Measurable fun U=> minted c b p z A U D := by
  unfold minted; refine Measurable.ite ?_ (A.continuous.measurable.comp (Complex.measurable_exp.comp (Measurable.mul measurable_const (Complex.measurable_ofReal.comp (energy_measurable ..))))) measurable_const
  change MeasurableSet {U:Pane n| Unmasked b p U D}; rw [show {U:Pane n| Unmasked b p U D}= (⋂ i : D,{U:Pane n| ↑i ∈ flags b.threshold U}) ∩ {U | Healthy p.threshold D U} from by ext; simp [Unmasked,Finset.subset_iff]]; exact (MeasurableSet.iInter fun i=> (flags_open ..).measurableSet).inter (healthy_closed ..|>.measurableSet)
lemma minted_price (H:Decent c b)(h : b.threshold ≤ p.threshold)(hp : p.threshold≤ Start.threshold SU.group p.order p.power)(hA:∀ x,|A x| ≤ ‖x‖)(hb:0≤z.re)(ht : σ ≤ z.re*(gain b-liabilities c b p)) : |minted c b p z A U D| ≤ offer σ D:= by
  unfold minted offer; split
  next hv =>
    refine (hA _).trans ?_; rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.neg_re,Real.exp_le_exp]; have he:= mul_le_mul_of_nonneg_left (energy_price c b p D U H h hp hv.1) hb; linarith [mul_le_mul_of_nonneg_right ht (show (0:ℝ) ≤ D.card by positivity)]
  rw [abs_zero]; positivity
lemma frozen (X:tangD n) : Agrees (tiles b D) U (increment U (openG b D X)):=by
  rw [tiles_spec]; intro i hi _; have e: ¬ Disjoint (ends i) (Lattice.halo (5*b.B) D):= fun t=> Finset.disjoint_left.mp t (mem_insert_self ..) (Corona.halo_mono (by omega) (Subset.refl _) hi)
  simp [RG.increment,openG,e]
lemma crumbs (x:ℝ)(Z:Finset (Dwell n)) : crumb (moldV n x).val Z=if Z=∅ then ↑x else 0:= by
  rw [mon_v]; by_cases h: Z=∅; · rw [h,if_pos rfl]; exact hullB _
  rw [if_neg h]; change ((x:ℂ) • (1:FC (Dwell n))) Z ∅=0; simp [h]
lemma shape (H:Decent c b)(he : 12 ≤ b.B)(w:ℝ)
    (hh : ∀ U:Pane n, |minted c b p z A U (marks i)| ≤ offer σ (marks i)) : ForceB b i (entry c b p z A i) w (quote b i σ):=by
  unfold quote; split
  next hi=>
    let X:=marks i; let T:=tiles b X; let v:=offer σ X; let k := (#T:ℝ)⁻¹
    have hv:v≥0:=(Real.exp_pos _).le; have hk:k≥0:=by unfold k; positivity
    let f:=fun u=> k*minted c b p z A u X
    have hvid(i':Skye.Orbit n) : entry c b p z A i i'=moldV n (f i'.1):= by rw [entry,if_pos hi,hi.2]
    have hl : LocalOn T f:= fun U V h=> congrArg (k*·) (minted_reads c b p z A X H he U V h)
    refine ⟨fun U V _ _ H _=> by simp_rw [hvid]; exact congrArg _ (hl U V (by rw [show T= patch i from hi.2.symm]; exact H)),fun i'=>?_,fun e=>False.elim (e (by change inspected (marks i) ⊆ patch i; rw [hi.2]; exact tails b (marks i) he)),?_,fun i' h=> ?_,fun V τ g=>?_,?_⟩
    · rw [hvid,mon_v]; exact Flour.grainE.smul _
    · rw [funext hvid]; exact (moldV n).continuous.measurable.comp ((Measurable.mul measurable_const (minted_measurable ..)).comp measurable_fst)
    · contrapose! h; rw [hvid]; unfold f minted; rw [if_neg (fun t : Unmasked b p _ X=> h t.1),mul_zero,map_zero]
    · simp_rw [hvid]; unfold f; rw [minted_gauge]; change _= paintR _ _ _ ( (k*minted c b p z A V X) • (1:Cipher n)); rw [map_smul,map_one]; rfl
    refine ⟨fun i=> if i=∅ then k*v else 0,fun i=>by change 0 ≤ if i=∅ then k*v else 0; split <;> positivity,fun u _ Z=> ?_,?_⟩
    · simp_rw [hvid,crumbs]; have he(i':tangD n): f (increment u.1 (openG b X i'))= f u.1:= (hl _ _ (frozen b u.1 X i')).symm; change Signs _ _ (fun i' : tangD n=>if Z=∅ then (↑(f (RG.increment u.1 (openG b X i'))):ℂ) else 0) _; simp_rw [he]
      by_cases h:Z=∅; simp_rw [if_pos h]; swap
      · simp_rw [if_neg h]; exact Vale.sign_nil ..
      apply Prism.hail; simpa [Real.norm_eq_abs,f, abs_mul, abs_of_nonneg hk] using mul_le_mul_of_nonneg_left (hh u.1) hk
    simp only [mul_ite,mul_zero,sum_ite_eq', mem_univ, if_true]; change tariff b _ _ ∅*(k*v)≤ (#(patch i):ℝ)⁻¹*v; rw [hi.2]; simp [Scree.tariff,Scree.endL,k,T,X]
  next hi=> rw [show entry c b p z A i=0 from funext fun x=>if_neg hi]; exact Vale.rinsed ..
lemma shape_turn (s: Sweep n) (M) (hs:JetS s.s s.charge (detX s.s) M)(V:Pane n)(τ:Ids n):
    entry c b p z A (moveForce s i) (flashA s V,bun s τ)=paintR s.charge (detX s.s) (prepU (castX s) M (xtra s.charge) n) (entry c b p z A i (V,τ)):=by
  let t:=(boxA s).symm.toEmbedding; let T:= ((assembly n).embed s.b)
  let D:=marks i; let X:= patch i
  have hp : tiles b (D.map t)=(tiles b D).map t:=by rw [tiles_spec,tiles_spec, show t= (boxA s⁻¹).toEmbedding from rfl,paysT]
  have ht (W:Support (More n)) : W.map (boxA s).toEmbedding=W.image (affine s.s T):= by rw [map_eq_image]; rfl
  have hu: (D.map t).image (affine s.s T)=D:= by rw [←ht]; ext; simp [t]
  let D':= D.map t
  have he : Used b (moveForce s i) ↔ Used b i:=by unfold Used; change Ac.Spark _ D' ∧ X.map t = tiles b D' ↔ _; rw [show tiles b D'=_ from hp, Finset.map_inj,← spark_transport _ D' s.s T,show D'.image _=_ from hu]
  have hm : Unmasked b p (flashA s V) D' ↔ Unmasked b p V D:= by unfold Unmasked Healthy D'; rw [flagsA,flagsA]; simp only [t,map_subset_map,Finset.disjoint_map]
  have hη : tagEnergy c b p D' (flashA s V)=tagEnergy c b p D V:= by
    have hv(r:Bool)(W:Pane n):tagEnergy c b p D' (polarT r∘W)=tagEnergy c b p D' W:=by cases r; rfl; exact energy_echo ..
    rw [revoke,hv,energy_turn]; exact congrArg (fun y=> tagEnergy c b p y V) hu
  unfold entry; by_cases h: Used b i
  · rw [if_pos h, if_pos (he.mpr h), show patch (moveForce s i)= X.map t from rfl,card_map]; change moldV n ((#X:ℝ)⁻¹ * minted c b p z A (flashA s V) D')= paintR _ _ _ ((_ * minted c b p z A V D) • (1:Cipher n)); unfold minted; rw [hm,hη,map_smul,map_one]; rfl
  rw [if_neg (mt he.mp h),if_neg h,map_zero]
end YM.CF.SplitFlag
