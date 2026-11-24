import YM.CF.Vp929.Retag.Entry
set_option autoImplicit false
set_option maxHeartbeats 400000
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
/-! Factor the gas sum. -/
variable {n:Side} (c:Clip)(b p:BudgetPoint)(z:ℂ)(A:ℂ→L[ℝ]ℝ) (V:Orbit n)
variable (D X:Support (More n))
def groups (h:Finset (Force n)):=h.biUnion marks = D ∧ (h:Set (Force n)).PairwiseDisjoint patch
private lemma reconstruct_record (F:Finset (Force n))(hh : ∀ i∈F, Used b i) (hx : groups D F) : F.image marks = parts (widen b) D ∧ Set.InjOn (@marks n) (↑F) := by
  let L:=F.image marks
  have he(x)(h:x∈L): Ac.Spark (pad (widen b)) x:=by obtain ⟨j,hj,rfl⟩:= mem_image.mp h; exact (hh j hj).1
  have hu := Ac.separates (pad (widen b)) L he (by
    rintro x hx' y hy g; obtain ⟨i,h,rfl⟩:= mem_image.mp hx'; obtain ⟨j,w,rfl⟩:= mem_image.mp hy; change Disjoint (tiles b _) (tiles b _); rw [←(hh i h).2,←(hh j w).2]; exact hx.2 h w (ne_of_apply_ne _ g))
  have ht : L.biUnion id=D:= by unfold L; rw [Finset.image_biUnion]; exact hx.1
  rw [ht] at hu; refine ⟨hu.symm,fun i hi j hj e=> ?_⟩
  obtain ⟨x,h⟩:= i.property.1; by_contra h'
  exact Finset.disjoint_left.mp (hx.2 hi hj h') (i.property.2 h) (j.property.2 (by change x∈ marks j; rw [←e]; exact h))
abbrev Chart (X:Support (More n)) := {i:Force n // Used b i ∧ marks i=X}
lemma chart_equiv (h : Ac.Spark (pad (widen b)) X) : Nonempty (Chart b X ≃ (tiles b X)) := by
  refine ⟨Equiv.ofBijective (fun i:Chart b X=> (⟨anchor i.val, ?_⟩ : ↥(tiles b X))) ?_⟩
  · rw [← (i.property.1.2.trans (congrArg (tiles b) i.property.2))]; exact i.val.val.1.property
  constructor
  · intro i j e; have hp : marks i.val=marks j.val:=i.property.2.trans j.property.2.symm
    exact Subtype.ext (Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (Subtype.ext_iff.mp e) (by change patch _=patch _; rw [i.property.1.2,j.property.1.2,hp]))) hp))
  intro i; exact ⟨⟨⟨(⟨(i.val,tiles b X),i.property⟩,X),h.1,subset_region ..⟩,⟨h,rfl⟩,rfl⟩,rfl⟩
local notation "P"=> parts (widen b) D
abbrev Charting:= ∀ i : P, Chart b i.val
def record (f:Charting b D):= univ.image fun i:P=> (f i).val
lemma record_mem (f:Charting b D) (F:Force n): F∈record b D f ↔ ∃ i:P,(f i).val=F:= by simp [record]
lemma record_inj (f:Charting b D): Injective fun i:P=>(f i).val:= fun x y e=> Subtype.ext ((f x).property.2.symm.trans ((congrArg marks e).trans (f y).property.2))
private lemma inj_choice: Injective (record b D):=by
  intro f g h; apply funext; intro i; obtain ⟨j,hj⟩:= (record_mem b D g _).mp (h ▸ ((record_mem b D f _).mpr ⟨i,rfl⟩))
  have e:j=i:= Subtype.ext ((g j).property.2.symm.trans ((congrArg marks hj).trans (f i).property.2)); subst j; exact Subtype.ext hj.symm
private lemma represented {F:Finset (Force n)}(h : groups D F)(p : ∀ i∈F, Used b i): F ∈ Set.range (record b D):=by
  obtain ⟨hr,ht⟩:= reconstruct_record b D F p h
  choose f e using (show ∀ i : P, ∃ f : Chart b i.val, f.val∈ F from fun i=> by
    obtain ⟨j,hj,h'⟩:= mem_image.mp (show (i.val : Support (More n)) ∈ F.image marks from (by rw [hr]; exact i.property)); exact ⟨⟨j,p j hj,h'⟩,hj⟩)
  refine ⟨f, Finset.Subset.antisymm (fun i H=> ?_) fun i H=>?_⟩
  · obtain ⟨i,rfl⟩:= (record_mem b D f _).mp H; exact e i
  let x:P:=⟨marks i, hr ▸ mem_image_of_mem marks H⟩; exact (record_mem b D f _).mpr ⟨x,ht (e x) H (f x).property.2⟩
lemma recorded(f:Charting b D):groups D (record b D f):=by
  have he : (record b D f).image marks=P:= by
    ext i; rw [mem_image]; constructor
    · rintro ⟨j,hj,rfl⟩; obtain ⟨i,rfl⟩:= (record_mem b D f _).mp hj; rw [(f i).property.2]; exact i.property
    intro h; let x:P:=⟨i,h⟩; exact ⟨_,(record_mem b D f _).mpr ⟨x,rfl⟩,(f x).property.2⟩
  constructor
  · have h:= Ac.reconstruct (pad (widen b)) D; rw [← (show _=Ac.Parts (pad (widen b)) D from he),Finset.image_biUnion] at h; exact h
  rintro i h j w g; obtain ⟨i,rfl⟩:= (record_mem ..).mp h; obtain ⟨j,rfl⟩:= (record_mem ..).mp w; show Disjoint (patch _) (patch _); rw [(f i).property.1.2,(f j).property.1.2,(f i).property.2,(f j).property.2]; exact Ac.separate _ _ i.property j.property ((Subtype.coe_injective.ne_iff).mpr (ne_of_apply_ne (fun x↦ (f x).val) g))
lemma unclamp (hv : Rue.FleetS b.threshold V.1) (i : parts (widen b) (flags b.threshold V.1)) (f:Chart b i.val)(F:ForceBudget n) : clamp b f.val (F f.val) V= F f.val V:= by
  unfold clamp; rw [if_pos]; apply (shoreK _ _ hv _).mp; refine Finset.disjoint_left.mpr fun x H g=>?_; change x∈ patch f.val\marks f.val at H; rw [f.property.1.2,f.property.2] at H
  exact (mem_sdiff.mp H).2 (coverage (widen b) (flags b.threshold V.1) i.property ▸ mem_inter.mpr ⟨(mem_sdiff.mp H).1,g⟩)
lemma sum_chart (hv : Ac.Spark (pad (widen b)) X) : (∑ f:Chart b X, entry c b p z A f.val V) = moldV n (minted c b p z A V.1 X):= by
  have hu:(0:ℝ)<(tiles b X).card:= by exact_mod_cast card_pos.mpr (hv.1.mono (subset_region ..))
  have he(f:Chart b X): entry c b p z A f.val V= (#(tiles b X):ℝ)⁻¹ • moldV n (minted c b p z A V.1 X):= by rw [entry,if_pos f.property.1,f.property.1.2,f.property.2,← smul_eq_mul, map_smul]
  simp_rw [he,sum_const,card_univ,Fintype.card_congr (chart_equiv b X hv).some,Fintype.card_coe]; rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,mul_inv_cancel₀ (ne_of_gt hu),one_smul]
lemma registry (hv:Rue.FleetS b.threshold V.1) : fueled b (entry c b p z A) V= ∏ D∈parts (widen b) (flags b.threshold V.1), moldV n (minted c b p z A V.1 D):=by
  let D:=flags b.threshold V.1; let F(Mx:Support (More n)) := moldV n (minted c b p z A V.1 Mx)
  have he : (∏ i∈parts (widen b) D,F i) = ∑ f:Charting b D, ∏ i : parts (widen b) D, entry c b p z A (f i).val V:=by rw [←prod_coe_sort]; simp_rw [show ∀ i : parts (widen b) D,F i.val=_ from fun i=> (sum_chart c b p z A V i.val (Ac.lives (pad (widen b)) D i.property).2).symm]; rw [Fintype.prod_sum]
  rw [fueled]; change _=∏ i∈parts (widen b) D,F i; rw [he]; symm
  -- only registrars
  refine Fintype.sum_of_injective (record b D) (inj_choice b D) _ _ (fun i hi=> ?_) fun i=>?_
  · split_ifs with h; swap; · rfl
    by_contra he; apply hi; refine represented b D h fun j hj=>?_ ; by_contra hj'; have hx:clamp b j (entry c b p z A j) V=0:=by unfold clamp; split; exact if_neg hj'; rfl
    exact he (prod_eq_zero hj hx)
  rw [if_pos (show coverF b _ V.1 ∧ _ from ⟨(recorded b D i).1,(recorded b D i).2⟩),record,prod_image (record_inj b D i).injOn]; exact prod_congr rfl fun j _=> (unclamp b V hv j (i j) _).symm
end YM.CF.SplitFlag
