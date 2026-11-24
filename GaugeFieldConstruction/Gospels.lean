import GaugeFieldConstruction.Ixi
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 55000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
variable {N:Side}{A D I E:Type}[Fintype I][LinearOrder I][Fintype A][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
variable (X: Cornea A D E N){p:ℕ}{a b c u r R:ℝ}{J T:Finset (Finset I)}{W:Finset I→A→D→E}
lemma Shelf_roll {U:A→ D→ E}(h: ShelfK X U p a c)(s:b ≤ a): ShelfK X U p b c:=by
 obtain ⟨C,h,v⟩:=h; refine ⟨C,h,fun k=>?_⟩; exact le_trans (sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right s (Nat.cast_nonneg _))) (X.posG _ _ _ (h _))) (v k)
lemma Book_more (h:BookT X W p J a r c)(v:c≤ b): BookT X W p J a r b:=by obtain ⟨C,h,u⟩:=h; exact ⟨C,h,fun i=>(u i).trans v⟩
lemma Book_tie (v: BookT X W p J a r b)(t: BookT X W p T a r c)(px:Disjoint J T): BookT X W p (J∪T) a r (b+c):=by
 obtain ⟨C,h,u⟩:=v; obtain ⟨S,s,q⟩:=t; let H(i:Finset I):= if i∈ J then C i else S i
 have hx(i:I):0 ≤ (1:ℕ):=by omega -- remove
 have hb(i)(x:i∈J):H i=C i:=if_pos x; have ht(i)(x:i∈T):H i=S i:=if_neg (fun v=> disjoint_left.mp px v x)
 refine ⟨H,fun i v x=>?_,fun i=>?_⟩
 · rcases mem_union.mp v with l|r; · rw [hb _ l]; exact h _ l _
   rw [ht _ r]; exact s _ r _
 rw [sum_union px]; refine add_le_add ((Eq.trans_le (sum_congr rfl (fun i v=>?_) : _=_) (u i))) (Eq.trans_le (sum_congr rfl (fun i v=>?_)) (q i)); rw [hb _ v]; rw [ht _ v] -- tune
lemma Book_none (h: ShelfK X (W ∅) p a b): BookT X W p {∅} a r b:=by
 obtain ⟨C,h,V⟩:=h; refine ⟨fun _=>C,fun v p i=>?_,fun i=>?_⟩
 · rw [mem_singleton] at p; rw [p]; exact h i
 rw [sum_singleton,card_empty,pow_zero,one_mul]; exact V i
lemma Book_roll (U:BookT X W p J a r c)(s:b≤ a)(e:T⊆ J)(h:u≤ r)(pU:0≤u): BookT X W p T b u c:=by
 obtain ⟨F,hx,w⟩:=U; refine ⟨F,fun i v=>hx i (e v),fun i=>le_trans ?_ (w i)⟩
 have he(x:ℝ)(t)(p:t∈ J): 0≤ ∑ j∈ univ.filter (fun j:A=>i∈X.Φ j),dra_k ‹ℕ› x (X.Φ j)*F t j:= sum_nonneg (fun i _=>mul_nonneg (Real.exp_pos _).le (X.posG _ _ _ (hx t p i))) -- p binder ‹ℕ› tune
 refine le_trans (sum_le_sum fun j z=> mul_le_mul (pow_le_pow_left₀ pU h j.card) (sum_le_sum (fun i _=> mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right s (Nat.cast_nonneg _))) (X.posG _ _ _ (hx _ (e z) _)))) (he b _ (e z)) (pow_nonneg (pU.trans h) _)) ?_
 exact sum_le_sum_of_subset_of_nonneg e (fun i z _=> mul_nonneg (pow_nonneg (pU.trans h) _) (he a _ z))
-- Strata BookD.Separate mixed. Entry y.P.Total
variable (σ:I→ Site N) (C:I→ I→ℂ) {V:Key I→ A→ D→ E}{κ:ℝ}
abbrev TotsI(σ:I→Site N):= univ.image (fun i:I=>({i}:Finset I))
abbrev AltI(σ:I→Site N):= (realm_C σ).filter (fun i=> 1 < i.card)
lemma Tots_s :TotsI σ ⊆ realm_C σ:=by intro i h; obtain ⟨j,t,rfl⟩:=mem_image.mp h; exact meta_one ..
lemma realm_c : realm_C σ= {∅}∪ (TotsI σ∪AltI σ):=by
 symm; apply Subset.antisymm; · refine union_subset ?_ (union_subset (Tots_s _) (filter_subset ..)); exact singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_univ _, (by simp)⟩) -- tune
 intro i h; by_cases p:i=∅; · rw [p]; simp
 apply mem_union_right; by_cases p':i.card=1; · obtain ⟨j,rfl⟩:=card_eq_one.mp p'; exact mem_union_left _ (mem_image_of_mem _ (mem_univ j))
 have hx:= card_pos.mpr (nonempty_iff_ne_empty.mpr p); exact mem_union_right _ (mem_filter.mpr ⟨h,by omega⟩)
lemma preroot (h:BookT X W p {∅} a r b)(u:BookT X W p (TotsI σ) a r c)(k:BookT X W p (AltI σ) a r R): BookT X W p (realm_C σ) a r (b+(c+R)):=by
 rw [realm_c]; refine Book_tie _ h (Book_tie _ u k ?_) ?_
 · refine disjoint_left.mpr ?_; intro i v q; obtain ⟨w,x,rfl⟩:=mem_image.mp v; have hx:1 < ({w}:Finset I).card:=(mem_filter.mp q).2; simp at hx
 rw [disjoint_singleton_left]; simp [TotsI,AltI]
lemma Book_stow (h:Ledges X σ W)(e:0≤ c)(p':0<r)(t:1 ≤r)(v:8 ≤ p){d:ℕ}(u: lamp_B (cape_B p) p d σ)(p₀:Nice_B p d r (1/32))(f:∀ i:I,ShelfK X (W {i}) p (3/2) c) :BookT X W p (TotsI σ) (11/8) r (d*r*c+ hope_E p c):=by
 have hZ(i)(u:i∈TotsI σ):i.card=1:=by obtain ⟨j,x,rfl⟩:=mem_image.mp u; exact card_singleton _
 refine Book_more _ (Book_single X σ h (Tots_s _) (η:=1) (V:=c) (a:=11/8) ?_ p'.le (by rwa [mul_one]) zero_lt_one u (by rw [mul_one]; exact p₀) v e hZ) (by rw [mul_one])
 intro i w; obtain ⟨j,l,rfl⟩:=mem_image.mp w; rw [one_pow,one_mul, show (11/8:ℝ)+1/8=3/2 by norm_num]; exact f _ -- tune image no simp
structure Harmony (p a:ℕ)(r η:ℝ) :Prop where
    radiusR: 8 ≤ p
    valR:0≤r
    spaceC: 0<η
    stage:1 ≤ r*η
    stamina : Nice_B p a (r*η) (1/32)
variable {m:ℕ}
lemma Book_unmarked (u:Strain X σ V)(y: ShelfK X (V 0) p a b) :BookT X (Boats σ C V) p {∅} a r b:=by
 apply Book_none; refine Shelf_adapt X ?_ y; intro i x e; exact (empty_Φ _ C _ (u i x e).1).symm
lemma Book_touch (u:Strain X σ V)(Z:∀ i:I,ShelfK X (fun x y=>tipI (fun z=> V z x y) [i]) p (3/2) b)(v:Harmony p m r κ)(x:lamp_B (cape_B p) p m σ)(y:0≤b)(k:ColLim σ C κ): BookT X (Boats σ C V) p (TotsI σ) (11/8) r (m*(r*κ)*b+hope_E p b):=by
 refine Book_single X σ (Leads X σ C u) (Tots_s _) ?_ v.valR v.stage v.spaceC x v.stamina v.radiusR y ?_
 · intro i s; obtain ⟨t,h,rfl⟩:=mem_image.mp s; refine BeetK _ _ _ u _ (meta_one ..) k v.spaceC.le y (fun j v t=>?_)
   have h:j.length=1:= t.trans (card_singleton _); obtain ⟨z,rfl⟩:=List.length_eq_one_iff.mp h; rw [show (11/8:ℝ)+1/8=3/2 by norm_num]; exact Z z
 intro i p; obtain ⟨u,y,rfl⟩:=mem_image.mp p; exact card_singleton _
lemma Book_alloys (u:Strain X σ V)(Z:∀ l:List I, ψS σ l→ 2 ≤ l.length → ShelfK X (fun i x=> tipI (fun z=>V z i x) l) p (3/2) b) (v:Harmony p m r κ)(w: Force_M p σ m)(h:0≤b)(k:ColLim σ C κ): BookT X (Boats σ C V) p (AltI σ) (11/8) r (hope_E p b):=by
 refine Book_many X σ (Leads X σ C u) (fun i s=>(mem_filter.mp s).1) ?_ v.valR v.stage v.spaceC w.2 w.1 v.stamina v.radiusR h (fun i p=>(mem_filter.mp p).2)
 intro i t; refine BeetK _ _ _ u _ (mem_filter.mp t).1 k v.spaceC.le h (fun l x u'=>?_); rw [show (11/8:ℝ)+1/8=3/2 by norm_num]; exact Z l x (u'.symm ▸ (Nat.add_one_le_of_lt (mem_filter.mp t).2)) -- tune
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
