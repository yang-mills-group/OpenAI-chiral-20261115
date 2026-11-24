import YM.SU5.Selected.Cairn.Dawn
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint Mezz Silks Stencil
namespace Giant
variable (A:Giant) {N:Side} (Z:A.Notes→basisRule) {T:Type}[Fintype T][DecidableEq T](P:Society T)(b:Bool)(i:A.Block)
variable {M:Tulip.Male}{δ γ C:ℝ}(e: A.Pride Z C δ γ M N) (q:A.tokenS<N.val)
local notation "L₀"=>stable A Z P b C e q
open Afterglow
local notation "B₀"=> park N A.Broad
local notation "K"=> cutM (Tset N)
variable (c:1≤ C)
include e q c
lemma daily (y t:Bool)(x:Pane N): ‖Hours A Z P y b C i t x‖≤ coastCap C:=by
 let U:= coastCap C; let h:= A.pays Z P b c e; have hx:= capCost C c; have hh:‖filmR A Z P C x‖≤ coastCap C/4:=by rw [← snow A Z P x e]; exact bound_shift (cutM_idp _) ((toll_1 ..).trans_le h.cost)
 have hf:‖filmL A P b C x‖≤ 1/4:= (toll_1 ..).trans_le h.tribute
 have ht(v:WRect (Single N) (A.Plot P)):‖yoke v i t‖≤ ‖v‖:= portion_le _ _ (show Injective (fun a:P.Club=>(t,i,a)) from fun _ _ h=>(Prod.mk.inj (Prod.mk.inj h).2).2)
 cases y; exact (ht _).trans (hh.trans (by linarith)); exact (ht _).trans (hf.trans (by linarith))
local notation "T₀"=> park N A.Core
local notation "η"=> A.sampleW
local notation "w"=> A.bW
local notation "uL"=> wrap (More N) A.hub
abbrev wageL(C:ℝ):= Station.tollK (Tender.dueW (coastCap C)) -- no A
noncomputable def lobo:= Station.chamber T₀ (L₀) 1
#print lobo
local notation "π" => A.lobo Z P b e q
local notation "W′" => coastCap C
variable (d:0≤δ)(v:Brace.Sparkle N δ M 4)(wnd: Winter 4 δ N γ A.debt.val A.snowLine) (s:0< γ) (j:Clear A.rank A.debt.val (coastCap C))
include v d wnd s j
def Humble (τ:ℝ)(t:ℕ):Prop:= Lounge M 4 A.debt.val t τ A.sampleW A.sampleW (wageL C) (coastCap C) δ (A.Sing P) 1 (π)
lemma humid {τ:ℝ}{t:ℕ}(hp:∀ x:Pane N, Disjoint (BlockP t (uL)) (flags τ x) → Rightful B₀ (gauge (stampG (uL) x) x) 1 (min γ (A.bath (C:=C)))) : Humble A Z P b e q τ t:=by
 -- use Station!
 let J:= L₀; have hW:=capCost C c; apply Station.ships J _ _ P.club_card (by simp [Block,Tour.Lolli]) (by decide) _ (image_subset_image A.portT) A.nearBudget (Tender.due_pos W′ (by linarith));
 · intro V i; refine Tender.counter J V P.club_card i W′ (by linarith) (fun t j=> (col_charge ..).trans (daily A Z P b i e q c true t V.1)) (fun t j=>(col_charge ..).trans (daily A Z P b i e q c false t V.1))
 · intro V v0 A' p f; let z:=stampG (uL) V.1; have he: { (uL) } ⊆ B₀:= singleton_subset_iff.mpr (mem_image_of_mem _ (show A.hub∈A.Broad from plant_id ..)); have hx: Rightful B₀ (gauge z V.1) 1 (min γ (A.bath (C:=C))):= hp _ (v0.mono_left (Corona.halo_mono le_rfl he)); -- bath C implicit
   refine coverL A Z P b f e q V z c d v wnd s j p A' ?_; apply (riotPort ..).2; intro t i; obtain ⟨a,k⟩:=(mem_filter.mp i).2; simp only [Lattice.gauge,← A' t a k]; exact (riotPort ..).1 hx _ i
 exact Glow A
omit d v wnd s e q j
include s
lemma hemisphere: ∃ τ>(0:ℝ),∀ N:Side,∀ (M:Tulip.Male)(T:Type) [Fintype T] [DecidableEq T] (P:Society T) (b:Bool) (e: A.Pride Z C δ γ M N) (q:A.tokenS<N.val) (x:ℝ)(p:0 ≤ x)(g:x ≤ τ)(d:0 ≤ δ)(t:ℕ)(z:A.bW+1≤ t)(v:Brace.Sparkle N δ M 4)(wnd: Winter 4 δ N γ A.debt.val A.snowLine) (j:Clear A.rank A.debt.val (coastCap C)), Humble A Z P b e q x t:=by
 let V:= min γ (A.bath (C:=C)); obtain ⟨τ,h,p⟩:= stampG_price A.bW V (lt_min s (A.bath_ps c)); refine ⟨_,h,fun N M T _ _ P b e q z p' v d t t' p₀ w₀ y=>?_⟩
 apply humid A Z P b e q c d p₀ w₀ s y; unfold Broad; rw [park_plant]; exact fun x l=> p _ p' v (by change 2*(A.bW+1)<N.val*2; unfold tokenS at q; have hp:=A.height; omega) t' _ _ l
omit s c
variable {t:ℕ}{p:ℝ}(h: A.Humble Z P b e q p t)(z : safeReflect M 4 δ N)
noncomputable def penumbra : List (Cab N):= [ (π).shadow 3 0,π]
include e q h z
lemma umbra (U:Calibration)(u:addgap U ≤ A.timeGap.val): Lantern.Service M 4 A.debt.val t p η η (wageL C) (coastCap C) δ (A.Sing P) 1 (A.penumbra Z P b e q):=by
 let ht: Lounge M 4 A.debt.val t p _ _ _ _ _ _ _ _ := h; apply Service.append (Service.alone (ht.shadow 3 0 z)) (Service.alone ht); change Disjoint (hyphen 3 0 B₀∪∅) (B₀∪∅); rw [union_empty,union_empty]; exact west U 3 0 _ (A.broad_space u q)
omit h z
lemma shade_cow (i:Axis): cows i (Resort (A.penumbra Z P b e q)) A.maxAge:=by change cows i ((hyphen 3 0 B₀) ∪ (B₀ ∪ ∅)) _; rw [union_empty]; exact A.broad_cows i
lemma shade_warm (t:20≤ A.rank): Attic.Huts A.rank (A.penumbra Z P b e q):=by
 let v:List (Cab N):=[π]; have h:Huts A.rank v:= fun i p x=> (hut_box (L₀) P.club_card _ i p x).growth t; exact (huts_mirror h 3 0).append h
lemma offerG: guest (A.penumbra Z P b e q)=reflMark 3 0 (π).frame * (π).frame:= by change _*(_*1)=_; rw [mul_one]; rfl
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms hemisphere
#print axioms umbra
#print axioms shade_warm
#print axioms offerG
#check @humid
