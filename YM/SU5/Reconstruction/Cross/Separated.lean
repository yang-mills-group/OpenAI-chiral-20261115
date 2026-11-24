import YM.SU5.Reconstruction.DocketPrice
import YM.SU5.Reconstruction.Cross.Acquisition
import YM.SU5.Reconstruction.Cross.Passage
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
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  {D : ℕ→Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
  (s : ℕ) (j : Axis) (C : Arena Y H Q.circuit j 0 false) -- aim all even incl characters extension
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "𝔄" => driveAlgebra Y H V Q Qt j false C
local notation "ρ" => indoor Y H V Q Qt j false C c
local notation "Ρ" => procession Y H V Q Qt j false C c
local notation "Ω" => doorstep Y H V Q Qt j false C c
local notation "Eχ" s:max => Selected.response Y H V s Q Qt j false C c
local notation "Ex" => ride Y H V Q Qt j false C c
local notation "Φ" t:max => Tower.Field Y H t j 0 false
local notation "T" n:max => Selected.bud Y H V n Q Qt j false C c
/- *Already* on one fixed stencil at the acquired s, one same support ψ for cost and calibration.
Extend through higher common charts (if t>s needed to resolve the gap), use CPB's full compact method.
This makes the Exceeds open on common continuum chart incl for prices on ANY time axis (earlier i & j
purchases kept Exceeds per j due space-continuity issue, not one common formulation). Not
claiming those real kernels local. Θ formulation applies through M1 pins. Spacetime here for width
windows only! Γ shifts preserve shifted stamps. The positive-size claimed region width δ
is Euclidean separation of TWO copies of the already interaction probe; potentially tinier when
wiggled but still positive. Not a shrinking UV test.
-/
open _root_.YM.SelectionAnalysis Vacancy.Average
variable {X Y' : Set RSpace}
private lemma two_family (j:Axis) (hX:IsCompact X) (hY:IsCompact Y') (p : ∀ x∈ X, ∀ y∈Y', x j < y j) : ∃ a b c:ℝ, a<b∧ b<c ∧ (∀ x∈X,x j∈ Ioo a b) ∧ ∀ x∈Y',x j∈ Ioo b c:=by
 let f(x:RSpace):ℝ:=x j; have h:Continuous f:=continuous_apply j
 obtain ⟨u,xu⟩:= hY.bddAbove_image h.continuousOn
 obtain ⟨v,xv⟩:= hX.bddBelow_image h.continuousOn
 have hz(b:ℝ)(a:∀ x∈X,x j<b)(c:∀ x∈Y',b<x j) : ∃ m n k:ℝ,m<n∧ n<k∧(∀ x∈X,x j∈ Ioo m n)∧∀ x∈Y',x j∈ Ioo n k:=by
    obtain ⟨m,hx,hy⟩:= exists_lt (min v b) |>.imp (fun c h=> (by simpa using h)) -- produce ∃ m, m<v ∧ m<b
    obtain ⟨k,hk⟩:= exists_gt (max u b)
    exact ⟨m,b,k,hy,(le_max_right ..).trans_lt hk,fun x h=> ⟨hx.trans_le (xv (Set.mem_image_of_mem f h)), a x h⟩,fun x h=> ⟨c x h,(le_trans (xu (Set.mem_image_of_mem f h)) (le_max_left ..)).trans_lt hk⟩⟩
 rcases Y'.eq_empty_or_nonempty with y|y
 · obtain ⟨k,hk⟩ := hX.bddAbove_image h.continuousOn
   exact hz (k+1) (fun x h=> lt_of_le_of_lt (hk (Set.mem_image_of_mem f h)) (lt_add_one _)) (by rw [y]; simp)
 obtain ⟨b,hb,u⟩:= hY.exists_isMinOn y h.continuousOn
 rcases X.eq_empty_or_nonempty with x|x
 · exact hz ((b j)-1) (by rw [x]; simp) (fun k hk=> lt_of_lt_of_le (sub_one_lt _) (u hk))
 obtain ⟨a,ha,c⟩:= hX.exists_isMaxOn x h.continuousOn
 obtain ⟨t,hp,ht⟩:= exists_between (p a ha b hb)
 exact hz t (fun x p=> lt_of_le_of_lt (c p) hp) (fun y z=> ht.trans_le (u z))

-- true and false index; chosen mark f with support S₁ false (first-copy) and S₂ true ..
variable (S : Bool → Finset Cover) (F : Bool → Marks (tent Y H) false)
local notation "Θ" => Marks (tent Y H) false
local notation "L" => [false,true]
local notation "Λ₀" => timeMesh Λ
local notation "Z" t:max=> fun i:Bool=> upGrade Y H s Q false (F i) t
local notation "U" x:max=> silhouette Λ l s (S x)
variable {δ : ℝ} (p:0<δ)(hS:∀ q,InTest (tent Y H) true (S q) false (F q).val) (e:∀ i:Axis, ∀ x∈silhouette Λ l s (S false),∀ y∈silhouette Λ l s (S true),x i+δ ≤ y i)
include hS e p in
lemma tickets_axis (a₀:Axis) : ∀ᶠ t in atTop, ∃ (g:∀ x:Bool,Gate Y H t a₀ (upGrade Y H s Q false (F x) t)) (m:ℤ), Leaves Y H t a₀ (Z t) g m [false,true] ∧ ∀ x,(g x).within_ 0 ∧ ∀ u∈ silhouette Λ l s (S x),u a₀∈ Set.Icc (bell Μ t (g x).base) (bell Μ t ((g x).base+(g x).width)):=by
 obtain ⟨a,b,z,v,w,hx,hy⟩:= two_family a₀ (silhouette_compact Λ l s (S false)) (silhouette_compact Λ l s (S true)) (fun x w y h=> by linarith [e a₀ x w y h])
 let u : Bool→ℝ:= fun i=> if i then b else a; let t : Bool→ℝ:=fun i=> if i then z else b
 let T':= L; have h:books u t a T' := books.next (i:=false) rfl (books.next (i:=true) rfl (.blank _)) -- tune
 let m(x:Bool):Axis→ℝ:=0
 have ht : ∀ i:Bool,u i < t i ∧ ∀ x∈ U i,u i < m i a₀+x a₀ ∧ m i a₀+x a₀ < t i:=by
    intro i; cases i; · simpa [m,u,t,v] using (show ∀ x∈ U false,a < x a₀∧x a₀<b from hx)
    simpa [m,u,t,w] using (show ∀ x∈ U true,b<x a₀ ∧ x a₀<z from hy)
 filter_upwards [stretching Y H Q s a₀ F S T' ht h hS] with t x
 obtain ⟨v,h,g⟩:=x; exact ⟨v,_,h,g⟩
include hS in
lemma price_cover_zero (t:ℕ)(p:s ≤ t) (h : Detached Λ l (S false) (S true)) :
    (Eχ t) (orderWord Y H Q s F t [false,true] 0) = (Eχ s) ((F false)*(F true)):=by -- notation tune
 have hg: (orderWord Y H Q s F t [false,true] 0)=upGrade Y H s Q false (F false*F true) t:=by
    apply Subtype.ext; unfold orderWord; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,Pi.zero_apply,Selected.world_seed] -- maybe Subtype defs
    exact (woven_product Y H Q.circuit s _ (hS false) (hS true) h).symm
 rw [hg]; obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le p
 unfold upGrade; rw [show s+k-s=k by omega]; exact moves_up ..

-- preserve difference measure and support even when looking inside chosen real nbhd. h_s moved all k axes.
local notation "S'"=> Bool→ Axis→ℝ
local notation "θ"=> Bool→ ℝ
local notation "T'"=> Bool→ seeMesh Μ
variable (P : ∀ j:Axis, Arena Y H Q.circuit j 0 false)
local notation "C₁" k:max=> Selected.displacement Y H V Q Qt j false C c k (P k)
local notation "Ψ" t:max k:max=> electedAtlas Y H V Q Qt t k (P k) (C₁ k)
local notation "ζ" v:max=> gridChart Μ v
local notation "Π₄"=> commonR Y H V Q Qt s j C c F [false,true] P
local notation "f₀"=> F false*F true
local notation "Πw"=> (Eχ s) (F false* F true)
lemma grid_blank (Λ:Preparation) (t:ℕ) : grid (timeMesh Λ) t ∘ (0:Bool→ Cover)=(0:Bool→seeMesh (timeMesh Λ)):=funext fun i=> funext fun j=>notch_zero ..
-- scene window, *actual* sharp contact rules as before on these stencil mark. May send ANY t high.
include hS e p
lemma priced_opens (k:ℝ) (B:k< ‖Selected.response Y H V s Q Qt j false C c (F false* F true)‖) (q : Detached Λ l (S false) (S true)) :
   ∀ᶠ t in atTop,∃ (g:∀ i:Axis,∀ x:Bool,Gate Y H t i (upGrade Y H s Q false (F x) t)) (X:Set (Bool→Axis→ℝ)),
     Π₄ 0=Πw ∧ X∈𝓝 (0 : Bool → Axis→ℝ) ∧ X⊆ arenaRegion Y H Q s F [false,true] ∧ IsOpen X ∧
     -- keep spatial support
     (∀ w∈X,∀ x∈ U false,∀ y∈ U true,∀ i,x i+w false i+δ/2 ≤ y i+w true i) ∧
     (∀ w∈X,k< ‖Π₄ w‖) ∧
     (∀ i:Axis, (∃ lo:ℤ, Leaves Y H t i (Z t) (g i) lo [false,true]) ∧ (∀ w∈X,(∀ x,(g i x).within_ (w x)) ∧ Π₄ w=(Ψ t i) (Z t) (g i) L w) ∧ ∀ v:Bool→seeMesh Μ, ζ v∈X→ Π₄ (ζ v) =rawTrace Y H V Q Qt t i (P i) (C₁ i) (Z t) (g i) [false,true] v) ∧
     -- carry positive-width contour price to real times in that axis (with shifts). cost at EACH axis simultaneously, true Mink cigar, not point field.
     ∀ᶠ w : (Bool→Axis→ℝ)×(Bool→ℝ) in 𝓝 (0,0),w.1∈X ∧ ∀ i:Axis,k<‖edgeArrival Y H V Q Qt t i (P i) (C₁ i) (Z t) (g i) [false,true] w‖:=by
  filter_upwards [eventually_ge_atTop s, eventually_all.mpr (tickets_axis Y H Q s S F p hS e)] with t pt ht
  choose g m h0 h using ht; let W : List Bool:=[false,true]; have hx : W.Nodup:=by simp [W]
  let A(i:Axis):= (⟨t,pt,g i,W,List.Perm.refl W,m i,h0 i⟩ : AcceptFrom Y H Q s i F W)
  let E₀ : Set (Bool→Axis→ℝ) := ⋂ i:Axis,(A i).domain
  have hx':(0:S')∈E₀:= Set.mem_iInter.mpr (fun i q _=>(h i q).1)
  have body (i:Axis) (v:S') (p:v∈E₀) : Π₄ v= (Ψ t i) (Z t) (g i) W v:= enters_common Y H V Q Qt s j C c F W P hx (A i) v (Set.mem_iInter.mp p i)
  have throughout (i:Axis) (v:S') (p:v∈ E₀) (x:Bool): (g i x).within_ (v x) := (show ∀ x∈ W,(g i x).within_ (v x) from Set.mem_iInter.mp p i) x (by cases x<;>simp [W])
  have linked (i:Axis)(v : T') (p:ζ v∈ E₀) : Π₄ (ζ v)=rawTrace Y H V Q Qt t i (P i) (C₁ i) (Z t) (g i) W v :=by
    rw [body i (ζ v) p]; exact (recovers Y H V Q Qt t i (P i) (C₁ i) _ _ (h0 i) hx v P (fun a _=> throughout i _ p _) (fun i=> ⟨W,m i,g i,h0 i,List.Perm.refl W, fun a _=> throughout i _ p _⟩)).symm
  have he:Π₄ 0=Πw:=by
    have hv:ζ (0:T')= (0 : Bool→ Axis→ℝ):= rfl
    rw [← hv,linked j 0 (hv.symm ▸ hx')]; rw [← grid_blank Λ t, train_lattice Y H V Q Qt t j (P j) (C₁ j) _ _ t le_rfl 0 _ _ (h0 j), ← keyPath Y H Q s F t t pt le_rfl,across_response Y H V t,price_cover_zero Y H V Q Qt s j C c S F hS t pt q]
    rw [← grid_blank Λ t] at hv; exact fun i p=> (g j i).allows (throughout j _ (hv.symm ▸ hx') i) -- not tune
  let allowance(i:Axis): Set (Bool→Axis→ℝ):= {v|v false i - v true i < δ/2}
  let R:= ⋂ i:Axis,allowance i; have O: IsOpen R:= isOpen_iInter_of_finite (fun i=> isOpen_lt (show Continuous (fun x:Bool→Axis→ℝ=> x false i - x true i) from by fun_prop) continuous_const)
  have hR:(0:S')∈R:= Set.mem_iInter.mpr fun i=> (show (0:ℝ)-0 < δ/2 by linarith)
  let U₀:Set (Bool→Axis→ℝ) := R ∩ E₀ ∩ {v| k < ‖(Ψ t j) (Z t) (g j) W v‖}; have hc:= body j _ hx'; have hB0:k< ‖Π₄ 0‖:= he.symm ▸ B
  have hp:IsOpen U₀ := (O.inter (isOpen_iInter_of_finite (fun i=> (A i).isOpen))).inter (isOpen_lt continuous_const ((electedAtlas_continuous Y H V Q Qt t j (P j) (C₁ j) _ _ _).norm))
  have hg:(0:S')∈U₀:= ⟨⟨hR,hx'⟩,hB0.trans_eq (congrArg norm hc)⟩
  refine ⟨g,U₀,he,hp.mem_nhds hg,fun x (z:x∈U₀)=> in_chart Y H Q s j F W (A j) (Set.mem_iInter.mp z.1.2 j),hp,fun w (z:w∈U₀) x u y t i=> ?_,fun w (z:w∈U₀)=> (body j w z.1.2).symm ▸ z.2,fun i=>⟨⟨m i,h0 i⟩,fun w (z:w∈U₀)=>⟨throughout i w z.1.2,body i w z.1.2⟩,fun v (z:ζ v∈U₀)=> linked i v z.1.2⟩,?_⟩
  · have ht := e i x u y t; have hv:w false i-w true i < δ/2 := Set.mem_iInter.mp z.1.1 i; linarith
  apply Filter.Eventually.and (show ∀ᶠ w : (Bool→Axis→ℝ)×(Bool→ℝ) in 𝓝 (0,0),w.1∈U₀ from (continuous_fst.tendsto (x:=( (0:S'), (0:Bool→ℝ)))).eventually (show ∀ᶠ x in 𝓝 (0:S'), x∈U₀ from hp.mem_nhds hg))
  refine eventually_all.mpr fun i=> ((edge_cont Y H V Q Qt t i (P i) (C₁ i) (Z t) (g i) L).norm.tendsto (0,0)).eventually (lt_mem_nhds ?_)
  change _< ‖arrived Y H V Q Qt t i _ _ _ _ _ _ _‖
  rw [Mink_empty, ← body i (0:S') hx']; exact hB0
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.priced_opens
