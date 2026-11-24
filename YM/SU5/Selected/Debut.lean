import YM.SU5.Selected.Elevation
import YM.SU5.Selected.Reserved
/-! # Double protocol debuts together on ONE next-sized host, carry the costs.
FixedLink and ensemble-uniform first prices (on the ground!) including both versions
before taking any character. Then L2 estimates transferable. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 400000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (C : Arena Y H Q.circuit 0 0 false)
open Tapestry _root_.YM.SelectionAnalysis CF.Pannier.Chancel
variable (S : Finset Cover)
local notation "𝔄" => Ark.Ht Y H Q.circuit 0 0 false C
local notation "ℛ" => Aurora Y H V Q 0 false C
local notation "R₀" => groundRoom Y H V Q 0 false C
local notation "𝔅" => driveAlgebra Y H V Q Qt 0 false C
local notation "A" => displayAlgebra Y H V Q Qt 0 false C
local notation "ω₀" => floorV Y H Q.circuit 0 0 false C
local notation "π" => (ℛ).orthogonalProjectionOnto
local notation "Ω₀" => seat0 Y H V Q 0 false C
local notation "qv" s:max i:max x:max => entrance Y H V s Q Qt 0 false C i x
local notation "P₁" t:max => actor Y H t Q.circuit 0 0 false C
local notation "σ" => ruler Λ.block
local notation "Ρ" x:max => indoor Y H V Q Qt 0 false C x
local notation "κ₀" f:max t:max x:max => bud Y H V t Q Qt 0 false C f x

variable {q d w : ℕ} {R A' : ℝ} (z : SU.Slot)
local notation "B" => payout d q w
local notation "G" => grain B
local notation "Z" => Sen G B
local notation "φ" x:max => located Y H V s Q Qt 0 false C x

-- the Work received at that positive stencil, on the VERY same selected cap after averaging.
private lemma carry_price {S : Finset Cover}
    (u f : Marks (tent Y H) false) (v : InTest K true S false u.val) (p : InTest K true S false f.val)
    (n : ℕ) (h : Hosp S ((tent Y H).c (momentm Y n s)))
    (t : exhibit Y H s n u.val = molasses (exhibit Y H s n f.val)) (e : Continuous (exhibit Y H s n f.val)) :
    φ u = φ f := by
  let m := momentm Y n s
  obtain ⟨x,hx⟩ := rendered S (tent Y H) p; obtain ⟨y,hy⟩ := rendered S (tent Y H) v
  rw [←hx] at t e; rw [←hy] at t
  have ht := terrain Y H (Y.ir n) s
  have hr : render S K y m=molasses (render S K x m) ∧ Continuous (render S K x m) := by exact acrossS (N:=(tent Y H).c m) ht _ _ t e
  have he := coup_smooth_price S m K h x hr.2
  have Hv : y=sigil S m K x := Tapestry.appear_inj S K m h (hr.1.trans (sigil_pour S m K h x he).symm)
  rw [show f=labelL Y H S x from Subtype.ext hx.symm, show u=labelL Y H S y from Subtype.ext hy.symm,Hv,registered Y H V s Q Qt 0 C S x m he]
where
 acrossS {N T : Side} (h : N=T) (u f : Mark N) (p : Tapestry.arrange N T h u=molasses (arrange N T h f)) (q : Continuous (arrange N T h f)) : u=molasses f ∧ Continuous f := by subst T; exact ⟨p,q⟩

private lemma forecasts_grain {f : Marks K false} (p : InTest K true (Sen (grain B) B) false f.val)
    (k : addgap (tent Y H)≤ payout d q w) : ∃ x : Tower.Field Y H s 0 0 false, f=actorLabel Y H s 0 false x := by
  have hv : Between K 0 0 (12*(B:ℤ)) (Sen (grain B) B) := between_grain k _ _ (le_refl _)
  exact ⟨(⟨f.val,(purpose_ok ..).mpr ⟨⟨(Sen (grain B) B),p,by intro i hi; rw [area0]; exact (hv i hi).1⟩,nofun⟩⟩ : Tower.Field Y H s 0 0 false), rfl⟩
structure Worthy (z : SU.Slot) (q d w : ℕ) (F : observable (tent Y H) true) : Prop where
  indeed : FixedLink Y H V s Q Qt z (grain (payout d q w)) q d (Sen (grain (payout d q w)) (payout d q w)) F
  price : ‖(located Y H V s Q Qt 0 false C (1+(show Marks (tent Y H) false from bosonLabel (tent Y H) F))).val (seat0 Y H V Q 0 false C)‖^2≤ 1/2048 -- instance/coercion problem type

lemma covalues (g : Papal.Korn Y H q d w R A') : ∀ᶠ s in atTop, ∀ z : SU.Slot,
    ∃ F : observable (tent Y H) true, Worthy Y H V s Q Qt C z q d w F:=by
  have hR:= g.heap
  let o := grain B; let Z':=Sen o B; let T:= reflectedBox 0 0 Z'∪ Z'
  let D':= R+1+R*R; have hD : 0<D':=by unfold D'; positivity
  let v:=(1/8192)/D'; have hv:0<v:=by unfold v; positivity
  filter_upwards [g.here,g.pairs] with s p h z
  obtain ⟨u1,u2⟩:= Satin.boutique Y H V T s
  let g1:= V.pick.grow_i.tendsto_atTop
  obtain ⟨n, hx, H₁, hp, hr⟩:=
    ((u2 v hv).and ((g1.eventually ((p o).and h)).and ((g1.eventually u1).and (g1.eventually (roomyTail Y H s T))))).exists -- H₁ is and eventually and
  obtain ⟨t,⟨f₀,h'⟩,sU⟩:= ((V.pick.grow_k.tendsto_atTop.eventually (H₁.1.and H₁.2)).and (hp v hv)).exists -- H₁ probably event of ∀ ... and; check obtain pattern
  obtain ⟨g',lX,φE,X,a₀,x₀,F,ζ,hF,hEq,hVal⟩:= f₀ z
  obtain ⟨fQ,f,hf,he⟩:= h' z
  let y : observable (tent Y H) true := ⟨F, aux_test ((FilTest ζ).widen), fun _=> hF⟩
  let m:= momentm Y (i n) s
  let x:=Papal.taggin Y s (i n) (k t) q d w o z
  have ht := terrain Y H (Y.ir (i n)) s
  have Hz : Hosp Z' ((tent Y H).c m):=ht.symm ▸ Roomy.seats g'
  have h : Hosp T ((tent Y H).c m):=ht.symm ▸ Roomy.seats hr
  have Hl : ∀ f:Family K, InTest K true T false f→(∀ x, ‖exhibit Y H s (i n) f x‖≤D')→‖sharp Y H s (i n) (k t) f-E s f‖≤ 1/4096 := by
    intro f g r; have hv := (displayPositive ht D' (f m)).mpr r; have h1:= sU f g m h D' hv; have h2:= (hx f g m h D' hv).1
    have he: v*D'=1/8192:=div_mul_cancel₀ _ hD.ne'; rw [he] at h1 h2
    exact (norm_sub_le_norm_sub_add_norm_sub _ (I s f (i n)) (E s f)).trans (by linarith only [h1,h2])
  have ht0 := (FilTest ζ).widen; have ht1 := (FilTest hf).widen
  have h₀:= Hl F (ht0.mono subset_union_right) (fun a=>by rw [hEq]; exact (x₀ a).trans (by unfold D'; nlinarith only [sq_nonneg R]))
  have hh : 1/4≤ ‖E s F‖:= by linarith only [hVal,h₀,norm_sub_norm_le (sharp Y H s (i n) (k t) F) (E s F)]
  refine ⟨y,freeze Y H V s Q Qt y _ (g.cents _) (Papal.stake_centers Y H _ _ _ _) ζ hh,?_⟩
  let X₁ := (show Marks K false from bosonLabel K y)
  let X₀ : Marks K false := ⟨f, aux_test ht1,nofun⟩
  let f₂ := (X₀+1)
  have Hx : exhibit Y H s (i n) f₂.val=x.frame:=by
    change exhibit Y H s (i n) (f+1)=_; rw [actual_add, he,actual_one,sub_add_cancel]
  have hcou : located Y H V s Q Qt 0 false C X₁=located Y H V s Q Qt 0 false C X₀:=by
    apply carry_price Y H V s Q Qt C X₁ X₀ (S:=Z') ht0 ht1 (i n) Hz
    · change exhibit Y H s (i n) F= molasses (exhibit Y H s (i n) f); rw [hEq, he]
    change Continuous (exhibit Y H s (i n) f); rw [he]; exact (feastReady ..).sub continuous_const
  have hN : InTest K true Z' false f₂.val:= ht1.add InTest.one
  let θ:= mirror K 0 0 f₂.val * f₂.val
  have hθ : InTest K true T false θ:= ((axial K 0 0 hN).mono subset_union_left).mul (hN.mono subset_union_right)
  have hy : exhibit Y H s (i n) θ = reflMark 0 0 x.frame*x.frame:=by
     unfold θ; rw [actual_product, show exhibit Y H s (i n) (mirror K 0 0 f₂.val)=reflMark 0 0 (exhibit Y H s (i n) f₂.val) from (displayRef ht 0 0 (f₂.val m)),Hx]
  have hU : ‖sharp Y H s (i n) (k t) θ-E s θ‖≤ 1/4096:= Hl θ hθ (fun u=>by rw [hy]; refine ((norm_mul_le ..).trans (mul_le_mul (Papal.pairPrice (show ∀ v, ‖x.frame v‖ ≤ R from X) 0 _) (show ‖x.frame u‖ ≤ R from X u) (norm_nonneg _) hR.le)).trans ?_; unfold D'; linarith)
  have hq : ‖sharp Y H s (i n) (k t) θ‖≤ 1/4096:=by rw [actualRead,hy]; exact fQ
  have hy : ‖E s θ‖ ≤ 1/2048:= (norm_le_norm_sub_add _ (sharp Y H s (i n) (k t) θ)).trans (by rw [norm_sub_rev]; linarith)
  obtain ⟨y',H'⟩:=forecasts_grain Y H s hN g.limit; let Vx:= actor Y H s Q.circuit 0 0 false C y'
  have heq : ‖Vx‖^2=‖E s θ‖:=by
    unfold θ; rw [H']; change _= ‖E s (mirror K 0 0 y'.val*y'.val)‖
    rw [show E s (mirror K 0 0 y'.val*y'.val)=inner ℂ Vx Vx from (by symm; unfold Vx; rw [stems Y H V,area0])]
    rw [inner_self_eq_norm_sq_to_K]; change _=‖((‖Vx‖:ℂ)^2)‖; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  change ‖(located Y H V s Q Qt 0 false C (1+X₁)).val Ω₀‖^2 ≤ _
  rw [add_comm,map_add,hcou,← map_add]; change ‖cap Y H V s Q Qt 0 false C f₂ Ω₀‖^2≤ _; rw [H',cap_plant]
  exact (pow_le_pow_left₀ (norm_nonneg _) ((ℛ).norm_orthogonalProjectionOnto_apply_le Vx) _).trans (heq.trans_le hy)
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.covalues
