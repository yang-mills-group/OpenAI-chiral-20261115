import YM.SU5.Selected.PeakMotion
import YM.SU5.Selected.Clinic
/-! # One true *ALL-coordinates-separated* pair family. At the very same char.
Without mixing, meaning of RemoteSplit. Live even THAT measure. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 310000
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
variable (j : Axis) (C : Arena Y H Q.circuit j 0 false)
open Tapestry CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
variable {S : Finset Cover}
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "E'" => pigmentReading Y H V s Q Qt j C c
local notation "D₀" => indoor Y H V Q Qt j false C c
local notation "Χ" n:max => response Y H V n Q Qt j false C c

open SelectionAnalysis
lemma drives_shifted (z:Cover) (t:List Axis) (p:t.Nodup) (i: Cover)(h:i∈drivePlot z (tent Y H) t S): ∃ y∈ S,∀ l:Axis,i l=y l+ if l∈ t then ruler Λ.block*z l else 0:= by
 induction t generalizing i with
 | nil=> exact ⟨i,h,by simp⟩
 | cons v t ih=>
    obtain ⟨x,hx,rfl⟩:= plow_stays K v (z v) _ h
    obtain ⟨y,hy,e⟩:= ih (List.nodup_cons.mp p).2 x hx; refine ⟨y,hy,?_⟩; intro l
    rw [moves]; by_cases g:l=v; · subst l; rw [if_pos rfl,e,if_neg (List.nodup_cons.mp p).1,if_pos List.mem_cons_self,add_zero]; rfl
    simp [g,e]
lemma plots_shifted (z:Cover)(i:Cover)(h:i∈ streetBox (tent Y H) z S) (t:Axis):∃ y∈ S,i t=y t+ruler Λ.block*z t:= by
 obtain ⟨y,w,e⟩:=drives_shifted Y H z ordinate ordinate_one i h; exact ⟨y,w,(e t).trans (by rw [if_pos (ordinates t)])⟩
local notation "B"=> ruler Λ.block
local notation "Ω"=> doorstep Y H V Q Qt j false C c
local notation "P₀" v:max f:max=> relocateWorld Y H true v f
local notation "W" x:max=> mirrorInMarks Y H j true x
local notation "f∝" x:max=>show Marks K false from bosonLabel K x
local notation "V₁"=> turnstile Y H V Q Qt j false C c
variable {t : ℝ}
-- lower on all axes with margins u. Hush proof
lemma distant_true {X : Finset Cover} {k:Axis} {W₀: ℕ} (c : (W₀:ℝ)*gaugeMesh Λ s ≥ t) (d:0<t)
    (p:Tower.region k (W₀:ℤ) ((tent Y H).ℓ) S)(h:∀ i∈ X,i k+(K).ℓ≤ -(W₀:ℤ)) : PhysicalHush (Λ:=Λ) (l:=l) s k X S t:=by
 refine ⟨d,?_⟩; let w:= reserve Λ l; let P:=gaugePosition Λ; let U:=gaugeMesh Λ; intro i x v y h'
 obtain ⟨a,ha,g⟩:= physical_shield Λ l s X i v; obtain ⟨b,hb,u⟩:= physical_shield Λ l s S i h'; specialize g k; specialize u k
 have ht : (a k:ℝ)+(w:ℝ)≤ -(W₀:ℝ):= by exact_mod_cast h a ha; -- may need defeq
 have hz : (W₀:ℝ)+(w:ℝ)≤ (b k:ℝ):=by exact_mod_cast p b hb
 have h₁ : P s a k+(w:ℝ)*gaugeMesh Λ s≤ -t := by
    unfold P gaugePosition; rw [← add_mul]; exact (mul_le_mul_of_nonneg_right ht (gaugeMesh_pos ..).le).trans (by rw [neg_mul]; exact neg_le_neg c)
 have h₂ : t ≤ P s b k-(w:ℝ)*U s:= by unfold P gaugePosition U; rw [← _root_.sub_mul]; exact c.trans (mul_le_mul_of_nonneg_right (le_sub_iff_add_le.mpr hz) (gaugeMesh_pos ..).le)
 unfold P U w at *; linarith only [le_abs_self (gaugePosition Λ (s+i) x k-gaugePosition Λ s a k),g,u,neg_le_abs (gaugePosition Λ (s+i) y k-gaugePosition Λ s b k),d,h₁,h₂]
-- no raw separation before rotation assumed. after this purchase all four dimensions.
lemma placementVoy (S : Finset Cover) (K₀:ℕ) : ∃ (X : Cover)(n:ℕ),
    Tower.region j (K₀:ℤ) ((tent Y H).ℓ) (streetBox (tent Y H) X S) ∧ (∀ k:Axis, ∀ x∈ reflectedBox j 0 (streetBox (tent Y H) X S), x k+(K).ℓ ≤ -(K₀:ℤ)) ∧ ∀ f:Trans j→ℤ,(∀ i, (n:ℤ) ≤ f i)→∀ k:Axis,Tower.region k (K₀:ℤ) ((tent Y H).ℓ) (streetBox (tent Y H) (gaea j f+X) S):=by
 let u := S.sup (fun i=> Finset.univ.sup fun k:Axis=> (i k).natAbs); have ht {x:Cover}(p:x∈ S) (k:Axis) : |x k|≤ (u:ℤ):=by
    rw [← Int.natCast_natAbs]; exact_mod_cast le_trans (Finset.le_sup (f:=fun i:Axis=> (x i).natAbs) (Finset.mem_univ k)) (Finset.le_sup (f:=fun i:Cover=> Finset.univ.sup fun k:Axis=> (i k).natAbs) p)
 let n:= u+K₀+(K).ℓ; let X:Cover:=fun i=>if i=j then (n:ℤ) else -(n:ℤ); let S':=streetBox K X S; have hp:1≤ ruler Λ.block:=ruler_gene _
 have he:(n:ℤ)≤ B*n:=le_mul_of_one_le_left (by positivity) hp
 have hw : Tower.region j (K₀:ℤ) ((tent Y H).ℓ) S':=by
    intro i hi; obtain ⟨x,t,q⟩:= plots_shifted Y H X i hi j; rw [q,show X j=(n:ℤ) from if_pos rfl]
    have y:= neg_le_of_abs_le (ht t j); unfold n at *; omega
 refine ⟨X,2*n,hw,?_,?_⟩
 · intro k i v; obtain ⟨y,t,h⟩:= reflect_stays j 0 S' v; rw [h]
   by_cases s:k=j; · subst k; rw [if_pos rfl]; specialize hw y t; omega
   rw [if_neg s]; obtain ⟨x,t,q⟩:=plots_shifted Y H X y t k; rw [q, show X k= -(n:ℤ) from if_neg s, mul_neg]; have y:= le_of_abs_le (ht t k); unfold n at *; omega
 intro f g k i v; obtain ⟨x,t,q⟩:= plots_shifted Y H (gaea j f+X) i v k; have hy:= neg_le_of_abs_le (ht t k); rw [q,Pi.add_apply]
 suffices h:(n:ℤ)≤B * (gaea j f k+X k) by unfold n at *; omega
 refine he.trans (mul_le_mul_of_nonneg_left ?_ (by omega)); unfold gaea X; split
 next x=> simp [x]
 next v=> specialize g ⟨_,v⟩; omega

local notation "｟" x:max v:max "｠"=> streetBox (tent Y H) x v
local notation "X₀" x:max v:max=> reflectedBox j 0 (streetBox K x v)
local notation "Ξ"=> land Y H V s Q Qt j false C c -- unused
local notation "F" x:max=> arriving Y H V s Q Qt j false C c x
local notation "M" q:max x:max=>futureMark Y H s q false x
private lemma Fore (j : Axis) (f : Marks (tent Y H) false) (p : InTest K true S false f.val) (u : Tower.region j 0 ((tent Y H).ℓ) S) : ∃ x:Tower.Field Y H s j 0 false, f=futureMark Y H s j false x:= by
  exact ⟨(⟨_,(purpose_ok ..).mpr ⟨⟨_,p,by rw [area0]; exact u⟩,nofun⟩⟩ : Tower.Field Y H s j 0 false),rfl⟩
local notation "tw" p:max q:max f:max => ((mirrorInMarks Y H j true (P₀ p f))*(P₀ q f))
local notation "z₀" p:max => ChartCost K p
/-- Exact geometry cert. There exist common separated presentations across all axes with their
spatial continuum reading *on the compass*. -/
structure Ridge (V₀: Finset Cover) (p q : Cover) (f : observable (tent Y H) true) (z : SU.Slot)(o : Cover)(u d' : ℕ) (δ : ℝ) : Prop where
  span_positions : ∀ i:Axis,PhysicalHush (Λ:=Λ) (l:=l) s i (X₀ p V₀) (streetBox (tent Y H) q V₀) δ
  structured : Detached Λ l (X₀ p V₀) (streetBox (tent Y H) q V₀)
  whole_twin : (tw p q f).val=remotePair j K p q f.val f.val
  paid : ¬ RemoteSplit j K p q V₀ (booty o d' u) (Window.family z) (pigmentReading Y H V s Q Qt j C c)
  consumption : 1/32 ≤ ‖response Y H V s Q Qt j false C c (f∝ (tw p q f))‖
  zones : ∃ (x y : Tower.Field Y H s j 0 false),
    x.val=(relocateWorld Y H true p f).val ∧ y.val=(relocateWorld Y H true q f).val ∧
    (∀ (u : placement Λ), (∀ i:Axis,uptown i u) → scene Y H V s Q Qt j false C c x y (fun i=>(u i:ℝ))=Visits Y H V s Q Qt j false C c x y u) ∧
    ∀ (i:Axis)(Ci:Arena Y H Q.circuit i 0 false), i≠j → ∃ x' y':Tower.Field Y H s i 0 false,
        Duality Y H V s Q Qt j false C c Ci (displacement Y H V Q Qt j false C c i Ci) x y x' y'

lemma procured (p : Tower.region j 0 (K).ℓ (S)) (k : Finset Cover)(v:∀ i∈k,i j+(K).ℓ≤ 0) : Detached Λ l k S:=by
  let T:= reflectedBox j 0 k; have ht : Tower.region j 0 (K).ℓ T:=by
    intro i h; obtain ⟨y,q,h⟩ := reflect_stays j 0 k h; specialize v y q; rw [h,if_pos rfl]; omega
  have hh: reflectedBox j 0 T=k:=by
    ext i; unfold T reflectedBox; rw [Finset.image_image]; -- prove involution
    rw [show ((plane j 0).motion ∘ (plane j 0).motion)= id from ?_, Finset.image_id]
    -- lemma mirror
    funext x; change (plane j 0).motion ((plane j 0).motion x)=x; funext k; simp [fling_move]; split_ifs <;> simp_all
  rw [←hh]; exact mirror_detached _ _ ht p

variable (δ : ℝ) {o : Cover} {q' d' : ℕ}
lemma blankZero (x y : Tower.Field Y H s j 0 false) : Visits Y H V s Q Qt j false C c x y 0=inner ℂ (bud Y H V s Q Qt j false C c x) (bud Y H V s Q Qt j false C c y):= by
  unfold Visits atEstate; simp only [Pi.zero_apply,AddSubgroup.coe_zero, Real.toNNReal_zero]; rw [(ride Y H V Q Qt j false C c).eZero,show (fun _ : Trans j=> (0:marks (timeMesh Λ)))=0 from rfl,Germ.Alliance.raw_zero (V₁) (look j)]; rfl
lemma high_paired (V₀ : Finset Cover) (z:SU.Slot)(f: Marks (tent Y H) true)(w: Survivor Y H V s Q Qt j C z o q' d' V₀ f c)(d0:0<δ): ∃ (p q:Cover), Ridge Y H V s Q Qt j C c V₀ p q f z o q' d' δ:=by
 obtain ⟨r,hU⟩:= exists_nat_gt (δ/gaugeMesh Λ s); have hr:= ((div_lt_iff₀ (gaugeMesh_pos ..)).mp hU).le
 obtain ⟨p,n,H₀,hpOld,hv⟩:= placementVoy Y H j V₀ r
 let v : Marks K false:= f∝ (P₀ p f); have hx:= world_val Y H true p (show Marks K true from f)
 have h(x): x∈ streetBox K p V₀ → 0+(K).ℓ≤ x j:=fun q=> le_trans (by omega) (H₀ x q)
 have H' : InTest K true V₀ false f.val:= (FilTest w.link.mark_mem).widen
 have he(v : Cover): InTest K true (streetBox K v V₀) false (P₀ v f).val:=by rw [world_val]; exact cad_test v _ H'
 obtain ⟨x,eq⟩:= Fore Y H s j v (he p) h
 have hm:1/4 ≤ ‖inner ℂ Ω (F x)‖:=by
    unfold arriving; change _≤ ‖inner ℂ (doorstep ..) (bud Y H V s Q Qt j false C c x)‖; rw [call,← eq];
    have hv:v= relocateWorld Y H false p (f∝ f):=Subtype.ext (by change (P₀ p f).val=(relocateWorld Y H false p _).val; rw [world_val,world_val]; rfl)
    rw [hv,world_still]; exact w.responds
 obtain ⟨u,g,v'⟩:= peek (look j) (timeMesh Λ) (V₁) (F x) Ω (1/32) (by norm_num) (look_one _) (fun i u=> jamb ..) (ready ..) (by nlinarith only [hm]) s (fun _=>n)
 let q:=gaea j u+p
 let y:=transport Y H s j false (look j) u x
 have hy : (M j y)=(f∝ (P₀ q f)):=by
    apply Subtype.ext; rw [future_val]; unfold y; rw [transverseT Y H V s Q j false C,show x.val=(P₀ p f).val from congrArg Subtype.val eq.symm,hx]; change _=(P₀ q f).val; rw [world_val]; refine Eq.trans ?_ (cad_plus _ _ (marksSpec true (show Marks K true from f)).1 _ _); symm; change Vacancy.chart K _ _= _; rw [chart_piece]; -- mismatch chart after plus not syntactic
    next => rw [gaea,dif_pos rfl]; apply relocate_zero; exact cad_paid K _ (cad_paid K _ (marksSpec true (show Marks K true from f)).1 _) _
    exact cad_paid K _ (marksSpec true (show Marks K true from f)).1 _
 have h0 : Visits Y H V s Q Qt j false C c x y 0=response Y H V s Q Qt j false C c (f∝ (tw p q f)):=by
    rw [blankZero,earns,←eq,hy]; rfl
 have Hz:1/32≤ ‖response Y H V s Q Qt j false C c (f∝ (tw p q f))‖:=by
    rw [←h0,blankZero]; refine le_of_lt (v'.trans_eq ?_)
    change ‖inner ℂ (bud Y H V s Q Qt j false C c x) ((V₁).raw (look j) (fun i=> notch (timeMesh Λ) s (u i)) (bud Y H V s Q Qt j false C c x))‖=_; rw [roving Y H V s Q Qt j false C c (look j) x u]
 let t:=X₀ p V₀; have he₁ := procured Y H (S:=streetBox K q V₀) j (fun i u=> le_trans (by omega) (hv _ g _ i u)) t (fun i h=>(hpOld j i h).trans (neg_nonpos.mpr (by positivity)))
 have h₂ : (tw p q f).val= _:= (show (tw p q f).val=remotePair j K p q f.val f.val from (by change mirror _ _ _ _*_=_; rw [world_val Y H true p,world_val Y H true q]; rfl))
 have hp(i: Axis)(k:Arena Y H Q.circuit i 0 false)(hk:i≠ j) : ∃ (x' y':Tower.Field Y H s i 0 false),Duality Y H V s Q Qt j false C c k (displacement Y H V Q Qt j false C c i k) x y x' y':=by
    let C₁:= mirrorInMarks Y H j false v; let P:=mirrorInMarks Y H i false C₁
    let Z:= streetBox K q V₀; obtain ⟨y',pY⟩ := Fore Y H s i (M j y) (hy.symm ▸ he q) -- insert defeq hp proof
        (fun x s=> le_trans (by omega) (hv _ g i x s))
    have ht : InTest K true t false C₁.val := axial K j 0 (he p)
    have hf': Tower.region i 0 (K).ℓ (reflectedBox i 0 t):=by
       intro z h; obtain ⟨a,h₃,h'⟩:=reflect_stays i 0 t h; specialize hpOld i a h₃; rw [h',if_pos rfl]; omega
    obtain ⟨x',pX⟩:= Fore Y H s i P (axial K i 0 ht) hf'
    refine ⟨x',y',fun i' s=> (across_response Y H V s Q Qt j false C c i' i k).symm, ?_, congrArg Subtype.val pY⟩
    have hh:x'.val=P.val:= congrArg Subtype.val pX.symm; have hx:x.val=v.val:= congrArg Subtype.val eq.symm; rw [hh,hx, show mirror K i 0 P.val = mirror K j 0 v.val from mirror_invert K i 0 (aux_test ht)]
 refine ⟨p,q,(fun i=> distant_true Y H s hr d0 (hv u g i) (hpOld i)),he₁,h₂,?_,Hz,x,y,congrArg Subtype.val eq.symm,congrArg Subtype.val hy,fun u h=> scene_revival Y H V s Q Qt j false C c x y ?_ u h,hp⟩ -- hpOld
 · intro a; let Fa:= pigmentReading Y H V s Q Qt j C c; have ht : Fa (tw p q f).val=0 := h₂.symm ▸ remotePair_price Y H V s Q Qt j C c p q (detached_disjoint he₁) w.link.anchor_inj a w.link.mark_mem w.link.mark_mem
   have hv:= ((reads_color Y H V s Q Qt j C c (show Marks K false from bosonLabel K (tw p q f))).symm.trans ht)
   have ht := Hz.trans_eq ((congrArg norm (show response Y H V s Q Qt j false C c (f∝ (tw p q f))=0 from hv)).trans norm_zero)
   norm_num at ht
 intro k i; let P:=Classical.choice (voyage_H Y H V Q.circuit k 0 false); exact ⟨P,_, hp k P i⟩
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.placementVoy

#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.high_paired
