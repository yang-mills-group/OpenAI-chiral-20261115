import YM.SU5.Selected.Mainland
/-! # B (positive-time box, before projection) itself kills local color motion
(individual tested entries), not just the cap or the mean in the vacuum.
Cover costs unchanged. D intertwining with the coherent choice of physical
gauge function (Tapestry.GPhysical) extends every given prescription; prove
for any G here with no need for a Fashion identity. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Tapestry (Swatch render texture Circular GPhysical parentGauge restrictG)
open Set Theory
variable (S:Finset Cover)(s:ℕ)(R:Tapestry.GPhysical)
local notation "W₀"=>wingspan Λ l S
local notation "T" s:max=> Tapestry.restrictG Λ s R
include V in
lemma spendColors {f g:Family (tent Y H)} (p:InTest K true S false f)(t:InTest K true S false g)
    (c:Circular S (T s) f g): Circular (wingspan Λ l S) (T (s+1)) (G.refine s f) (G.refine s g):=by
  obtain ⟨F,rfl⟩:= Tapestry.rendered S K p; obtain ⟨F',rfl⟩:= Tapestry.rendered S K t
  have hk:Tendsto (i ∘ G.rows) atTop atTop:= (V.pick.grow_i.comp G.history.growsA).tendsto_atTop
  let P₀(n):=Tapestry.coupon Y H S s (i (G.rows n)) (k (G.columns n))
  let Q:= transfer Y H G S s
  have hc(x:Swatch S): Tendsto (fun n=>P₀ n x) atTop (𝓝 (Q x)):= Tapestry.cn_apply (X:=Swatch S) (Y:=Swatch (W₀)) (transfer_limit Y H V G S s) tendsto_const_nhds
  rw [transferred Y H G S s F,transferred Y H G S s F']
  rw [Tapestry.gaugeHarmony] at c
  apply Tapestry.continuousColor (tent Y H) (W₀) (T (s+1)) (hc F) (hc F'); filter_upwards [G.history.finance (s+1),hk.eventually (Tapestry.seasons Y H S s)] with n t v
  exact Tapestry.couponColor S (T (s+1)) Y H s _ _ F F' c ⟨⟨t.depth,t.enters⟩,v⟩
include V in
lemma framesOn (u:ℕ) {f g:Family (tent Y H)} (p:InTest K true S false f)(t:InTest K true S false g)(c:Circular S (T s) f g):
    Circular (volumeAround Λ l u S) (T (s+u)) (stream Y H G.refine s u f) (stream Y H G.refine s u g):=by
  induction u with
  | zero=> exact c
  | succ u h=> rw [stream_step,stream_step,←Nat.add_assoc]; exact spendColors Y H V G (volumeAround Λ l u S) (s+u) R (proceeds Y H G.history.circuit s u p).1 (proceeds Y H G.history.circuit s u t).1 h

private lemma disjoint_of_detached {S T₀:Finset Cover} (p:Detached Λ l S T₀) : Disjoint S T₀:=Finset.disjoint_left.mpr (fun {x} t e=>p x t x e (by rw [sub_self]; apply Lattice.box_test.mpr; constructor<;> intro i<;> change _ ≤ _ <;> simp only [Pi.zero_apply,neg_nonpos] <;> exact Nat.cast_nonneg _))
variable (w:ℕ)(hw:0<w)
local notation "ρ"=>ruler (tent Y H).B
include V C
lemma same_box_form (a b:Tower.Field Y H s j 0 strict)(f h:Entry Y H s j strict w)(p:InTest K true S false f.val.val) (t:InTest K true S false h.val.val)
    {R':Cover→ SU.E}(hS:Between K j 0 (ruler (tent Y H).B*w) S)(e:Circular S R' f.val.val h.val.val):
    inner ℂ ((κ s) b) ((B s f hw) ((κ s) a))=inner ℂ ((κ s) b) ((B s h hw) ((κ s) a)):=by
  obtain ⟨u,⟨a,rfl⟩⟩:=(field_entry Y H j strict s a).exists
  obtain ⟨v,⟨b,rfl⟩⟩:=(field_entry Y H j strict s b).exists -- shadow
  rw [snatch_equal,snatch_equal,stems Y H V,stems Y H V,SlabMark.area0]
  let P':= mirror K j 0 b.val.val
  obtain ⟨D,g,Bv⟩:= b.property; obtain ⟨U,v',u'⟩:= a.property
  have ht:= axial K j 0 g; let D':=reflectedBox j 0 D; let W':= plow K j w U
  let L:=relocate K j w a.val.val; have hu: InTest K true W' false L:= flow_port K j _ v'; have hv:= Between.relocate K j u' w -- order tune
  rw [add_zero] at hv
  have hP:Detached Λ l D' S:= mirror_detached Λ l (a:=j) (z:=0) (fun x v=> (Bv x v).1) (fun x v=>(hS x v).1)
  have hL:Detached Λ l S W':= cover_between K Λ l rfl j (fun i v=>(hS i v).2) (fun i v=>(hv i v).1)
  have hz:= ward_cancel Y H V s p t (((ht.mono (Finset.subset_union_left (s₂:=W'))).mul (hu.mono (Finset.subset_union_right (s₁:=D'))))) (by rw [Finset.disjoint_union_right]; exact ⟨(disjoint_of_detached hP).symm, disjoint_of_detached hL⟩) e
  simp_rw [slab_eq]; change E s (P'*(f.val.val*L))= E s (P'*(h.val.val*L))
  rw [even_tests K (aux_test p) (aux_test hu),even_tests K (aux_test t) (aux_test hu),←mul_assoc,←mul_assoc]; exact hz

lemma stance_color (f g:Entry Y H s j strict w)(p:InTest K true S false f.val.val)(t:InTest K true S false g.val.val) {R':Cover→ SU.E}
    (q:Between K j 0 (ruler Λ.block*w) S)(e:Circular S R' f.val.val g.val.val):
    B s f hw=B s g hw:=by
  obtain ⟨R,rfl⟩:= Tapestry.iceExtension Λ s R'
  apply test_high Y H V s G.history j strict C; intro u v a
  apply all_voices Y H G.history.circuit j 0 strict C; intro r b
  let m:=max u r; have hv:u≤ m:=le_max_left ..; have hm:r≤ m:=le_max_right ..
  let k:=m-s; have h':s≤ m:=v.trans hv
  have hy:Between K j 0 (ruler (tent Y H).B*(((Λ.R.L.val)^k*w:ℕ):ℤ)) (volumeAround Λ l k S):=by rw [Nat.cast_mul,Nat.cast_pow,mul_left_comm]; exact expands_shape Y H q k
  rw [←join_actor Y H V G.history.circuit j 0 strict C u m hv a,←join_actor Y H V G.history.circuit j 0 strict C r m hm b,refined_box Y H V s G.history G.clipped j strict C w f hw m h',refined_box Y H V s G.history G.clipped j strict C w g hw m h']
  exact same_box_form Y H V G j strict C (volumeAround Λ l k S) m _ _ _ _ _ _ (proceeds Y H G.history.circuit s k p).1 (proceeds Y H G.history.circuit s k t).1 hy (framesOn Y H V G S s R k p t e)
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.stance_color
