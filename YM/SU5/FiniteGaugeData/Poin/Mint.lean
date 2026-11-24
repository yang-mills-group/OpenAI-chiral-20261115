import YM.SU5.FiniteGaugeData.Poin.Starley
import YM.Shift.Cut
/-!
# Spatial locality patches for regular-bought field word-domain operators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set Mink Mink.General Mink.Lorentz MeasureTheory Boundary Probe Metric Submodule
open scoped Topology ContDiff NNReal InnerProductSpace ComplexOrder
local notation "tt"=>timeAxis
variable (x y:E4)(g h:Test4)
namespace Mint
open Real Distribution
section cut
variable (f:Test4→ Distn E4)(F: Test4→ Distn E4)(z:Set (E4× E4)) (p:∀ g h,f g h= F h g)
structure Patch :Prop where
 d(x y:E4)(e:(x,y)∈z): ∃ A B:Set E4, IsOpen A∧x∈A∧ IsOpen B∧ y∈B ∧ ∀ g:Test4,tsupport g⊆A→∀ h:Test4, tsupport h ⊆ B→ f g h=0
-- Distribution tube uniform P
variable (k: Patch f z)(hv:tsupport g ×ˢ tsupport h⊆z)
private lemma van(f:Distn E4): IsVanishingOn f (dsupport f)ᶜ := (Distn.general_open _ isClosed_dsupport.isOpen_compl).2 disjoint_compl_left
include p k hv
lemma disperse : f g h=0:=by
 suffices he: ∀ h:Test4,tsupport g ×ˢ tsupport h⊆ z→HasCompactSupport (h:E4→ℂ)→ f g h=0 by
    refine tendsto_nhds_unique (( (f g).continuous.tendsto h).comp (persistent h)) ?_; apply tendsto_const_nhds.congr'; filter_upwards with i; exact (he _ ((prod_mono (_root_.subset_refl _) (cap_support i)).trans hv) (finite_cap i)).symm
 intro h z' h'; rw [p]; apply van; -- goal support g subset comp. assembly
 intro x g'; apply (notMem_dsupport_iff x).mpr
 let K:= tsupport h; choose D V O B J T Y using (fun (y:K)=>k.d x y.val (z' ⟨g',y.property⟩))
 have he : K ⊆ ⋃ y:↥(tsupport h), V y := fun y p=> Set.mem_iUnion.mpr ⟨⟨y,p⟩,T ⟨y,p⟩⟩
 obtain ⟨Z,hZ⟩:= h'.elim_finite_subcover V J he; let A:= ⋂ y∈Z,D y; refine ⟨A, ?_, isOpen_biInter_finset (fun i _=>O i), Set.mem_iInter₂.mpr (fun y _=> B y)⟩; intro f' q; rw [←p]; apply van; intro y h; obtain ⟨j,z₀,w⟩:= Set.mem_iUnion₂.mp (hZ h); exact (notMem_dsupport_iff y).mpr ⟨V j,Y j _ (fun x p=> Set.mem_iInter₂.mp (q p) j z₀), J j,w⟩ -- orientation domains.Yes.
#print axioms disperse
end cut
-- Geometry pair orientation
variable (i:Axis)
def PriceX(i:Axis)(t d:ℝ)(T:ℝ): Set (E4× E4):= {x| |time x.1-time x.2| < t∧ t+d<x.2 i-x.1 i ∧ x.2 i<T ∧ x.1 i<T}
lemma awake (p:y-x∈ spacelike): ∃ V:Mink.Lorentz,∃ i: Axis,i≠tt∧time (V.act y)= time (V.act x) ∧ V.act x i≠ V.act y i:=by
 let z:=y-x; have hd: |time z|<‖spatial z‖:=(Mink.lateral z).mp p; let s:=‖spatial z‖; have hp:0<s:=(abs_nonneg _).trans_lt hd; let e:Ray:=⟨s⁻¹ • spatial z,by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]; exact inv_mul_cancel₀ hp.ne'⟩
 let T:=-time z/s; let t:=artanh T; have he: |T|<1:=by unfold T; rw [abs_div,abs_neg,abs_of_pos hp,div_lt_iff₀ hp,one_mul]; exact hd
 have hs: sinh t=T*cosh t:= by apply (div_eq_iff (Real.cosh_pos t).ne').mp; rw [←tanh_eq_sinh_div_cosh]; exact tanh_artanh (abs_lt.mp he)
 let V:= e.boost t; have hV: time (V.act z)=0:=by
    unfold V; rw [Ray.boost_at,Ray.newClock]; have H:e.along z=s:=by unfold Ray.along; change inner ℝ _ (s⁻¹ • spatial z)=_; rw [real_inner_smul_right, real_inner_self_eq_norm_sq, pow_two,←mul_assoc]; rw [show s⁻¹*‖spatial z‖=1 from inv_mul_cancel₀ hp.ne',one_mul]
    rw [H,hs]; unfold T; field_simp; ring -- tune
 have Hw: V.act z ∈ spacelike:= by change m _<0; rw [Lorentz.keeps]; exact p
 have HGH: ∃ i:Axis,i≠ tt∧ V.act z i ≠ 0:=by
    by_contra! h; apply lt_irrefl (0:ℝ); calc
       (0:ℝ)=|time (V.act z)|:=by rw [hV,abs_zero]
       _ < ‖spatial (V.act z)‖:= (Mink.lateral ..).mp Hw
       _ = 0:=by rw [show spatial (V.act z)=0 from PiLp.ext (fun i=> h i.castSucc (Fin.castSucc_ne_last i)),norm_zero]
 obtain ⟨i,h',q⟩:= HGH; unfold z at q hV; rw [map_sub] at hV q; refine ⟨V,i,h',?_,?_⟩; · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hV) -- time alias
 exact fun H=> q (show (V.act y i)-(V.act x i)=0 from sub_eq_zero.mpr H.symm)
lemma PriceOpen(t d T:ℝ): IsOpen (PriceX i t d T):=by
 change IsOpen ({x:E4×E4| |time x.1-time x.2|<t} ∩ ({x:E4×E4| t+d<x.2 i-x.1 i} ∩ ({x:E4×E4| x.2 i<T} ∩{x:E4×E4|x.1 i<T})))
 refine IsOpen.inter (isOpen_lt ?_ ?_) (IsOpen.inter (isOpen_lt ?_ ?_) (IsOpen.inter (isOpen_lt ?_ ?_) (isOpen_lt ?_ ?_))) <;> fun_prop
#print axioms awake
-- rectangular windows after L, or after exchanging x,y with reversed orders. B neighborhoods separately.
structure FieldWindow (A B:Set E4)(P:Lorentz)(i:Axis)(t d T:ℝ):Prop where
 holds (x:E4)(p: x∈A)(y:E4)(q:y∈B): (P.act x,P.act y) ∈ PriceX i t d T
lemma Specialty (P:Lorentz)(h:time (P.act x)=time (P.act y))(u:P.act x i < P.act y i) : ∃ (A B:Set E4)(t d:ℝ≥0)(T:ℝ), IsOpen A∧ IsOpen B ∧ 0<t ∧0<d∧ x∈A∧y∈ B∧ FieldWindow A B P i t d T:=by
 let r:=(P.act y i-P.act x i)/4; have hr:0<r:=by unfold r; positivity
 let f:=r.toNNReal; let T:=P.act y i+1; let S:= PriceX i r r T; have hx:(P.act x,P.act y)∈ S:=⟨by rw [h,sub_self, abs_zero]; exact hr,by unfold r; linarith, by unfold T; linarith, by unfold T; linarith⟩; let Q:=(Prod.map (P.act) (P.act)) ⁻¹' S; obtain ⟨Z,W,a,v,b,w,k⟩:= mem_nhds_prod_iff'.1 (show Q∈ 𝓝 (x,y) from ((PriceOpen i r r T).preimage (Continuous.prodMap P.act.continuous P.act.continuous)).mem_nhds hx); refine ⟨Z,W,f,f,T,a,b, Real.toNNReal_pos.mpr hr, Real.toNNReal_pos.mpr hr,v,w,⟨?_⟩⟩; intro x p y q; unfold f; rw [Real.coe_toNNReal _ hr.le]; exact k (show (x,y)∈ Z ×ˢ W from ⟨p,q⟩)
lemma service (p:y-x∈spacelike): ∃ (A B:Set E4)(P:Lorentz)(i:Axis)(t d:ℝ≥0)(T:ℝ), IsOpen A∧IsOpen B∧ x∈A∧y∈ B∧ i≠tt∧ 0<t∧0<d∧ (FieldWindow A B P i t d T ∨ FieldWindow B A P i t d T):=by
 obtain ⟨P,i,h,q,v⟩:=awake x y p; rcases lt_or_gt_of_ne v with h|h -- shadows
 · obtain ⟨Z,W,t,d,T,Pg,p',h₁,h₂,hx,hy,u⟩:= Specialty x y i P q.symm h; refine ⟨Z,W,P,i,t,d,T,Pg,p',hx,hy,?_,h₁,h₂,Or.inl u⟩; assumption
 obtain ⟨Z,W,t,d,T,Pg,p',h₁,h₂,hx,hy,u⟩:= Specialty y x i P q h; refine ⟨W,Z,P,i,t,d,T,p',Pg,hy,hx,?_,h₁,h₂,Or.inr u⟩; assumption
#print axioms service
end Mint
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
