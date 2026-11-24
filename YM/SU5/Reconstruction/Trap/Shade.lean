import YM.SU5.Reconstruction.Trap.Horizon
import YM.SU5.Reconstruction.Trap.Transits
/-!
# Half spectrum law
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K H D:Hilbert}
namespace Clasp
open Multiplier Chirp
variable (C:Clasp K H D)
noncomputable def range (C:Clasp K H D) := spectrum ℂ C.angle -- abbrev
local notation "I" => spectrum ℂ C.angle
local notation "A"=> C.angle
local notation "Aᵛ"=> (1-C.angle)
noncomputable def realF (z: spectrum ℂ C.angle) : ℝ:= z.val.re
lemma angle_self : IsSelfAdjoint C.angle:= IsSelfAdjoint.of_nonneg C.angle_pos
noncomputable def motion : PVM K (spectrum ℂ C.angle) := Rep.ships (cfcHom C.angle_self.isStarNormal (R:=ℂ))
local notation "P"=> C.motion
local notation "f₀" => C.realF
lemma onShelf (z: I) : (C.realF z:ℂ)=z.val := Eq.symm ((SpectrumRestricts.real_iff.mp C.angle_self.spectrumRestricts) z.val z.property)
lemma price (z:I): C.realF z ∈ Icc (0:ℝ) 1:=by
 have h: C.realF z ∈ spectrum ℝ C.angle:= (spectrum.algebraMap_mem_iff (R:=ℝ) (a:=C.angle) ℂ).1 (show ( (C.realF z:ℝ) :ℂ) ∈ spectrum ℂ A by rw [onShelf]; exact z.property) -- tune
 exact ⟨spectrum_nonneg_of_nonneg C.angle_pos h,((CFC.le_one_iff (R:=ℝ) A (ha:=C.angle_self)).1 C.angle_le) _ h⟩
@[fun_prop] lemma measurable_realF : Measurable (C.realF):= by unfold realF; fun_prop
lemma tagF : Tag C.realF:= ⟨C.measurable_realF,1,zero_le_one,fun x=> by simp only [Real.norm_eq_abs, abs_of_nonneg (price C x).1]; exact (price C x).2⟩
lemma angle_reads : Registers C.motion (fun x=>(C.realF x:ℂ)) C.angle := by
 constructor
 · refine ⟨by fun_prop,1,zero_le_one, fun x=>?_⟩; simp [Real.norm_eq_abs,abs_of_nonneg (price C x).1,(price C x).2]
 let h:= C.angle_self.isStarNormal; let V:= (ContinuousMap.id ℂ).restrict I
 intro x; simp_rw [onShelf]; change _=∫ p, (V p:ℂ)∂(Rep.ships (cfcHom h)).diagonal x; change _= ∫ p, (V p:ℂ)∂Rep.sees _ _
 rw [Rep.pairings]; rw [cfcHom_id]; -- eta V
-- Endpoint states zero for angle
variable {P₀:K.Op} -- useful positive
lemma inOpen (v:K): ∀ᵐ x ∂C.motion.diagonal v, C.realF x∈ Ioo (0:ℝ) 1:= by
 let a (t:ℝ):={x:I| f₀ x=t}; have h (t) : MeasurableSet (a t):= C.measurable_realF (show MeasurableSet ({t} : Set ℝ) from measurableSet_singleton _)
 have hp(w : I→ℂ)(A':K.Op) (t:ℝ)(p: Registers C.motion w A') (q:∀ x ∈ a t, w x=0)(e:Injective A'): (P).diagonal v (a t)=0:= by
   have k : (P).region (a t)*A'=0:=by
     have e:= p.mask (h t) (p.comm (h t)); apply Registers.single e; rw [show (a t).indicator w=0 from ?_]; exact Registers.none P
     funext x; by_cases v:x∈ a t
     · rw [indicator_of_mem v]; exact q _ v
     simp only [indicator_of_notMem v]; rfl
   apply ((P).null_pair (h t) v).2; apply e; rw [map_zero]
   exact DFunLike.congr_fun (Eq.trans (p.comm (h t)|>.eq) k) v
 have hb : Injective A := (C.l.adjoint_comp_self_injective_iff).mpr C.j
 have he : Injective ((1 : K.Op)-C.angle : K.Op) := (show C.r.adjoint.comp C.r= _ from C.complement) ▸ (C.r.adjoint_comp_self_injective_iff.mpr C.k)
 have hv:∀ᵐ x ∂(P).diagonal v, x∉a 0:= by apply ae_iff.mpr; simpa using hp (fun x=>(f₀ x:ℂ)) A 0 C.angle_reads (fun x h=>by change f₀ x=0 at h; simp [h]) hb -- tune double negative
 have h1:∀ᵐ x ∂(P).diagonal v,x∉ a 1:= by apply ae_iff.mpr; simpa using hp (1-(fun x=>(f₀ x:ℂ))) Aᵛ 1 ((Registers.one P).sub C.angle_reads) (fun x h=>by change f₀ x=1 at h; simp [h]) he
 filter_upwards [hv,h1] with x u v; exact ⟨lt_of_le_of_ne (price C x).1 (Ne.symm u),lt_of_le_of_ne (price C x).2 v⟩
-- modular
noncomputable def river (u:ℝ)(x:ℝ): ℂ := sing u ((1-x)/x)
lemma river_price (u:ℝ):Tag (river u):= ⟨by unfold river; fun_prop,1,zero_le_one,fun x=> (nice ..).le⟩
noncomputable def Cabin (u:ℝ):K.Op:= order C.motion (river u ∘ C.realF)
lemma Cabin_reads (u:ℝ):Registers C.motion (river u ∘ C.realF) (C.Cabin u):= order_reads _ ((river_price u).port C.realF C.measurable_realF)
lemma Cabin_time (u v:ℝ):C.Cabin u*C.Cabin v=C.Cabin (u+v):= by
 apply ((Cabin_reads C u).times (Cabin_reads C v)).single
 rw [show (river u ∘ C.realF)*(river v ∘ C.realF)=_ from funext (fun x:I=> show _=(river (u+v) ∘ C.realF) x from Chirp.team u _ v)]; exact Cabin_reads C (u+v)
@[simp] lemma Cabin_zero : C.Cabin 0=1:= by
 apply (Cabin_reads C 0).single
 rw [show river 0 ∘ C.realF=1 from funext fun _=> Chirp.origin _]; exact Registers.one P
lemma Cabin_cross (u:ℝ): star (C.Cabin u)=C.Cabin (-u):= Registers.single ((C.Cabin_reads u).adjoint) (by
 rw [show star (river u ∘ C.realF)= (river (-u) ∘ C.realF) from funext fun _=> (Chirp.neg_time ..).symm]; exact Cabin_reads ..)
lemma Cabin_pays (u:ℝ):Pays (C.Cabin u):=⟨by rw [Cabin_cross,Cabin_time,neg_add_cancel,Cabin_zero],by rw [Cabin_cross,Cabin_time,add_neg_cancel,Cabin_zero]⟩
lemma cabin_strong (x:K):Continuous (fun t=> C.Cabin t x) := by
 apply continuous_iff_continuousAt.mpr; intro z
 exact Registers.tends (𝓝 z) (fun t=> river t ∘ C.realF) _ (C.Cabin_reads z) (fun t=> C.Cabin_reads t) x 1 (Eventually.of_forall fun t=> Eventually.of_forall fun x=> (show _ from (Chirp.nice ..).le)) (Eventually.of_forall fun x=> (show Continuous (fun t=> sing t ((1-f₀ x)/f₀ x)) from by unfold sing; fun_prop).tendsto z)
lemma oneCabin {T:K.Op}(h:Commute T C.angle)(u:ℝ): Commute T (C.Cabin u):= compare_at _ _ T _ _ C.measurable_realF C.measurable_realF C.tagF C.tagF C.angle_reads C.angle_reads h.eq _ (river_price u)
end Clasp
end YM.CrossedFrame
