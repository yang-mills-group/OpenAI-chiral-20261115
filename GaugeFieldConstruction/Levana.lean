import GaugeFieldConstruction.Adnexa
import YM.SU5.Relativistic.Nashi
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale.Veins
open Function Filter Lattice Laurent Bloch Wilson Precision RG Next.Free Work.F08 Craft Pressure Stationary Tree Reef Hom AnalyticBridge.LocalGaussianLaws
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius
open Exterior Next.Free.Stretch Finset Matrix
variable {L c f:Side}{C:ℝ}
open Crest.Shore CF.Jill CF.Fir MeasureTheory Lat Ember
local notation "I"=>Complex.I
variable {α:Type*}{l:Filter α}{M:α→Side}{F:α→Momentum}(u:Tendsto M l atTop)(h:∀ᶠ i in l, Odd (M i).val){x:Bin}(vF:Tendsto F l (𝓝 (tmap x)))
variable (i j: Cover × PlaqAxes) (r:TypeFace 1)
abbrev minnow (p:Momentum) (L: Side) := ∑ l:Site L,gateW i j p L l r
lemma toto (p:Momentum) (L: Side) : minnow i j r p L=∑' l:Cover,chelate i j r l L p:=by
 rw [tsum_eq_sum (s:=univ.image (@lift L)),sum_image]; · unfold minnow; simp only [chelate,wrap_lift,if_true]
 · exact lift_inj.injOn
 intro b k; unfold chelate; rw [if_neg]; intro l; exact k (mem_image.mpr ⟨_,mem_univ _,l⟩)
abbrev shelved (f:Bin→ℂ) (x:Bin):ℂ:=∑' l:Cover, f (x+stem l)
include u vF h
lemma baitR (g:∀ᶠ i in l,F i∈baseCube)(p:Bound Real.pi x)(b:x≠0):Tendsto (fun k=> minnow i j r (F k) (M k)) l (𝓝 (shelved (WritW i j r) x)):=by
 obtain ⟨D,e,hD⟩:=tipW; simp_rw [toto]; refine tendsto_tsum_of_dominated_convergence (wallet.mul_left D) (sweepsE u h vF i j r p b) ?_
 filter_upwards [g,h] with k a c l; unfold chelate; split
 next hh=> have he:= income_lift (wrap (M k) l); rw [hh] at he; rw [he]; apply hD <;>assumption
 rw [norm_zero]; exact (mul_pos e (income_2 _)).le
omit u vF h
lemma mig (h: Even L.val)(p:Site L) : lift (p+1)= fun i=> chert (p i)+1:=by
 rw [lift_eq_iff]; constructor
 · ext1 i; symm; change (↑(chert (p i)+1:ℤ):Per L)= _; rw [Int.cast_add,chert_cast]; simp
 intro i; have he:= shelf (p i) h; rw [ch_price,payH (N:=L)] at he; let A:=pinch L; have hA:0<A:=pinch_pos _; apply And.intro
 · refine (Int.cast_lt (R:=ℝ)).mp ?_; push_cast; apply lt_of_mul_lt_mul_right ?_ hA.le; dsimp only [A] at *; linarith [he.1]
 refine (Int.cast_le (R:=ℝ)).mp ?_; push_cast; apply le_of_mul_le_mul_right ?_ hA; dsimp only [A] at *; linarith [he.2]
lemma wave_Y (h: Even L.val)(p:Site L)(i:Axis): mon (p+1) i= Rush.mel p i + pinch L :=by
 unfold mon; rw [mig h,Pi.smul_apply,smul_eq_mul]; change _ * (2*(Real.pi:ℂ)*↑(chert (p i)+1:ℤ)) = ↑(principal (p i))+ _; rw [ch_price,payH (N:=L)]; push_cast; field_simp [side_ne L]; ring -- tune
-- cubature utility
lemma aging_p : Tendsto (fun N:Side=> N.val) atTop atTop:= tendsto_atTop.mpr (fun b=> (eventually_ge_atTop (⟨b+1,by omega⟩:Side)).mono (fun x (p:b+1≤x.val)=> Nat.le_of_succ_le p))
lemma ageI : Tendsto pinch atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp aging_p)
lemma driftφ {Λ:ℕ→Side}(g:Tendsto Λ atTop atTop)(V:∀ k,Site (Λ k)){p:Gaia}(v:∀ i,p∈cellH (V i)): Tendsto (fun i=> bark (V i)) atTop (𝓝 p):=by
 rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero (fun _=>norm_nonneg _) (fun i=>proximity _ (v i)) ?_; simpa only [Function.comp_apply,Function.comp_def,mul_zero] using ((ageI.comp g).const_mul 2)
abbrev gridQ (a b:Cover × PlaqAxes)(r:TypeFace 1):ℂ:= (cartWeight:ℂ) * ∫ p:Gaia in boundsEarth, shelved (WritW a b r) (exileE p)
variable {N T:ℕ→Side} (g:Tendsto N atTop atTop)(v:Tendsto T atTop atTop) (w:∀ i, Even (N i).val)(o:∀ i,Odd (T i).val) -- collides v name
include i j r g v w o
lemma price_C : Tendsto (fun (k:ℕ)=> (stageVolume (N k))⁻¹ * ∑ p:Site (N k), minnow i j r (mon p) (T k)) atTop (𝓝 (gridQ i j r)):=by
 let H(k:ℕ)(p:Site (N k)):= minnow i j r (mon (p+1)) (T k)
 obtain ⟨C,p,B⟩:= tipW; obtain ⟨D,h',L⟩:= decay_cost
 suffices W:Tendsto (fun (k:ℕ)=> (stageVolume (N k))⁻¹*∑ p:Site (N k), H k p) atTop (𝓝 (gridQ i j r)) from W.congr (fun k=> congrArg _ (show (∑ p':Site (N k), H k p') = ∑ p':Site (N k), minnow i j r (mon p') (T k) from Equiv.sum_comp (Equiv.addRight (1:Site (N k))) (fun p=> minnow i j r (mon p) (T k)))) -- tune
 refine Papyrus.Franc.Loaves.registry g w _ ?_ (C*D) ?_
 · intro x t y z h; apply baitR v (Eventually.of_forall o) ?_ _ _ _ (Eventually.of_forall (fun i=>mon_mem _ _)) ((pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr (fun i=> abs_le.mpr ⟨(t i).1.le,(t i).2⟩)) (fun V=> y (exileE.injective V))
   refine tendsto_pi_nhds.mpr fun a=>?_ ; have hh:=tendsto_pi_nhds.mp (Papyrus.Franc.Loaves.mill z (driftφ g z h)) a
   refine Tendsto.congr ?_ (show Tendsto (fun k=> Rush.mel (z k) a + pinch (N k)) atTop (𝓝 ((tmap (exileE x)) a)) from by simpa [Function.comp_def,Papyrus.Franc.Loaves.cn] using hh.add ((Complex.continuous_ofReal.tendsto 0).comp (ageI.comp g)))
   intro k; exact (wave_Y (w k) _ a).symm
 intro k x
 change ‖H k x‖≤C*D; unfold H minnow; apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun l: Site (T k)=> C*decay 2 l) (fun i _=> B _ (o k) _ (mon_mem _ _) _ _ _ _)).trans ?_); rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (L _) p.le
omit r
include i j
lemma pier_S : Tendsto (fun (k:ℕ)=> (stageVolume (N k))⁻¹ * ∑ p:Site (N k),∑ l: Site (T k), WaveT (face_K i (N k)) (face_K j (N k)) (T k) (mon p) l) atTop (𝓝 (∑ r:TypeFace 1,gridQ i j r)):=by
 refine (tendsto_finsetSum _ (fun r _=>price_C i j r g v w o)).congr fun k=>?_
 simp_rw [remits]; rw [←mul_sum]; apply congrArg; rw [sum_comm]; exact sum_congr rfl fun p _=> sum_comm
#print axioms pier_S
end YM.CF.Vale.Veins
end
