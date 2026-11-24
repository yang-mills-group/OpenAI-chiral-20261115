import YM.SU5.Selected.Mainland
import YM.SU5.Selected.Standing
import YM.SU5.Selected.CheckpointTemporal
/-! # The proposed DETERMINING physical sector really is full enough for this
Hilbert system. Every positive-time B operator from the larger even system is
the norm limit of positive-time B operators from the physical sublanguage,
in fact with continuous (still joint pair field) marks, AT THAT SUPPORT.
Consequence: physical (pure matter stencil charged but only cov composites)
subset with continuous joint pair dependence produces already dense set (not
just span closure) in elected phase (and can use Strict=false etc with no
repair). Thus this limitation not in effect at the temporal-Reconstruction
level. Not claiming dispersion of states in local-H enough. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 460000
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
open Tapestry (Swatch render texture fabric appear render_fabric Roomy daub)
open Set Theory
section continued
variable (J:Calibration)(S:Finset Cover) {n:Side}
-- use eye_read of ALL coordinates in one period
private lemma replant_cont (m:Side) : Continuous (replant S m):=by
  have he:Continuous (Satin.graft S m):= by
    apply continuous_pi; intro i; unfold Satin.graft; split; exact continuous_apply _; exact continuous_const
  exact (he.comp continuous_fst).prodMk (he.comp continuous_snd)
lemma insistent (p:Hosp S (J.c n))(f:Swatch S)(q:Continuous (appear S J n f))(m): Continuous (render S J f m):=by
  change Continuous (fun x => appear S J m f x)
  simp_rw [Tapestry.appearSpool]; refine continuous_finsetSum _ fun i _=>?_ ; refine (?_ : Continuous fun x=> daub S (f i) (Prod.map (onC (J.c m)) (onC (J.c m)) x)).smul continuous_const
  have h : Continuous (daub S (f i)) := by
    have he:(fun x=> daub S (f i) x)=(Tapestry.eye S J n p i) ∘ (appear S J n f) ∘ (replant S (J.c n)):= funext fun x=> (Tapestry.eye_readCover S J n p f x i).symm
    rw [show daub S (f i)=_ from he]; exact ((LinearMap.continuous_of_finiteDimensional _).comp (q.comp (replant_cont S (J.c n)))) -- tune
  exact h.comp ((on_cont _).prodMap (on_cont _))
end continued
variable (D:Arena Y H G.history.circuit j 0 false)
variable (S:Finset Cover) (s w:ℕ)
local notation "ϕ"=> catalog Y H V G j false D
local notation "B₀" => stationC Y H V G j false D
local notation "Q"=>Ark.Ht Y H G.history.circuit j 0 false D
local notation "R"=>render S K
local notation "TV" s:max w:max => Entry Y H s j false w
local notation "Z" s:max α:max x:max h:max=> boxOp Y H V s G.history G.clipped j false D α x h
local notation "St" s:max α:max x:max h:max=> boxElement Y H V G j false D s α x h
section form
variable (p:Between (tent Y H) j 0 (ruler Λ.block*w) S)(t:0<w)
local notation "B'"=>allBox Y H V G j S s D w p t
lemma boxReynolds (m:Side)(f:Swatch S)(h: Hosp S (tent Y H |>.c m))(a:Continuous (appear S K m f)) : B' f=B' (reynoldsC S K m f):=by
  let Aₛ:= orbitC S K m f
  unfold reynoldsC; refine Eq.trans ?_ (ContinuousLinearMap.integral_comp_comm (𝕜:=ℂ) (E:=Swatch S) (Fₗ:=(Q).Op) (B') (φ:= Aₛ) ((orbitC_cont S K m f h a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))
  have he(x):B' (Aₛ x)=B' f:= (stance_color Y H V G j false D S s w t (toEntry Y H j false S s w p (allHues Y H S f)) (toEntry Y H j false S s w p (allHues Y H S (Aₛ x))) (texture ..) (texture ..) p (Tapestry.decorates K S _ f)).symm
  simp_rw [he]; simp

include p in
lemma renovate (f:TV s w) (e:InTest K true S false f.val.val) :
    ∃ x:ℕ→(TV s w),(∀ i,InTest K true S false (x i).val.val ∧ CovCover (tent Y H) ((x i).val.val) ∧
      ∀ m,Continuous ((x i).val.val m)) ∧ Tendsto (fun i=>St s w (x i) t) atTop (𝓝 (St s w f t)):=by
  let F:= fabric S K e; have he:R F= f.val.val:= render_fabric S K e
  obtain ⟨m,hp⟩:= (separates K S).exists; let v: Hosp S ((K).c m):=⟨hp⟩
  obtain ⟨U,g,k,a⟩:= movie Y H S s F
  let u(i):=reynoldsC S K m (U i)
  let X(i:ℕ):= toEntry Y H j false S s w p (allHues Y H S (u i))
  have hx(i): Z s w (X i) t=B' (U i) := Eq.symm (boxReynolds Y H V G j D S s w p t m (U i) v (g m i))
  have hy(i:ℕ): (X i).val.val= R (u i):= rfl
  refine ⟨X, fun i=> ⟨texture S K (u i), neutralC S K m _ v (g m i), insistent K S v _ (show Continuous (appear S K m (u i)) from ?_)⟩,?_⟩
  · unfold u; rw [reynoldsC_apply S K m (U i) v (g m i)]
    exact CF.Pannier.Chancel.sweet (g m i) -- tune
  let A'(i) :=U i-F
  have Ht:Dues Y H G s (R ∘ A'):=by
    refine Filter.Eventually.of_forall fun r=>?_ ; let m:= i (G.rows r)
    filter_upwards [a m] with x h
    let z:=drawn ((Y.voyage m).CapeT s) x; let u(i):= Tapestry.present Y H s m S (U i) z
    let Z':= Tapestry.present Y H s m S F z
    have he: Tendsto (fun i=>u i-Z') atTop (𝓝 0):= by
      have ht:Tendsto u atTop (𝓝 Z'):= h -- tune
      exact (sub_self Z') ▸ ht.sub (g:= fun _=> Z') tendsto_const_nhds
    change Tendsto (fun i=> Tapestry.present Y H s m S (A' i) z) atTop _
    unfold A'; simp_rw [map_sub]; exact he
  have ht:= responsiveBox Y H V G j S s D w p t A' (‖F‖+1+‖F‖) (fun i=> (norm_sub_le ..).trans (add_le_add_left (k i) _)) Ht
  apply tendsto_subtype_rng.mpr -- notation
  change Tendsto (fun i=>Z s w (X i) t) atTop (𝓝 (Z s w f t))
  simp_rw [hx]; rw [box_chart Y H V G j S s D w p t F he.symm]
  have hh:= ht.add (tendsto_const_nhds (x:=B' F) (f:=atTop)) -- tune
  simp_rw [A',(B').map_sub,sub_add_cancel,zero_add] at hh; exact hh
end form

namespace Acting
variable (T₀:Acting Y H V G j false D)
local notation "N" s:max x:max=> Acting.voice Y H V G j false D T₀ s x
-- form on every operator actor
noncomputable def castRecord : Set T₀.space:={t|∃ (s w:ℕ) (x:Entry Y H s j false w),0<w∧ CovCover (tent Y H) x.val.val∧ (∀m,Continuous (x.val.val m)) ∧ t=N s x.val}
lemma drawnDensity : Dense (castRecord Y H V G j D T₀):=by
  intro x; apply closure_minimal (s:=citizens Y H V G j false D T₀) _ isClosed_closure (T₀.densely Y H V G j false D x)
  intro y p; obtain ⟨s,p⟩:= mem_iUnion.mp p; obtain ⟨a,l⟩:=p -- tune
  obtain ⟨w,⟨u,rfl⟩,e⟩:= ((field_entry Y H j false s a).and (eventually_gt_atTop (0:ℕ))).exists
  obtain ⟨S,h,v⟩:=u.property
  obtain ⟨x,t,c⟩:= renovate Y H V G j D S s w v e u h
  rw [←l]
  refine mem_closure_of_tendsto (f:=fun n=> T₀.showL (St s w (x n) e) T₀.ground) (b:=atTop) ?_ ?_
  · let F (x:B₀) := T₀.showL x T₀.ground; have hv:Continuous F:= Continuous.clm_apply (show Continuous T₀.showL from map_continuous _) continuous_const
    rw [Acting.notes Y H V G j false D T₀ s e u]; exact (hv.tendsto (St s w u e)).comp c
  exact Filter.Eventually.of_forall fun i=>⟨s,w,x i,e,(t i).2.1,(t i).2.2,(T₀.notes Y H V G j false D s e (x i)).symm⟩
end Acting
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.renovate
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Acting.drawnDensity
