import YM.SU5.Reconstruction.Cross.Boundaries
import YM.SU5.Reconstruction.Cross.Train
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
/- Sufficient chart criterion: slots on common fine enough mesh n, item supports in real
sets lying in consecutive window interiors. Works at the very hierarchy. -/
-- Work on future extension after contour flows: prove here geometry realization independently of response.
open _root_.YM.SelectionAnalysis Vacancy.Average
section round
variable (M:Mesh)
noncomputable def meshPy (y:ℝ)(n:ℕ):ℤ:=⌊ y/(mill M n :ℝ)⌋
lemma round_down (y:ℝ) (n:ℕ) :
    bell M n (meshPy M y n)≤y ∧ y<bell M n (meshPy M y n+1):=by
 let z :ℝ := mill M n; have h:0<z:=mill_pos M n; constructor
 · exact (le_div_iff₀ h).mp (Int.floor_le _)
 unfold meshPy bell; push_cast; exact (div_lt_iff₀ h).mp (Int.lt_floor_add_one _)
lemma round_shrink (y:ℝ) : Tendsto (fun n=> bell M n (meshPy M y n)) atTop (𝓝 y):=by
  have hx:Tendsto (fun i:ℕ=> (mill M i:ℝ)) atTop (𝓝 0) := NNReal.tendsto_coe.mpr (vanishes M)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g:=fun n=> y-((mill M n):ℝ)) (h:=fun _=>y) (by simpa using tendsto_const_nhds.sub hx) tendsto_const_nhds (fun n=>?_) (fun n=>(round_down M y n).1)
  have h:=(round_down M y n).2; rw [bell_add] at h; have he: bell M n 1=(mill M n:ℝ):=by simp [bell]
  rw [he] at h; exact sub_le_iff_le_add.mpr h.le
lemma eventual_lt {x y:ℝ} (p:x<y): ∀ᶠ n in atTop, meshPy M x n< meshPy M y n  := by
  filter_upwards [(round_shrink M x).eventually_lt (round_shrink M y) p] with n h
  exact lt_of_not_ge (fun v=> h.not_ge ((bell_le M _ _ _).2 v))
end round

variable {f:Marks (tent Y H) false} {S:Finset Cover}
local notation "U" g:max t:max=> upGrade Y H s Q false g t
local notation "Us" t:max=> volumeAround Λ l (t-s) S
local notation "G" v:max=> silhouette Λ l v
lemma nearby_power (p : InTest K true S false f.val) (t : ℕ)(h:s≤t) :
   InTest (tent Y H) true (volumeAround Λ l (t-s) S) false (upGrade Y H s Q false f t).val ∧
   silhouette Λ l t (volumeAround Λ l (t-s) S) ⊆ silhouette Λ l s S:=by
  refine ⟨(proceeds Y H Q.circuit s _ p).1,?_⟩
  have e:= sheltered_still (Λ:=Λ) (l:=l) (S:=S) (s:=s) (t-s)
  rwa [show s+(t-s)=t by omega] at e
lemma of_between {a b:ℤ}(p : InTest K true S false f.val) (d: Between (tent Y H) j (ruler Λ.block*a) (ruler Λ.block*b) S) {w:ℕ} (he:b=a+(w:ℤ)) :
    ∃ x : Entry Y H s j false w,
      x.val.val = SlabMark.relocate (tent Y H) j (-a) f.val ∧
      -- stronger: lies in given compact support after relocating even within buffer; use separately
      f.val= SlabMark.relocate (tent Y H) j a x.val.val := by
 let F:= SlabMark.relocate (tent Y H) j (-a) f.val; let V₁:= plow (tent Y H) j (-a) S
 have ht: InTest K true V₁ false F:= flow_port K j _ p
 have hU: Between K j 0 (ruler Λ.block*w) V₁:=by
    have hX:= d.relocate K j (-a)
    rw [show (K).B= Λ.block from rfl,show ruler _* (-a)+ruler Λ.block*a=0 by ring,show ruler Λ.block * (-a)+ruler Λ.block*b=ruler Λ.block*w by rw [he]; ring] at hX; exact hX
 let x:Tower.Field Y H s j 0 false:=⟨F,(purpose_ok ..).2 ⟨⟨V₁,ht,by intro y v; rw [area0]; exact (hU y v).1⟩,nofun⟩⟩
 exact ⟨⟨x,V₁,ht,hU⟩,rfl,(by change f.val = SlabMark.relocate _ _ a F; unfold F; rw [relocate_sums K j _ _ (marksSpec false f).1, add_neg_cancel, relocate_zero K j (aux_test p)])⟩
-- advice re structure: coordinates real *abs* preferred, marks before shifts live in G binder.
structure Timetable (σ : Set RSpace) (v : Axis → ℝ) where
  origin : ℝ
  dest : ℝ
  -- strict relative mark time gate (not on order; afterward check)
  tall : origin < dest -- needed even for empty
  safe : ∀ u∈ σ,v j+u j∈ Set.Ioo origin dest
section
variable (σ : Set RSpace) {x y : ℝ}
namespace Timetable
-- Timetable doesn't mention s, etc; assertions try convert.
lemma refine_hints {σ : Set RSpace} {v : RSpace} {j : Axis} (T₀:Timetable j σ v)(p:IsCompact σ) : ∃ (a b:ℝ), a<b ∧ T₀.origin<a ∧ b<T₀.dest ∧ ∀ u∈σ,v j+u j∈ Set.Icc a b:=by
 let cx(u:RSpace):= v j+u j
 rcases σ.eq_empty_or_nonempty with h|h
 · let w:=(T₀.origin+T₀.dest)/2; refine ⟨(T₀.origin+w)/2,(T₀.dest+w)/2,?_,?_,?_,fun _ v=>?_⟩
   any_goals unfold w; linarith [T₀.tall]; done
   exact False.elim ((Set.notMem_empty _) (h ▸ v))
 have h' : Continuous cx := continuous_const.add (continuous_apply j)
 obtain ⟨a,a',w⟩:= p.exists_isMinOn h (show ContinuousOn cx σ from h'.continuousOn)
 obtain ⟨b,b',d⟩:= p.exists_isMaxOn h (show ContinuousOn cx σ from h'.continuousOn)
 have hc:T₀.origin < cx a := (T₀.safe a a').1; have hk: cx b < T₀.dest:= (T₀.safe b b').2; have hx : cx a≤ cx b := w b'
 refine ⟨(T₀.origin + cx a)/2,(T₀.dest + cx b)/2,by linarith only [hc,hk,hx],by linarith only [hc],by linarith only [hk], fun i h=> ?_⟩
 have hh:cx a≤ cx i := w h; have hu: cx i≤ cx b := d h; change (T₀.origin+ cx a)/2 ≤ cx i ∧ cx i ≤ _; constructor<;> linarith
end Timetable
end

local notation "L" x:max t:max=> meshPy Μ x t
lemma ticket_has {S:Finset Cover} (p:InTest (tent Y H) true S false f.val) {v : RSpace} (T₀:Timetable j (silhouette Λ l s S) v) :
    ∀ᶠ t in atTop,∃ g : Gate Y H t j (upGrade Y H s Q false f t), g.within_ v ∧ g.start=meshPy Μ T₀.origin t ∧ g.start+(g.full:ℤ)= meshPy Μ T₀.dest t ∧
      -- identify that silhouette region of refined MARK still fits in this Slot (stencil holds through varying t)
      ∀ x∈ silhouette Λ l s S,x j∈ Icc (bell Μ t g.base) (bell Μ t (g.base+g.width)):=by
 obtain ⟨a,b,h,X,U₁,Lp⟩:=T₀.refine_hints (silhouette_compact ..)
 -- choose slight further slack to reserve profiles w real bounds strict
 let C':=(T₀.origin+a)/2 - v j; let D':=(T₀.dest+b)/2-v j
 have he:C'<D':=by unfold C' D'; linarith
 have ha : T₀.origin < C'+v j:=by unfold C'; linarith
 have hb : D'+v j < T₀.dest:=by unfold D'; linarith
 have hr : b < D'+v j:=by unfold D'; linarith
 have ht(w:ℝ): Tendsto (fun t=> v j+bell Μ t (L w t)) atTop (𝓝 (v j + w)):= tendsto_const_nhds.add (round_shrink Μ w)
 have hL := Filter.Tendsto.eventually_lt (round_shrink Μ T₀.origin) (ht C') (by linarith : T₀.origin < v j+C'); -- lemma name check
 have hR := Tendsto.eventually_lt (ht D') (round_shrink Μ T₀.dest) (by linarith : v j+D'<T₀.dest)
 filter_upwards [eventual_lt Μ he,hL,hR, (ht D').eventually (lt_mem_nhds (by linarith : b<v j+D')), eventually_ge_atTop s] with t t1 tL tR t0 q
 let a₀:=meshPy Μ C' t; let b₀:= meshPy Μ D' t; let m:=meshPy Μ T₀.origin t; let n:=meshPy Μ T₀.dest t
 let M:= bell Μ t; let π :ℝ:= mill Μ t; have hπ:0<π:=mill_pos Μ t
 change a₀<b₀ at t1; change M m<v j+M a₀ at tL; change v j+M b₀ < M n at tR; change b< v j+M b₀ at t0
 let w:=(b₀-a₀).toNat; have hw:(w:ℤ)=b₀-a₀:= Int.toNat_of_nonneg (by omega)
 have hx: b₀=a₀+w:=by omega
 have hU(x:RSpace)(p:x∈silhouette Λ l s S):x j∈Set.Icc (M a₀) (M b₀):=by
    have p' := Lp x p; obtain ⟨u₀,v'⟩:= p'; have h':M a₀≤ C':=(round_down Μ C' t).1; change M a₀≤ x j ∧ x j ≤ M b₀
    unfold C' at h'; constructor <;> linarith
 obtain ⟨u,z⟩:=nearby_power Y H Q s p t q
 obtain ⟨y,g,g'⟩:=of_between Y H t j (f:=U f t) u ((stamp_span Y H j (volumeAround Λ l (t-s) S)).mp (fun _ v=> hU _ (z v))) hx
 let l':=(n-m-(b₀-a₀)).toNat; have hl:0<n-m-(b₀-a₀):=by
    have he : m+(b₀-a₀)<n:=lt_of_not_ge (fun (p₁:n ≤ _) => by
      have he: M n ≤ M (m+(b₀-a₀)):= (bell_le Μ _ _ _).2 p₁
      unfold M at *; rw [bell_add,bell_sub] at he; linarith)
    omega
 have hi:(l':ℤ)=n-m-(b₀-a₀):=Int.toNat_of_nonneg hl.le
 let g:Gate Y H t j (U f t):= ⟨w,by omega,y,a₀,g',m,l'⟩
 refine ⟨g,?_,rfl,?_,fun x u=>?_⟩
 · change 0<v j+M a₀-M m ∧ 0 < M l' - (v j+ M a₀-M m); constructor
   · exact sub_pos.mpr tL
   unfold M at *
   rw [hi, bell_sub Μ t _ (b₀-a₀),bell_sub,bell_sub]; linarith
 · change m+((w+l':ℕ):ℤ)=n; omega
 change x j∈Set.Icc (M a₀) (M (a₀ + (w:ℤ)))
 rw [←hx]; exact hU x u
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.ticket_has
