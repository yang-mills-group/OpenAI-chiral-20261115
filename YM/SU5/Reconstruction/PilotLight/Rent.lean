import YM.SU5.Reconstruction.PilotLight.Token
/-! Receipt at all physical heights, including one common occupancy stencil and
throughout with unbroken gauge--chiral lineage of the actual interpretation. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
local notation "K₀"=> tent Y H
open CF.Pannier.Chancel
open Fock Lat Lifted
variable {J : Calibration} {S : Finset Cover}{x: Dome (tent Y H)} -- tune
variable (s w:ℕ)
local notation "g₁"=> hOne Λ s w
local notation "g₂" n:max=> hAll Λ s w n
local notation "b₁"=> bOne Λ s w
local notation "bP" n:max=> bAll Λ s w n
local notation "K₁"=> ticket Y H G s
local notation "p'"=> stamps Λ s (granite w)
local notation "D₀" n:max=> alcove (g₂ n)
private def zoning (J:Calibration)(S:Finset Cover)(w:ℕ):ℕ→Finset Cover
| 0=> ∅
| n+1=> S ∪ streetBox J (granite w) (zoning J S w n)
local notation "Z" n:max => zoning (tent Y H) S w n
lemma lined_eq (x:Dome J) : (lined J w x).val=Vacancy.chart J (granite w) x.val:=rfl
section geometry
variable (h:PhaseChoice.SupportedPhysically Λ l s S (alcove (hOne Λ s w))) (hw:0<w)
include h hw
lemma stacks_fences (n:ℕ): PhaseChoice.SupportedPhysically Λ l s (Z n) (alcove (g₂ n)):=by
 rw [supported_iff] at h ⊢; induction n with
 | zero=> rintro _ v; obtain ⟨z,x,k⟩:= Set.mem_iUnion₂.mp v; exact ((by simpa [zoning] using x): False).elim
 | succ n ih=>
    rintro p'0 v; obtain ⟨z,x,k⟩:= Set.mem_iUnion₂.mp v; rcases Finset.mem_union.mp x with v|v
    · exact first_in s hw n (h (Set.mem_iUnion₂.mpr ⟨z,v,k⟩))
    have he:= slides_cov Y H s (Z n) (granite w) ((supported_iff ..).2 ih);
    exact second_in s w n ((supported_iff ..).1 he (Set.mem_iUnion₂.mpr ⟨z,v,k⟩))
end geometry
section permits
variable {n L:ℕ}{g m y:Dome J}{a:Fin L → Cover}{b:Bool}{z:SU.Slot}
private lemma gauge_ready (h:witnessGauge J S g): InTest J false S false g.val := by obtain ⟨F,v,h⟩:=h; rw [h]; exact .seed v
private lemma matter_ready (h:witnessLode J z S a m): InTest J false S false m.val := Lode_test h
private lemma line_b (p:InTest J false S false m.val): InTest J false (streetBox J (granite w) S) false (lined J w m).val:= street_narrow _ _ p
private lemma joint_ready (p: Clause J z S a w n b g m): InTest J false (zoning J S w n) false g.val ∧ InTest J false (zoning J S w n) false m.val:=by
 induction p with
 | begin_=> exact ⟨.one,.one⟩
 | later_ _ ih=> exact ⟨(line_b w ih.1).mono Finset.subset_union_right,(line_b w ih.2).mono Finset.subset_union_right⟩
 | here_ v p _ ih=> exact ⟨((gauge_ready v).mono Finset.subset_union_left).mul ((line_b w ih.1).mono Finset.subset_union_right), ((matter_ready p).mono Finset.subset_union_left).mul ((line_b w ih.2).mono Finset.subset_union_right)⟩
private lemma layer_ready (z:InTest J false S false y.val)(n:ℕ): InTest J false (zoning J S w n) false (layers J y w n).val:=by
 induction n with
 | zero=> exact .one
 | succ n ih=> rw [step_layer]; exact (((InTest.one).add z).mono Finset.subset_union_left).mul ((line_b w ih).mono Finset.subset_union_right)
private lemma lantern_ready (z:InTest J false S false y.val)(n:ℕ): InTest J false (zoning J S w n) false (lantern J y w n).val:=by
 change InTest _ _ _ _ ((layers J y w n).val-1); rw [sub_eq_add_neg,← neg_one_smul ℂ (1:Family J)]; exact (layer_ready w z n).add (.smul _ .one)

lemma luminous_silence (h:Silence y.val)(n:ℕ): Silence (lantern J y w n).val:=by
 induction n with
 | zero=> intro m v e; rw [lantern,layer_starts,sub_self]; rfl
 | succ n ih=>
    intro m v e; rw [step_lantern]
    let t:= (lined J w (lantern J y w n)).val; change y.val m v+t m v+y.val m v*t m v=0
    have ht:Silence t:= street_silence _ ih ordinate; rw [h _ _ e,ht _ _ e]; simp
end permits
section earn
variable (hw:0<w)(h:∀ j:Axis, Between (tent Y H) j 0 (ruler Λ.block * w) S)
include hw
lemma permit_layers {q:Bool}(t:x∈insideAt Λ l K q (alcove g₁) s) (n:ℕ): layers (tent Y H) x w n ∈ insideAt Λ l K q (D₀ n) s:=by induction n with|zero=> exact Subalgebra.one_mem _|succ n ih=> exact lineNotes Y H s hw ((insideAt ..).add_mem (Subalgebra.one_mem _) t) ih
lemma permit_lantern {q:Bool}(t:x∈insideAt Λ l K q (alcove g₁) s) (n:ℕ): lantern (tent Y H) x w n ∈ insideAt Λ l K q (D₀ n) s:= Subalgebra.sub_mem _ (permit_layers Y H s w hw t n) (Subalgebra.one_mem _)
lemma rent_origin (p:∀ j, Between (tent Y H) j 0 (ruler Λ.block*w) S): PhaseChoice.SupportedPhysically Λ l s S (alcove g₁):= (supported_iff ..).2 fun _ h i=> (supported_iff ..).1 ((Chambers.strip_seats Y H i s w).2 (p i)) h
variable {y y': Dome (tent Y H)} {n d:ℕ}{z:SU.Slot} {a:Fin d → Cover}{b:Bool}
omit hw
lemma gauge_base (h:witnessGauge (tent Y H) S x): InTest K false S false x.val:= gauge_ready h
lemma lode_base (h:witnessLode (tent Y H) z S a x): InTest K false S false x.val:= matter_ready h
include h hw
lemma clause_permitted (p:Clause (tent Y H) z S a w n b y y') : y∈insideAt Λ l (tent Y H) false (D₀ n) s ∧ y'∈insideAt Λ l (tent Y H) false (D₀ n) s:= by
 obtain ⟨hx,u⟩:= joint_ready w p
 have v:=stacks_fences Y H s w (rent_origin Y H s w hw h) hw n
 exact ⟨(mem_insideAt ..).2 ⟨⟨Z n,hx.widen,v⟩,nofun⟩,(mem_insideAt ..).2 ⟨⟨Z n,u.widen,v⟩,nofun⟩⟩
lemma receiptStencil (p:InTest K false S false x.val)(n:ℕ) (z:SU.Slot){d:ℕ}(a:Fin d → Cover):
    ∃ B, PhaseChoice.SupportedPhysically Λ l s B (D₀ n) ∧ InTest K false B false (lantern K x w n).val ∧
     ∀ (g m:Dome (tent Y H)) (b:Bool), Clause (tent Y H) z S a w n b g m → InTest K false B false g.val ∧ InTest K false B false m.val:= ⟨Z n,stacks_fences Y H s w (rent_origin Y H s w hw h) hw n,lantern_ready w p n,fun g m _ p=>joint_ready w p⟩
end earn
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.receiptStencil
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.luminous_silence
